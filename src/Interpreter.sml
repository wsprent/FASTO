(* An interpreter for Fasto. *)

structure Interpreter = struct

(*

An interpreter executes a (Fasto) program by inspecting the abstract syntax
tree of the program, and doing what needs to be done in another programming
language (SML).

As mentioned in Fasto.sml, some Fasto expressions are implicitly typed. The
interpreter infers the missing types, and checks the types of the operands
before performing any Fasto operation.

Any valid Fasto program must contain a "main" function, which is the entry
point of the program. The return value of this function is the result of the
Fasto program.

The main function of interest in this module is:

  val evalProg : Fasto.KnownTypes.Prog -> Fasto.Value

*)

open Fasto

(* An exception for reporting run-time errors. *)
exception Error of string * pos

open Fasto.UnknownTypes

type e = Exp
type v = Value
type f = FunDec

(* Build a function table, which associates a function names with function
   declarations. *)
fun buildFtab [] =
    let val p  = (0, 0)
        val ch = #"a"
    in SymTab.fromList [ ("chr", FunDec ("chr", Char, [Param ("n", Int)],
                                         Constant (CharVal ch, p), p))
                       , ("ord", FunDec ("ord", Int, [Param ("c", Char)],
                                         Constant (IntVal 1, p), p)) ]
    end
  | buildFtab ( fdcl::fs ) =
    (* Bind the user-defined functions, in reverse order. *)
    let
      val fid   = getFunName fdcl
      val pos   = getFunPos fdcl
      val ftab  = buildFtab fs
    in
      case SymTab.lookup fid ftab of
        NONE => SymTab.bind fid fdcl ftab
      | SOME ofdecl =>
          (* Report the first occurrence of the name. *)
          raise Error ("Already defined function: " ^ fid, getFunPos ofdecl)
    end

(* Check whether a value matches a type. *)
fun typeMatch ( Int,  IntVal _ ) = true
  | typeMatch ( Bool, BoolVal _) = true
  | typeMatch ( Char, CharVal _) = true
  | typeMatch ( Array t, ArrayVal (vals, tp) ) =
    (t = tp) andalso List.all (fn value => typeMatch (t, value)) vals
  | typeMatch (_, _) = false

fun invalidOperand tp e pos =
    raise Error("expected " ^ (ppType tp) ^ ", got " ^ (ppType (valueType e)) ^
      " (" ^ (ppVal 0 e) ^ ") instead", pos)

fun invalidOperands tps e0 e1 pos =
    let
      val types = map (fn (tp0, tp1) => (ppType tp0) ^ " and " ^ (ppType tp1)) tps
    in
      raise Error(
        "expected " ^ (String.concatWith ", or " types) ^ ", got " ^
        (ppType (valueType e0)) ^ " (" ^ (ppVal 0 e0) ^ ") and " ^
        (ppType (valueType e1)) ^ " (" ^ (ppVal 0 e1) ^ ") instead", pos)
    end
(* Evaluating
    1. binary operators +, -, etc.
    3. relational operator <,> *)

fun evalBinopNum ( bop, IntVal n1, IntVal n2, pos ) =
    IntVal (bop(n1,n2))
  | evalBinopNum ( bop, e1, e2, pos ) =
    invalidOperands [(Int, Int)] e1 e2 pos

fun evalEq ( IntVal n1,     IntVal n2,     pos ) =
    BoolVal (n1=n2)
  | evalEq ( BoolVal b1,     BoolVal b2,     pos ) =
    BoolVal (b1=b2)
  | evalEq ( CharVal c1, CharVal c2, pos ) =
    BoolVal (c1=c2)
  | evalEq ( e1, e2, pos ) =
    invalidOperands [(Int, Int), (Bool, Bool), (Char, Char)] e1 e2 pos

fun evalRelop ( bop, IntVal n1,     IntVal n2,     pos ) =
    BoolVal (bop(n1,n2))
  | evalRelop ( bop, CharVal n1, CharVal n2, pos ) =
    BoolVal (bop(Char.ord(n1),Char.ord(n2)))
  | evalRelop ( bop, BoolVal n1,     BoolVal n2,     pos ) =
        let val i1 = if n1 then 1 else 0
            val i2 = if n2 then 1 else 0
        in  BoolVal (bop(i1,i2))
        end
  | evalRelop ( bop, e1, e2, pos ) =
    invalidOperands [(Int, Int), (Bool, Bool), (Char, Char)] e1 e2 pos

(* Index into an array. Check that the index is not out of bounds. *)
fun applyIndexing( ArrayVal(lst, tp), IntVal ind, pos ) =
        let val len = List.length(lst)
        in if( len > ind andalso ind >= 0 )
             then List.nth(lst,ind)
             else raise Error("Array index out of bounds! Array length: "^
                              Int.toString(len)^" Index: "^Int.toString(ind), pos )
        end
  | applyIndexing( arr, IntVal ind, pos ) =
    raise Error("Indexing Error: " ^ (ppVal 0 arr) ^ " is not an array", pos)
  | applyIndexing( arr, e, pos ) = (* Order of clauses is important here. *)
    invalidOperand Int e pos

(* Bind the formal parameters of a function declaration to actual parameters in
   a new vtab. *)
fun bindParams ([], [], fid, pd, pc) = SymTab.empty()
  | bindParams ([], a,  fid, pd, pc) =
        raise Error("Number of formal and actual params do not match! In call to "^fid, pc)
  | bindParams (b,  [], fid, pd, pc) =
        raise Error("Number of formal and actual params do not match! In call to "^fid, pc)
  | bindParams ( Param (faid, fatp)::fargs, a::aargs, fid, pd, pc ) =
        let val vtab   = bindParams( fargs, aargs, fid, pd, pc )
        in  if( typeMatch(fatp, a) )
              then case SymTab.lookup faid vtab of
                     NONE   => SymTab.bind faid a vtab
                   | SOME m => raise Error("Formal argument is already in symbol table!"^
                                           " In function: "^fid^" formal argument: "^faid, pd)
              else raise Error("Actual and formal argument type do not match!"^
                               " In function: "^fid^" formal argument: "^faid^
                               " of type: "^ppType(fatp)^
                               " does not matches actual argument: "^
                               ppVal 0 a, pc)
        end


(* Interpreter for Fasto expressions:
    1. vtab holds bindings between variable names and
       their interpreted value (Fasto.Value).
    2. ftab holds bindings between function names and
       function declarations (Fasto.FunDec).
    3. Returns the interpreted value. *)
fun evalExp ( Constant (v,_), vtab, ftab ) = v
  | evalExp ( ArrayLit (l, t, pos), vtab, ftab ) =
        let val els = (map (fn x => evalExp(x, vtab, ftab)) l)
            val elt = case els of []   => Int (* Arbitrary *)
                                | v::_ => valueType v
        in ArrayVal (els, elt)
        end

  | evalExp ( StringLit(s, pos), vtab, ftab ) =
        let val str  = String.explode s
            val exps = map (fn c => CharVal c) str
        in ArrayVal (exps, Char)
        end

  | evalExp ( Var(id, pos), vtab, ftab ) =
        let val res = SymTab.lookup id vtab
        in case res of
             NONE   => raise Error("Symbol "^id^" is not in symbol table!\n", pos)
           | SOME m => m
        end

  | evalExp ( Plus(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinopNum(op +, res1, res2, pos)
        end

  | evalExp ( Minus(e1, e2, pos), vtab, ftab ) =
        let val res1   = evalExp(e1, vtab, ftab)
            val res2   = evalExp(e2, vtab, ftab)
        in  evalBinopNum(op -, res1, res2, pos)
        end

  | evalExp ( Equal(e1, e2, pos), vtab, ftab ) =
        let val r1 = evalExp(e1, vtab, ftab)
            val r2 = evalExp(e2, vtab, ftab)
        in evalEq(r1, r2, pos)
        end

  | evalExp ( Less(e1, e2, pos), vtab, ftab ) =
        let val r1 = evalExp(e1, vtab, ftab)
            val r2 = evalExp(e2, vtab, ftab)
        in  evalRelop(op <, r1, r2, pos)   (* > *)
        end

  | evalExp ( If(e1, e2, e3, pos), vtab, ftab ) =
        let val cond = evalExp(e1, vtab, ftab)
        in case cond of
              BoolVal true  => evalExp(e2, vtab, ftab)
           |  BoolVal false => evalExp(e3, vtab, ftab)
           |  other         => raise Error("If condition is not a logical value!", pos)
        end

  | evalExp ( Apply(fid, args, pos), vtab, ftab ) =
        let val evargs = map (fn e => evalExp(e, vtab, ftab)) args
        in case SymTab.lookup fid ftab of
               SOME f => callFun(f, evargs, ftab, pos)
             | NONE   => raise Error("Function "^fid^" is not in symbol table! Called at: ", pos)
        end

  | evalExp ( Let(Dec(id,e,p), exp, pos), vtab, ftab ) =
        let val res   = evalExp(e, vtab, ftab)
            val nvtab = SymTab.bind id res vtab
        in  evalExp(exp, nvtab, ftab)
        end

  | evalExp ( Index(id, e, tp, pos), vtab, ftab ) =
        let val ind = evalExp(e, vtab, ftab)
            val arr = SymTab.lookup id vtab
        in case arr of
             NONE   => raise Error("Array id "^id^" is not in SymTab!", pos)
           | SOME m => applyIndexing(m, ind, pos)
        end

  | evalExp ( Iota (e, pos), vtab, ftab ) =
        let val sz = evalExp(e, vtab, ftab)
        in case sz of
             IntVal size =>
                if size > 0
                then ArrayVal(List.tabulate(size, (fn x => IntVal x)),
                              Int)
                else raise Error("Error: In iota call, size is less or equal to 0: "
                                 ^ Int.toString(size), pos)
           | _ => raise Error("Iota Arg Is Not A Number: "^ppVal 0 sz, pos)
        end

  | evalExp ( Replicate (n, e, tp, pos), vtab, ftab ) =
        let val sz  = evalExp(n, vtab, ftab)
            val el  = evalExp(e, vtab, ftab)
        in case sz of
             IntVal size =>
               let val els =
                       if size > 0
                       then List.tabulate(size, (fn x => el))
                       else raise Error("Error: In call to replicate, size is less or equal to 0: "
                                        ^Int.toString(size), pos)
               in ArrayVal (els, valueType el)
               end
           | _ => raise Error("Replicate First Arg (Array Size) "^
                              "Was Not Evaluated To A Number: "^ppVal 0 sz, pos)
        end

  | evalExp ( Map (farg, arrexp, _, _, pos), vtab, ftab ) =
        let val arr  = evalExp(arrexp, vtab, ftab)
            val (call_farg, farg_ret_type) = evalFunArg (farg, vtab, ftab, pos)
        in case arr of
               ArrayVal (lst,tp1) =>
               let val mlst = map (fn x => call_farg([x])) lst
               in  ArrayVal (mlst, farg_ret_type)
               end
             | otherwise => raise Error("Second Argument of Map Is Not An Array: "
                                        ^ppVal 0 arr, pos)
        end

  | evalExp ( Reduce (farg, ne, arrexp, tp, pos), vtab, ftab ) =
        let val (call_farg, farg_ret_type) = evalFunArg (farg, vtab, ftab, pos)
            val arr  = evalExp(arrexp, vtab, ftab)
            val nel  = evalExp(ne, vtab, ftab)
        in case arr of
               ArrayVal (lst,tp1) =>
               foldl (fn (x,y) => call_farg([y,x])) nel lst
             | otherwise => raise Error("Third Argument of Reduce Is Not An Array: "^
                                        ppVal 0 arr, pos)
        end

  | evalExp ( Filter (farg, arr_exp, elem_type, pos), vtab, ftab ) =
    let val (call_farg, farg_ret_type) = evalFunArg (farg, vtab, ftab, pos)
        fun pred exp =
            case call_farg [exp] of
                BoolVal p => p
              | ret_val => raise Error ("Filter: Predicate returned " ^
                             ppVal 0 ret_val ^ " instead of a bool", pos)
    in case evalExp (arr_exp, vtab, ftab) of
           ArrayVal (elems, ty) => ArrayVal (List.filter pred elems, ty)
         | arr_val => raise Error("Second Argument of Filter Is Not An Array: "^
                                  ppVal 0 arr_val, pos)
    end

  | evalExp ( Scan (farg, acc_exp, arr_exp, elem_type, pos), vtab, ftab ) =
    let val (call_farg, farg_ret_type) = evalFunArg (farg, vtab, ftab, pos)
        fun scan acc [] = [acc]
          | scan acc (elem::elems) = acc :: scan (call_farg [acc, elem]) elems
        val acc_val = evalExp (acc_exp, vtab, ftab)
    in case evalExp (arr_exp, vtab, ftab) of
           ArrayVal (elems, ty) => ArrayVal (scan acc_val elems, farg_ret_type)
         | arr_val => raise Error("Third Argument of Scan Is Not An Array: "^
                                  ppVal 0 arr_val, pos)
    end

  | evalExp ( ArrCompr (e, bindings, conds, e_tp, arr_tps, pos ), vtab, ftab ) =
    let
      fun evalArray (exp, vtab, ftab) =
        case evalExp (exp, vtab, ftab) of
          ArrayVal (v,_) => v
        | _ => raise Error(
              "One of the binding expressions is not an array.", pos)
      val bindings' = map (fn (name, exp) => (name, evalArray (exp, vtab, ftab))) bindings

      fun evalBool (exp, vtab, ftab) =
        case evalExp (exp, vtab, ftab) of
          BoolVal v => v
        | _ => raise Error(
              "One of the conditions is not a bool.", pos)

      fun evalConds ([], _) = true
        | evalConds (c::cs, vtab) =
          evalBool (c, vtab, ftab) andalso evalConds (cs, vtab)

      fun evalWithBinding (name, v, vtab) =
          let
            val vtab' = SymTab.bind name v vtab
          in
            if evalConds (conds, vtab')
            then SOME (evalExp (e, vtab', ftab))
            else NONE
          end

      fun optionListToList [] = []
        | optionListToList (NONE::os) = optionListToList os
        | optionListToList ((SOME v)::os) = v :: (optionListToList os)

      fun checkArrayType ([], tp) = tp
        | checkArrayType (v::vs, tp) =
          if (valueType v) = tp
          then checkArrayType (vs, tp)
          else raise Error("One of the value does not match in type.", pos)

      fun getArrayType [] = valueType (evalExp (e, vtab, ftab))
        | getArrayType (v::vs) = checkArrayType (vs, valueType v)

      fun evalBindings ([], vtab) =
          (* The parser shouldn't allow an array comprehension with no
           * bindings *)
          raise Error("impossible (array comprehension with no bindings)", pos)
        | evalBindings ([(name, vs)], vtab) =
          let
            val array = optionListToList
              (map (fn v => evalWithBinding (name, v, vtab)) vs)
          in
            ArrayVal (array, getArrayType array)
          end
        | evalBindings (((name, vs)::bs), vtab) =
          let
            val array = map (fn v => evalBindings (bs, SymTab.bind name v vtab)) vs
          in
            ArrayVal (array, getArrayType array)
          end
    in
      evalBindings (bindings', vtab)
    end

  | evalExp ( Read (t,p), vtab, ftab ) =
        let val str =
                case TextIO.inputLine(TextIO.stdIn) of
                    SOME line => line
                  | NONE      =>
                    raise Error("End of line when reading input", p)
        in case t of
             Int => let val v = Int.fromString(str)
                    in case v of
                           SOME n    => IntVal n
                         | otherwise => raise Error("read(int) Failed! ", p)
                    end
           | Bool => let val v = Int.fromString(str) (* Bool.fromString(str) *)
                     in case v of
                            SOME b    => if( b=0 ) then BoolVal false else BoolVal true
                          | otherwise => raise Error("read(bool) Failed; 0==false, 1==true! ", p)
                     end
           | Char => let val v = Char.fromCString(str)
                     in case v of
                            SOME c    => CharVal c
                          | otherwise => raise Error("read(char) Failed!  ", p)
                     end
           | otherwise => raise Error("Read operation is valid only on basic types ", p)
        end

  | evalExp ( Write(exp,t,p), vtab, ftab ) =
        let val v  = evalExp(exp, vtab, ftab)
            val () =
            case v of
              IntVal n => print( (Int.toString n) ^ " " )
            | BoolVal b => let val res = if(b) then "True " else "False " in print( res ) end
            | CharVal c => print( (Char.toCString c)^" " )
            | ArrayVal (a, Char) =>
              let fun mapfun e =
                      case e of
                          CharVal c => c
                        | otherwise => raise Error("Write argument " ^
                                                   ppVal 0 v ^
                                                   " should have been evaluated to string", p)
              in print( String.implode (map mapfun a) )
              end
            | otherwise => raise Error("Write can be called only on basic and array(char) types ", p)
        in v
        end

  (* TODO TASK 1: add cases for Times, Divide, Negate, Not, And, Or.  Look at
  how Plus and Minus are implemented for inspiration.
   *)

(* Interpreter for Fasto function calls:
    1. f is the function declaration.
    2. args is a list of (already interpreted) arguments.
    3. ftab is the function symbol table (containing f itself).
    4. pcall is the position of the function call. *)
and callFun (f, args, ftab, pcall) =
    callFunWithVtable(f, args, SymTab.empty(), ftab, pcall)

and callFunWithVtable (FunDec (fid, rtp, fargs, body, pdcl), aargs, vtab, ftab, pcall) =
    case fid of
      (* treat the special functions *)
        "ord" => (case aargs of
                      [CharVal c] => IntVal (ord(c))
                    | otherwise => raise Error("Argument of \"ord\" does not evaluate to Char: "^
                                               String.concat(map (ppVal 0) aargs), pcall)
                 )
      | "chr" => (case aargs of
                      [IntVal n] => CharVal (chr(n))
                    | otherwise => raise Error("Argument of \"chr\" does not evaluate to Num: "^
                                               String.concat(map (ppVal 0) aargs), pcall)
                 )
      | _ =>
        let
            val vtab' = SymTab.combine (bindParams (fargs, aargs, fid, pdcl, pcall)) vtab
            val res  = evalExp (body, vtab', ftab)
        in
            if typeMatch (rtp, res)
            then res
            else raise Error("Result type does not match the return type!"^
                             " in function: "^fid^" return type: "^ppType(rtp)^
                             " result: "^ppVal 0 res, pcall)
        end

(* evalFunArg takes as argument a FunArg, a vtable, an ftable, and the
position where the call is performed.

It returns a pair of two values: an anonymous SML function, and the
return type of the FunArg.  The anonymous function that is returned
takes a single argument - a list of arguments that should be applied
to the function.  This allows us to evaluate a FunArg once, then call
it several times in a loop.
 *)
and evalFunArg (FunName fid, vtab, ftab, callpos) =
    let
      val fexp = SymTab.lookup fid ftab
    in
      case fexp of
        NONE   => raise Error("Function "^fid^" is not in SymTab!", callpos)
      | SOME f => (fn aargs => callFun(f, aargs, ftab, callpos), getFunRTP f)
    end
   (* TODO TASK 3:

   Add case for Lambda.  This can be done by constructing an
   appropriate FunDec from the lambda and passing it to
   callFunWithVtable.
    *)

(* Interpreter for Fasto programs:
    1. builds the function symbol table,
    2. interprets the body of "main", and
    3. returns its result. *)
and evalProg prog =
    let
      val ftab  = buildFtab prog
      val mainf = SymTab.lookup "main" ftab
    in
      case mainf of
        NONE   => raise Error("Could not find the main function! Aborting! ", (0,0))
      | SOME m =>
          case getFunArgs m of
            [] => callFun(m, [], ftab, (0,0))
          | _  => raise Error("main is not allowed to have parameters", getFunPos m)
    end

end

