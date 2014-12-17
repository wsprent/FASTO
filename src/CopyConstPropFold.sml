structure CopyConstPropFold = struct

(*
    (* An optimisation takes a program and returns a new program. *)
    val optimiseProgram : Fasto.KnownTypes.Prog -> Fasto.KnownTypes.Prog
*)

open Fasto
open Fasto.KnownTypes

(* A propagatee is something that we can propagate - either a variable
   name or a constant value. *)
datatype Propagatee = ConstProp of Value
                    | VarProp of string

fun copyConstPropFoldExp vtable e =
    case e of
        Constant x => Constant x
      | StringLit x => StringLit x
      | ArrayLit (es, t, pos) =>
        ArrayLit (map (copyConstPropFoldExp vtable) es, t, pos)
      | Var (name, pos) =>
        (case SymTab.lookup name vtable of
            SOME(VarProp newname) => Var(newname, pos)
         |  SOME(ConstProp value) => Constant(value, pos)
         |  _ => Var(name, pos))
        (* TODO TASK 4: This case currently does nothing.

         You must perform a lookup in the symbol table and if you find
         a Propagatee, return either a new Var or Constant node. *)
      | Plus (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (IntVal x, _), Constant (IntVal y, _)) =>
               Constant (IntVal (x+y), pos)
             | (Constant (IntVal 0, _), _) =>
               e2'
             | (_, Constant (IntVal 0, _)) =>
               e1'
             | _ =>
               Plus (e1', e2', pos)
        end
      | Minus (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (IntVal x, _), Constant (IntVal y, _)) =>
               Constant (IntVal (x-y), pos)
             | (_, Constant (IntVal 0, _)) =>
               e1'
             | _ =>
               Minus (e1', e2', pos)
        end
      | Times (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (_, Constant (IntVal 0, _)) =>
               Constant (IntVal 0, pos)
             | (Constant (IntVal 0, _), _) =>
               (Constant (IntVal 0, pos))
             | (_, Constant (IntVal 1, _)) =>
               e1'
             | (Constant (IntVal 1, _), _) =>
               e2'
             | (Constant (IntVal x, _), Constant (IntVal y, _)) =>
               Constant (IntVal (x*y), pos)
             | _ =>
               Times (e1', e2', pos)
        end
      | Divide (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (IntVal 0, _), _) =>
               Constant(IntVal 0, pos)
             |  (Constant (IntVal x, _), Constant (IntVal y, _)) =>
               Constant (IntVal (Int.quot(x,y)), pos)
             | _ =>
               Divide (e1', e2', pos)
        end
      | Negate (e, pos) =>
        let val e' = copyConstPropFoldExp vtable e
        in case e' of
               (Constant (IntVal x, _)) =>
               Constant (IntVal (~x), pos)
             | _ =>
               Negate (e', pos)
        end
      | Equal (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (IntVal v1, _), Constant(IntVal v2, _)) =>
               Constant (BoolVal (v1 = v2), pos)
            |  (Constant (CharVal v1, _), Constant(CharVal v2, _)) =>
               Constant (BoolVal (v1 = v2), pos)
            |  _ => if e1' = e2'
                    then Constant (BoolVal true, pos)
                    else Equal (e1', e2', pos)
        end
      | Less (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (IntVal v1, _), Constant (IntVal v2, _)) =>
               Constant (BoolVal (v1 < v2), pos)
             | _ => if e1' = e2'
                    then Constant (BoolVal false, pos)
                    else Less (e1', e2', pos)
        end
      | And (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (BoolVal v1,_), Constant ((BoolVal v2),_)) =>
               Constant (BoolVal (v1 andalso v2), pos)
            |  _ => And (e1', e2', pos)
        end
      | Or (e1, e2, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
            val e2' = copyConstPropFoldExp vtable e2
        in case (e1', e2') of
               (Constant (BoolVal v1,_), Constant ((BoolVal v2),_)) =>
               Constant (BoolVal (v1 orelse v2), pos)
             | _ => Or (e1', e2', pos)
        end
      | Not (e, pos) =>
        let val e' = copyConstPropFoldExp vtable e
        in case e' of
               (Constant (BoolVal v, _)) =>
               Constant (BoolVal(not v), pos)
               | _ => Not (e', pos)
        end
      | If (e1, e2, e3, pos) =>
        let val e1' = copyConstPropFoldExp vtable e1
        in case e1' of
               Constant (BoolVal b, _) => if b
                                          then copyConstPropFoldExp vtable e2
                                          else copyConstPropFoldExp vtable e2
             | _ => If (copyConstPropFoldExp vtable e1',
                        copyConstPropFoldExp vtable e2,
                        copyConstPropFoldExp vtable e3,
                        pos)
        end
      | Apply (fname, es, pos) =>
        Apply (fname, map (copyConstPropFoldExp vtable) es, pos)
      | Let (Dec (name, e, decpos), body, pos) =>

        (* TODO TASK 4: This case currently does nothing.

         You must extend this case to expand the vtable' with whatever
         Propagatee that you can get out of e'.  That is, inspect e'
         to see whether it is a constant or variable, and if so,
         insert the appropriate Propagatee value in vtable. *)

        let val e' = copyConstPropFoldExp vtable e
            val vtable' = case e' of
                              Constant(value, _) => SymTab.bind name (ConstProp(value)) vtable
                           |  Var(newname, _) => SymTab.bind name (VarProp(newname)) vtable
                           | _ => vtable
        in Let (Dec (name, e', decpos),
                copyConstPropFoldExp vtable' body,
                pos)
        end
      | Index (name, e, t, pos) =>
        let val e' = copyConstPropFoldExp vtable e
        in (* We can only copy-propagate variables for indexing. *)
            case SymTab.lookup name vtable of
                SOME (VarProp newname) => Index (newname, e', t, pos)
              | _ => Index (name, e, t, pos)
        end
      | Iota (e, pos) =>
        Iota (copyConstPropFoldExp vtable e, pos)
      | Map (farg, e, t1, t2, pos) =>
        Map (copyConstPropFoldFunArg vtable farg,
             copyConstPropFoldExp vtable e,
             t1, t2, pos)
      | Reduce (farg, e1, e2, t, pos) =>
        Reduce (copyConstPropFoldFunArg vtable farg,
                copyConstPropFoldExp vtable e1,
                copyConstPropFoldExp vtable e2,
                t, pos)
      | Replicate (e1, e2, t, pos) =>
        Replicate (copyConstPropFoldExp vtable e1,
                   copyConstPropFoldExp vtable e2,
                   t, pos)
      | Filter (farg, e, t, pos) =>
        Filter (copyConstPropFoldFunArg vtable farg,
                copyConstPropFoldExp vtable e,
                t, pos)
      | Scan (farg, e1, e2, t, pos) =>
        Scan (copyConstPropFoldFunArg vtable farg,
              copyConstPropFoldExp vtable e1,
              copyConstPropFoldExp vtable e2,
              t, pos)
      | ArrCompr (e, bs, cs, e_tp, arr_tps, pos) =>
        ArrCompr (copyConstPropFoldExp vtable e,
                  map (fn (n, x) => (n, copyConstPropFoldExp vtable x)) bs,
                  map (copyConstPropFoldExp vtable) cs,
                  e_tp, arr_tps, pos)
      | Read (t, pos) =>
        Read (t, pos)
      | Write (e, t, pos) =>
        Write (copyConstPropFoldExp vtable e, t, pos)

  (* TODO TASKS 1/4: add cases for Timesv, Dividev, Negatev, Notv, Andv, Orv.  Look at
  how Plus and Minus are implemented for inspiration.
   *)

and copyConstPropFoldFunArg vtable (FunName fname) =
    FunName fname
  | copyConstPropFoldFunArg vtable (Lambda (rettype, params, body, pos)) =
    (* Remove any bindings with the same names as the parameters. *)
    let val paramNames = (map (fn (Param (name, _)) => name) params)
        val vtable' = SymTab.removeMany paramNames vtable
    in Lambda (rettype, params, copyConstPropFoldExp vtable' body, pos)
    end

fun copyConstPropFoldFunDec (FunDec (fname, rettype, params, body, loc)) =
    let val body' = copyConstPropFoldExp (SymTab.empty ()) body
    in FunDec (fname, rettype, params, body', loc)
    end

fun optimiseProgram prog =
    map copyConstPropFoldFunDec prog
end
