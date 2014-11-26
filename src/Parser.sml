local
type t__1__ = (int*int)
type t__2__ = (int*int)
type t__3__ = char*(int*int)
type t__4__ = (int*int)
type t__5__ = (int*int)
type t__6__ = (int*int)
type t__7__ = (int*int)
type t__8__ = (int*int)
type t__9__ = (int*int)
type t__10__ = (int*int)
type t__11__ = (int*int)
type t__12__ = string*(int*int)
type t__13__ = (int*int)
type t__14__ = (int*int)
type t__15__ = (int*int)
type t__16__ = (int*int)
type t__17__ = (int*int)
type t__18__ = (int*int)
type t__19__ = (int*int)
type t__20__ = (int*int)
type t__21__ = (int*int)
type t__22__ = (int*int)
type t__23__ = (int*int)
type t__24__ = int*(int*int)
type t__25__ = (int*int)
type t__26__ = (int*int)
type t__27__ = (int*int)
type t__28__ = (int*int)
type t__29__ = (int*int)
type t__30__ = (int*int)
type t__31__ = (int*int)
type t__32__ = (int*int)
type t__33__ = (int*int)
type t__34__ = string*(int*int)
type t__35__ = (int*int)
type t__36__ = (int*int)
in
datatype token =
    BOOL of t__1__
  | CHAR of t__2__
  | CHARLIT of t__3__
  | COMMA of t__4__
  | DEQ of t__5__
  | ELSE of t__6__
  | EOF of t__7__
  | EQ of t__8__
  | FILTER of t__9__
  | FN of t__10__
  | FUN of t__11__
  | ID of t__12__
  | IF of t__13__
  | IN of t__14__
  | INT of t__15__
  | IOTA of t__16__
  | LBRACKET of t__17__
  | LCURLY of t__18__
  | LET of t__19__
  | LPAR of t__20__
  | LTH of t__21__
  | MAP of t__22__
  | MINUS of t__23__
  | NUM of t__24__
  | OP of t__25__
  | PLUS of t__26__
  | RBRACKET of t__27__
  | RCURLY of t__28__
  | READ of t__29__
  | REDUCE of t__30__
  | REPLICATE of t__31__
  | RPAR of t__32__
  | SCAN of t__33__
  | STRINGLIT of t__34__
  | THEN of t__35__
  | WRITE of t__36__
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";


(* A parser definition for Fasto, for use with mosmlyac. *)

open Fasto
open Fasto.UnknownTypes

(* Line 12, file Parser.sml *)
val yytransl = #[
  257 (* BOOL *),
  258 (* CHAR *),
  259 (* CHARLIT *),
  260 (* COMMA *),
  261 (* DEQ *),
  262 (* ELSE *),
  263 (* EOF *),
  264 (* EQ *),
  265 (* FILTER *),
  266 (* FN *),
  267 (* FUN *),
  268 (* ID *),
  269 (* IF *),
  270 (* IN *),
  271 (* INT *),
  272 (* IOTA *),
  273 (* LBRACKET *),
  274 (* LCURLY *),
  275 (* LET *),
  276 (* LPAR *),
  277 (* LTH *),
  278 (* MAP *),
  279 (* MINUS *),
  280 (* NUM *),
  281 (* OP *),
  282 (* PLUS *),
  283 (* RBRACKET *),
  284 (* RCURLY *),
  285 (* READ *),
  286 (* REDUCE *),
  287 (* REPLICATE *),
  288 (* RPAR *),
  289 (* SCAN *),
  290 (* STRINGLIT *),
  291 (* THEN *),
  292 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\003\000\003\000\004\000\004\000\004\000\
\\004\000\005\000\005\000\009\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\007\000\007\000\008\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\001\000\
\\003\000\003\000\003\000\003\000\003\000\006\000\004\000\003\000\
\\004\000\004\000\004\000\006\000\008\000\006\000\009\000\003\000\
\\006\000\004\000\003\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\038\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
\\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\010\000\000\000\000\000\024\000\000\000\000\000\000\000\
\\000\000\017\000\000\000\032\000\037\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\034\000\
\\023\000\000\000\027\000\035\000\000\000\000\000\025\000\012\000\
\\000\000\000\000\000\000\026\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\030\000\000\000\000\000\028\000\
\\000\000\000\000\000\000\029\000\031\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\045\000\046\000\070\000\
\\089\000";

val yysindex = "\003\000\
\\011\255\000\000\197\255\000\000\005\255\000\000\000\000\000\000\
\\197\255\011\255\002\255\000\000\000\255\000\000\019\255\000\000\
\\049\255\032\255\040\255\021\255\073\255\054\255\052\255\000\000\
\\001\255\073\255\047\255\073\255\062\255\073\255\059\255\000\000\
\\067\255\068\255\070\255\000\000\074\255\205\255\197\255\073\255\
\\073\255\025\255\113\255\073\255\120\255\078\255\069\255\145\255\
\\084\255\197\255\247\254\073\255\073\255\073\255\073\255\073\255\
\\073\255\000\000\205\255\003\255\000\000\079\255\073\255\227\255\
\\073\255\000\000\073\255\000\000\000\000\106\255\080\255\087\255\
\\110\255\152\255\246\255\045\255\045\255\000\000\000\000\000\000\
\\000\000\057\255\000\000\000\000\029\000\073\255\000\000\000\000\
\\112\255\073\255\073\255\000\000\073\255\073\255\253\255\073\255\
\\198\255\007\000\205\255\205\255\000\000\044\000\073\255\000\000\
\\073\255\014\000\021\000\000\000\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\116\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\095\255\000\000\000\000\
\\094\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\255\254\000\000\000\000\
\\000\000\000\000\000\000\000\000\239\254\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\006\255\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\190\255\202\255\126\255\158\255\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\229\255\238\255\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000";

val yygindex = "\000\000\
\\000\000\109\000\000\000\254\255\089\000\235\255\216\255\084\000\
\\000\000";

val YYTABLESIZE = 326;
val yytable = "\038\000\
\\011\000\062\000\069\000\001\000\043\000\005\000\013\000\054\000\
\\048\000\005\000\036\000\012\000\004\000\015\000\036\000\072\000\
\\004\000\041\000\059\000\060\000\042\000\003\000\064\000\055\000\
\\084\000\056\000\016\000\024\000\057\000\080\000\074\000\075\000\
\\076\000\077\000\078\000\079\000\025\000\026\000\017\000\021\000\
\\027\000\082\000\028\000\029\000\030\000\085\000\031\000\071\000\
\\032\000\006\000\007\000\022\000\023\000\033\000\034\000\035\000\
\\061\000\039\000\036\000\040\000\037\000\054\000\093\000\008\000\
\\095\000\009\000\044\000\056\000\097\000\098\000\057\000\099\000\
\\100\000\047\000\102\000\024\000\067\000\055\000\049\000\056\000\
\\018\000\106\000\057\000\107\000\025\000\026\000\050\000\051\000\
\\027\000\052\000\028\000\029\000\030\000\053\000\031\000\069\000\
\\032\000\015\000\015\000\015\000\015\000\033\000\034\000\035\000\
\\015\000\066\000\036\000\015\000\037\000\086\000\081\000\087\000\
\\088\000\090\000\015\000\096\000\015\000\054\000\014\000\015\000\
\\015\000\015\000\003\000\065\000\054\000\015\000\011\000\058\000\
\\015\000\019\000\019\000\019\000\019\000\055\000\073\000\056\000\
\\019\000\000\000\057\000\019\000\055\000\000\000\056\000\000\000\
\\000\000\057\000\019\000\063\000\019\000\054\000\000\000\019\000\
\\019\000\019\000\000\000\091\000\054\000\019\000\000\000\000\000\
\\019\000\018\000\018\000\018\000\018\000\055\000\000\000\056\000\
\\018\000\000\000\057\000\018\000\055\000\000\000\056\000\000\000\
\\068\000\057\000\018\000\000\000\018\000\000\000\000\000\018\000\
\\018\000\018\000\000\000\000\000\000\000\018\000\000\000\000\000\
\\018\000\020\000\020\000\020\000\020\000\006\000\007\000\000\000\
\\020\000\103\000\054\000\020\000\000\000\021\000\021\000\021\000\
\\021\000\054\000\020\000\008\000\021\000\009\000\000\000\021\000\
\\020\000\020\000\055\000\000\000\056\000\020\000\021\000\057\000\
\\020\000\055\000\000\000\056\000\021\000\021\000\057\000\054\000\
\\022\000\021\000\022\000\022\000\021\000\000\000\000\000\022\000\
\\000\000\033\000\022\000\033\000\033\000\000\000\000\000\055\000\
\\033\000\056\000\054\000\033\000\057\000\000\000\000\000\022\000\
\\022\000\054\000\083\000\000\000\022\000\000\000\000\000\022\000\
\\033\000\033\000\055\000\054\000\056\000\033\000\000\000\057\000\
\\033\000\055\000\054\000\056\000\000\000\092\000\057\000\000\000\
\\000\000\054\000\000\000\055\000\101\000\056\000\000\000\000\000\
\\057\000\054\000\055\000\000\000\056\000\000\000\104\000\057\000\
\\000\000\055\000\094\000\056\000\000\000\108\000\057\000\105\000\
\\054\000\055\000\000\000\056\000\109\000\000\000\057\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\055\000\000\000\056\000\000\000\000\000\057\000";

val yycheck = "\021\000\
\\003\000\042\000\012\001\001\000\026\000\007\001\009\000\005\001\
\\030\000\011\001\028\001\007\001\007\001\012\001\032\001\025\001\
\\011\001\017\001\040\000\041\000\020\001\011\001\044\000\021\001\
\\065\000\023\001\027\001\003\001\026\001\027\001\052\000\053\000\
\\054\000\055\000\056\000\057\000\012\001\013\001\020\001\008\001\
\\016\001\063\000\018\001\019\001\020\001\067\000\022\001\050\000\
\\024\001\001\001\002\001\012\001\032\001\029\001\030\001\031\001\
\\032\001\004\001\034\001\008\001\036\001\005\001\006\001\015\001\
\\086\000\017\001\020\001\023\001\090\000\091\000\026\001\093\000\
\\094\000\012\001\096\000\003\001\008\001\021\001\020\001\023\001\
\\032\001\103\000\026\001\105\000\012\001\013\001\020\001\020\001\
\\016\001\020\001\018\001\019\001\020\001\020\001\022\001\012\001\
\\024\001\004\001\005\001\006\001\007\001\029\001\030\001\031\001\
\\011\001\028\001\034\001\014\001\036\001\004\001\032\001\032\001\
\\026\001\004\001\021\001\004\001\023\001\005\001\010\000\026\001\
\\027\001\028\001\007\001\004\001\005\001\032\001\032\001\039\000\
\\035\001\004\001\005\001\006\001\007\001\021\001\051\000\023\001\
\\011\001\255\255\026\001\014\001\021\001\255\255\023\001\255\255\
\\255\255\026\001\021\001\035\001\023\001\005\001\255\255\026\001\
\\027\001\028\001\255\255\004\001\005\001\032\001\255\255\255\255\
\\035\001\004\001\005\001\006\001\007\001\021\001\255\255\023\001\
\\011\001\255\255\026\001\014\001\021\001\255\255\023\001\255\255\
\\032\001\026\001\021\001\255\255\023\001\255\255\255\255\026\001\
\\027\001\028\001\255\255\255\255\255\255\032\001\255\255\255\255\
\\035\001\004\001\005\001\006\001\007\001\001\001\002\001\255\255\
\\011\001\004\001\005\001\014\001\255\255\004\001\005\001\006\001\
\\007\001\005\001\021\001\015\001\011\001\017\001\255\255\014\001\
\\027\001\028\001\021\001\255\255\023\001\032\001\021\001\026\001\
\\035\001\021\001\255\255\023\001\027\001\028\001\026\001\005\001\
\\004\001\032\001\006\001\007\001\035\001\255\255\255\255\011\001\
\\255\255\004\001\014\001\006\001\007\001\255\255\255\255\021\001\
\\011\001\023\001\005\001\014\001\026\001\255\255\255\255\027\001\
\\028\001\005\001\032\001\255\255\032\001\255\255\255\255\035\001\
\\027\001\028\001\021\001\005\001\023\001\032\001\255\255\026\001\
\\035\001\021\001\005\001\023\001\255\255\032\001\026\001\255\255\
\\255\255\005\001\255\255\021\001\032\001\023\001\255\255\255\255\
\\026\001\005\001\021\001\255\255\023\001\255\255\032\001\026\001\
\\255\255\021\001\014\001\023\001\255\255\032\001\026\001\004\001\
\\005\001\021\001\255\255\023\001\032\001\255\255\026\001\255\255\
\\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\\021\001\255\255\023\001\255\255\255\255\026\001";

val yyact = vector_ 39 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 37 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 40 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 41 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 45 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 6 : Fasto.Type
val d__2__ = peekVal 5 : string*(int*int)
val d__3__ = peekVal 4 : (int*int)
val d__4__ = peekVal 3 : Fasto.Param list
val d__5__ = peekVal 2 : (int*int)
val d__6__ = peekVal 1 : (int*int)
val d__7__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), (d__4__), (d__7__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 5, file Parser.grm, line 47 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__1__ = peekVal 5 : Fasto.Type
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( FunDec (#1 (d__2__), (d__1__), [], (d__6__), #2 (d__2__)) ) end : Fasto.UnknownTypes.FunDec))
;
(* Rule 6, file Parser.grm, line 50 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 51 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 52 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 53 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 56 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 57 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 60 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( (Lambda
                           (Int, [Param ("x", Int),
                                        Param ("y", Int)],
                            Plus (Var ("x", (d__1__)),
                                        Var ("y", (d__1__)),
                                        (d__1__)) ,(d__1__)))
                        ) end : Fasto.UnknownTypes.FunArg))
;
(* Rule 13, file Parser.grm, line 69 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 70 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 71 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 72 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 74 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 75 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 76 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 77 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 78 *)
val _ = update_ yyact 21
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 22, file Parser.grm, line 80 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( If ((d__2__), (d__4__), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 82 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 84 *)
val _ = update_ yyact 24
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 25, file Parser.grm, line 87 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 89 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 91 *)
val _ = update_ yyact 27
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 28, file Parser.grm, line 93 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : (int*int)
val d__3__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 0 : (int*int)
in
( Replicate ((d__3__), (d__5__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 95 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 7 : (int*int)
val d__2__ = peekVal 6 : (int*int)
val d__3__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 4 : (int*int)
val d__5__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 2 : (int*int)
val d__7__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__8__ = peekVal 0 : (int*int)
in
( Reduce ((d__3__), (d__5__), (d__7__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 97 *)
val _ = update_ yyact 30
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : (int*int)
val d__3__ = peekVal 3 : Fasto.UnknownTypes.FunArg
val d__4__ = peekVal 2 : (int*int)
val d__5__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__6__ = peekVal 0 : (int*int)
in
( Map ((d__3__), (d__5__), (), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 31, file Parser.grm, line 99 *)
val _ = update_ yyact 31
(fn () => repr(let
val d__1__ = peekVal 8 : (int*int)
val d__2__ = peekVal 7 : (int*int)
val d__3__ = peekVal 6 : (int*int)
val d__4__ = peekVal 5 : Fasto.UnknownTypes.FunArg
val d__5__ = peekVal 4 : (int*int)
val d__6__ = peekVal 3 : Fasto.UnknownTypes.Exp
val d__7__ = peekVal 2 : (int*int)
val d__8__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__9__ = peekVal 0 : (int*int)
in
( Reduce ((d__4__), (d__6__), (d__8__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 32, file Parser.grm, line 100 *)
val _ = update_ yyact 32
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 33, file Parser.grm, line 102 *)
val _ = update_ yyact 33
(fn () => repr(let
val d__1__ = peekVal 5 : (int*int)
val d__2__ = peekVal 4 : string*(int*int)
val d__3__ = peekVal 3 : (int*int)
val d__4__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__5__ = peekVal 1 : (int*int)
val d__6__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Let (Dec (#1 (d__2__), (d__4__), (d__3__)), (d__6__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 34, file Parser.grm, line 104 *)
val _ = update_ yyact 34
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 35, file Parser.grm, line 107 *)
val _ = update_ yyact 35
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 36, file Parser.grm, line 108 *)
val _ = update_ yyact 36
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 37, file Parser.grm, line 111 *)
val _ = update_ yyact 37
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( FunName (#1 (d__1__)) ) end : Fasto.UnknownTypes.FunArg))
;
(* Entry Prog *)
val _ = update_ yyact 38 (fn () => raise yyexit (peekVal 0));
val yytables : parseTables =
  ( yyact,
    yytransl,
    yylhs,
    yylen,
    yydefred,
    yydgoto,
    yysindex,
    yyrindex,
    yygindex,
    YYTABLESIZE,
    yytable,
    yycheck );
fun Prog lexer lexbuf = yyparse yytables 1 lexer lexbuf;
