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
type t__12__ = (int*int)
type t__13__ = string*(int*int)
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
type t__24__ = (int*int)
type t__25__ = int*(int*int)
type t__26__ = (int*int)
type t__27__ = (int*int)
type t__28__ = (int*int)
type t__29__ = (int*int)
type t__30__ = (int*int)
type t__31__ = (int*int)
type t__32__ = (int*int)
type t__33__ = (int*int)
type t__34__ = (int*int)
type t__35__ = string*(int*int)
type t__36__ = (int*int)
type t__37__ = (int*int)
type t__38__ = (int*int)
in
datatype token =
    BOOL of t__1__
  | CHAR of t__2__
  | CHARLIT of t__3__
  | COMMA of t__4__
  | DEQ of t__5__
  | DIV of t__6__
  | ELSE of t__7__
  | EOF of t__8__
  | EQ of t__9__
  | FILTER of t__10__
  | FN of t__11__
  | FUN of t__12__
  | ID of t__13__
  | IF of t__14__
  | IN of t__15__
  | INT of t__16__
  | IOTA of t__17__
  | LBRACKET of t__18__
  | LCURLY of t__19__
  | LET of t__20__
  | LPAR of t__21__
  | LTH of t__22__
  | MAP of t__23__
  | MINUS of t__24__
  | NUM of t__25__
  | OP of t__26__
  | PLUS of t__27__
  | RBRACKET of t__28__
  | RCURLY of t__29__
  | READ of t__30__
  | REDUCE of t__31__
  | REPLICATE of t__32__
  | RPAR of t__33__
  | SCAN of t__34__
  | STRINGLIT of t__35__
  | THEN of t__36__
  | TIMES of t__37__
  | WRITE of t__38__
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
  262 (* DIV *),
  263 (* ELSE *),
  264 (* EOF *),
  265 (* EQ *),
  266 (* FILTER *),
  267 (* FN *),
  268 (* FUN *),
  269 (* ID *),
  270 (* IF *),
  271 (* IN *),
  272 (* INT *),
  273 (* IOTA *),
  274 (* LBRACKET *),
  275 (* LCURLY *),
  276 (* LET *),
  277 (* LPAR *),
  278 (* LTH *),
  279 (* MAP *),
  280 (* MINUS *),
  281 (* NUM *),
  282 (* OP *),
  283 (* PLUS *),
  284 (* RBRACKET *),
  285 (* RCURLY *),
  286 (* READ *),
  287 (* REDUCE *),
  288 (* REPLICATE *),
  289 (* RPAR *),
  290 (* SCAN *),
  291 (* STRINGLIT *),
  292 (* THEN *),
  293 (* TIMES *),
  294 (* WRITE *),
    0];

val yylhs = "\255\255\
\\001\000\002\000\002\000\003\000\003\000\004\000\004\000\004\000\
\\004\000\005\000\005\000\009\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
\\006\000\006\000\006\000\006\000\007\000\007\000\008\000\000\000";

val yylen = "\002\000\
\\002\000\003\000\002\000\007\000\006\000\001\000\001\000\001\000\
\\003\000\004\000\002\000\001\000\001\000\001\000\001\000\001\000\
\\003\000\003\000\003\000\003\000\003\000\003\000\003\000\006\000\
\\004\000\003\000\004\000\004\000\004\000\006\000\008\000\006\000\
\\009\000\003\000\006\000\004\000\003\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\000\000\040\000\000\000\007\000\008\000\006\000\
\\000\000\000\000\000\000\001\000\000\000\002\000\000\000\009\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\014\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
\\000\000\000\000\000\000\016\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\010\000\000\000\000\000\026\000\000\000\
\\000\000\000\000\000\000\017\000\000\000\034\000\039\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\036\000\025\000\000\000\029\000\037\000\
\\000\000\000\000\027\000\012\000\000\000\000\000\000\000\028\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\032\000\000\000\000\000\030\000\000\000\000\000\000\000\031\000\
\\033\000";

val yydgoto = "\002\000\
\\004\000\005\000\010\000\019\000\020\000\045\000\046\000\072\000\
\\093\000";

val yysindex = "\005\000\
\\000\255\000\000\050\255\000\000\007\255\000\000\000\000\000\000\
\\050\255\000\255\017\255\000\000\249\254\000\000\018\255\000\000\
\\009\255\020\255\027\255\013\255\040\255\037\255\038\255\000\000\
\\242\254\040\255\029\255\040\255\042\255\040\255\035\255\000\000\
\\041\255\046\255\060\255\000\000\062\255\220\000\050\255\040\255\
\\040\255\077\255\120\255\040\255\206\255\055\255\049\255\106\000\
\\074\255\050\255\246\254\040\255\040\255\040\255\040\255\040\255\
\\040\255\040\255\040\255\000\000\220\000\113\000\000\000\056\255\
\\040\255\139\000\040\255\000\000\040\255\000\000\000\000\088\255\
\\066\255\076\255\089\255\214\255\146\000\058\255\000\000\058\255\
\\008\255\008\255\000\000\000\000\000\000\153\000\000\000\000\000\
\\154\255\040\255\000\000\000\000\097\255\040\255\040\255\000\000\
\\040\255\040\255\176\000\040\255\218\255\183\000\220\000\220\000\
\\000\000\242\255\040\255\000\000\040\255\190\000\213\000\000\000\
\\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\096\255\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\072\255\000\000\000\000\
\\112\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\005\255\000\000\000\000\
\\000\000\000\000\000\000\000\000\245\254\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\016\255\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\051\000\146\255\060\000\
\\253\255\024\000\180\255\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\087\000\093\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000";

val yygindex = "\000\000\
\\000\000\096\000\000\000\255\255\072\000\235\255\215\255\062\000\
\\000\000";

val YYTABLESIZE = 513;
val yytable = "\038\000\
\\064\000\011\000\071\000\041\000\043\000\001\000\042\000\013\000\
\\048\000\006\000\007\000\003\000\005\000\055\000\012\000\074\000\
\\005\000\038\000\061\000\062\000\016\000\038\000\066\000\004\000\
\\008\000\088\000\009\000\004\000\021\000\015\000\076\000\077\000\
\\078\000\079\000\080\000\081\000\082\000\083\000\017\000\022\000\
\\039\000\018\000\024\000\086\000\059\000\023\000\040\000\089\000\
\\073\000\044\000\006\000\007\000\025\000\026\000\047\000\049\000\
\\027\000\069\000\028\000\029\000\030\000\050\000\031\000\055\000\
\\032\000\008\000\051\000\009\000\099\000\033\000\034\000\035\000\
\\101\000\102\000\036\000\103\000\104\000\037\000\106\000\024\000\
\\052\000\057\000\053\000\068\000\058\000\110\000\071\000\111\000\
\\085\000\025\000\026\000\090\000\094\000\027\000\059\000\028\000\
\\029\000\030\000\091\000\031\000\100\000\032\000\092\000\003\000\
\\011\000\014\000\033\000\034\000\035\000\063\000\060\000\036\000\
\\075\000\000\000\037\000\015\000\015\000\015\000\015\000\015\000\
\\000\000\000\000\000\000\015\000\054\000\055\000\015\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\015\000\000\000\015\000\
\\000\000\000\000\015\000\015\000\015\000\056\000\000\000\057\000\
\\015\000\000\000\058\000\015\000\015\000\021\000\021\000\021\000\
\\021\000\021\000\000\000\065\000\059\000\021\000\054\000\055\000\
\\021\000\000\000\000\000\000\000\000\000\000\000\000\000\021\000\
\\098\000\021\000\000\000\000\000\021\000\021\000\021\000\056\000\
\\000\000\057\000\021\000\000\000\058\000\021\000\021\000\020\000\
\\020\000\020\000\020\000\020\000\000\000\000\000\059\000\020\000\
\\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\020\000\000\000\020\000\000\000\000\000\020\000\020\000\
\\020\000\067\000\054\000\055\000\020\000\000\000\000\000\020\000\
\\020\000\095\000\054\000\055\000\000\000\107\000\054\000\055\000\
\\000\000\000\000\000\000\056\000\000\000\057\000\000\000\000\000\
\\058\000\000\000\000\000\056\000\000\000\057\000\000\000\056\000\
\\058\000\057\000\059\000\000\000\058\000\109\000\054\000\055\000\
\\000\000\000\000\059\000\000\000\000\000\000\000\059\000\000\000\
\\019\000\019\000\000\000\019\000\019\000\000\000\000\000\056\000\
\\019\000\057\000\000\000\019\000\058\000\000\000\000\000\000\000\
\\000\000\000\000\019\000\000\000\019\000\000\000\059\000\019\000\
\\019\000\019\000\000\000\018\000\018\000\019\000\018\000\018\000\
\\019\000\000\000\000\000\018\000\000\000\000\000\018\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\018\000\000\000\018\000\
\\000\000\000\000\018\000\018\000\018\000\000\000\022\000\022\000\
\\018\000\022\000\022\000\018\000\000\000\000\000\022\000\023\000\
\\023\000\022\000\023\000\023\000\000\000\000\000\000\000\023\000\
\\022\000\000\000\023\000\000\000\000\000\000\000\022\000\022\000\
\\000\000\023\000\000\000\022\000\000\000\000\000\022\000\023\000\
\\023\000\000\000\024\000\000\000\023\000\024\000\024\000\023\000\
\\035\000\000\000\024\000\035\000\035\000\024\000\000\000\000\000\
\\035\000\000\000\000\000\035\000\000\000\000\000\054\000\055\000\
\\000\000\000\000\024\000\024\000\000\000\054\000\055\000\024\000\
\\035\000\035\000\024\000\000\000\000\000\035\000\000\000\056\000\
\\035\000\057\000\000\000\000\000\058\000\000\000\056\000\000\000\
\\057\000\000\000\070\000\058\000\084\000\000\000\059\000\054\000\
\\055\000\000\000\000\000\000\000\000\000\059\000\054\000\055\000\
\\000\000\000\000\000\000\000\000\000\000\054\000\055\000\097\000\
\\056\000\000\000\057\000\000\000\000\000\058\000\000\000\056\000\
\\000\000\057\000\000\000\087\000\058\000\000\000\056\000\059\000\
\\057\000\000\000\096\000\058\000\054\000\055\000\059\000\000\000\
\\000\000\000\000\000\000\054\000\055\000\059\000\000\000\000\000\
\\000\000\000\000\054\000\055\000\000\000\056\000\000\000\057\000\
\\000\000\000\000\058\000\000\000\056\000\000\000\057\000\000\000\
\\105\000\058\000\000\000\056\000\059\000\057\000\000\000\108\000\
\\058\000\054\000\055\000\059\000\000\000\000\000\112\000\000\000\
\\054\000\055\000\059\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\056\000\000\000\057\000\000\000\000\000\058\000\
\\000\000\056\000\000\000\057\000\000\000\113\000\058\000\000\000\
\\000\000\059\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\059\000";

val yycheck = "\021\000\
\\042\000\003\000\013\001\018\001\026\000\001\000\021\001\009\000\
\\030\000\001\001\002\001\012\001\008\001\006\001\008\001\026\001\
\\012\001\029\001\040\000\041\000\028\001\033\001\044\000\008\001\
\\016\001\067\000\018\001\012\001\009\001\013\001\052\000\053\000\
\\054\000\055\000\056\000\057\000\058\000\059\000\021\001\013\001\
\\004\001\033\001\003\001\065\000\037\001\033\001\009\001\069\000\
\\050\000\021\001\001\001\002\001\013\001\014\001\013\001\021\001\
\\017\001\009\001\019\001\020\001\021\001\021\001\023\001\006\001\
\\025\001\016\001\021\001\018\001\090\000\030\001\031\001\032\001\
\\094\000\095\000\035\001\097\000\098\000\038\001\100\000\003\001\
\\021\001\024\001\021\001\029\001\027\001\107\000\013\001\109\000\
\\033\001\013\001\014\001\004\001\004\001\017\001\037\001\019\001\
\\020\001\021\001\033\001\023\001\004\001\025\001\027\001\008\001\
\\033\001\010\000\030\001\031\001\032\001\033\001\039\000\035\001\
\\051\000\255\255\038\001\004\001\005\001\006\001\007\001\008\001\
\\255\255\255\255\255\255\012\001\005\001\006\001\015\001\255\255\
\\255\255\255\255\255\255\255\255\255\255\022\001\255\255\024\001\
\\255\255\255\255\027\001\028\001\029\001\022\001\255\255\024\001\
\\033\001\255\255\027\001\036\001\037\001\004\001\005\001\006\001\
\\007\001\008\001\255\255\036\001\037\001\012\001\005\001\006\001\
\\015\001\255\255\255\255\255\255\255\255\255\255\255\255\022\001\
\\015\001\024\001\255\255\255\255\027\001\028\001\029\001\022\001\
\\255\255\024\001\033\001\255\255\027\001\036\001\037\001\004\001\
\\005\001\006\001\007\001\008\001\255\255\255\255\037\001\012\001\
\\255\255\255\255\015\001\255\255\255\255\255\255\255\255\255\255\
\\255\255\022\001\255\255\024\001\255\255\255\255\027\001\028\001\
\\029\001\004\001\005\001\006\001\033\001\255\255\255\255\036\001\
\\037\001\004\001\005\001\006\001\255\255\004\001\005\001\006\001\
\\255\255\255\255\255\255\022\001\255\255\024\001\255\255\255\255\
\\027\001\255\255\255\255\022\001\255\255\024\001\255\255\022\001\
\\027\001\024\001\037\001\255\255\027\001\004\001\005\001\006\001\
\\255\255\255\255\037\001\255\255\255\255\255\255\037\001\255\255\
\\004\001\005\001\255\255\007\001\008\001\255\255\255\255\022\001\
\\012\001\024\001\255\255\015\001\027\001\255\255\255\255\255\255\
\\255\255\255\255\022\001\255\255\024\001\255\255\037\001\027\001\
\\028\001\029\001\255\255\004\001\005\001\033\001\007\001\008\001\
\\036\001\255\255\255\255\012\001\255\255\255\255\015\001\255\255\
\\255\255\255\255\255\255\255\255\255\255\022\001\255\255\024\001\
\\255\255\255\255\027\001\028\001\029\001\255\255\004\001\005\001\
\\033\001\007\001\008\001\036\001\255\255\255\255\012\001\004\001\
\\005\001\015\001\007\001\008\001\255\255\255\255\255\255\012\001\
\\022\001\255\255\015\001\255\255\255\255\255\255\028\001\029\001\
\\255\255\022\001\255\255\033\001\255\255\255\255\036\001\028\001\
\\029\001\255\255\004\001\255\255\033\001\007\001\008\001\036\001\
\\004\001\255\255\012\001\007\001\008\001\015\001\255\255\255\255\
\\012\001\255\255\255\255\015\001\255\255\255\255\005\001\006\001\
\\255\255\255\255\028\001\029\001\255\255\005\001\006\001\033\001\
\\028\001\029\001\036\001\255\255\255\255\033\001\255\255\022\001\
\\036\001\024\001\255\255\255\255\027\001\255\255\022\001\255\255\
\\024\001\255\255\033\001\027\001\028\001\255\255\037\001\005\001\
\\006\001\255\255\255\255\255\255\255\255\037\001\005\001\006\001\
\\255\255\255\255\255\255\255\255\255\255\005\001\006\001\007\001\
\\022\001\255\255\024\001\255\255\255\255\027\001\255\255\022\001\
\\255\255\024\001\255\255\033\001\027\001\255\255\022\001\037\001\
\\024\001\255\255\033\001\027\001\005\001\006\001\037\001\255\255\
\\255\255\255\255\255\255\005\001\006\001\037\001\255\255\255\255\
\\255\255\255\255\005\001\006\001\255\255\022\001\255\255\024\001\
\\255\255\255\255\027\001\255\255\022\001\255\255\024\001\255\255\
\\033\001\027\001\255\255\022\001\037\001\024\001\255\255\033\001\
\\027\001\005\001\006\001\037\001\255\255\255\255\033\001\255\255\
\\005\001\006\001\037\001\255\255\255\255\255\255\255\255\255\255\
\\255\255\255\255\022\001\255\255\024\001\255\255\255\255\027\001\
\\255\255\022\001\255\255\024\001\255\255\033\001\027\001\255\255\
\\255\255\037\001\255\255\255\255\255\255\255\255\255\255\255\255\
\\037\001";

val yyact = vector_ 41 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 39 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.UnknownTypes.FunDec list
val d__2__ = peekVal 0 : (int*int)
in
( (d__1__) ) end : Fasto.UnknownTypes.Prog))
;
(* Rule 2, file Parser.grm, line 42 *)
val _ = update_ yyact 2
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.FunDec
val d__3__ = peekVal 0 : Fasto.UnknownTypes.FunDec list
in
( (d__2__) :: (d__3__) ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 3, file Parser.grm, line 43 *)
val _ = update_ yyact 3
(fn () => repr(let
val d__1__ = peekVal 1 : (int*int)
val d__2__ = peekVal 0 : Fasto.UnknownTypes.FunDec
in
( (d__2__) :: [] ) end : Fasto.UnknownTypes.FunDec list))
;
(* Rule 4, file Parser.grm, line 47 *)
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
(* Rule 5, file Parser.grm, line 49 *)
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
(* Rule 6, file Parser.grm, line 52 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Int ) end : Fasto.Type))
;
(* Rule 7, file Parser.grm, line 53 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Bool ) end : Fasto.Type))
;
(* Rule 8, file Parser.grm, line 54 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 0 : (int*int)
in
( Char ) end : Fasto.Type))
;
(* Rule 9, file Parser.grm, line 55 *)
val _ = update_ yyact 9
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.Type
val d__3__ = peekVal 0 : (int*int)
in
( Array (d__2__) ) end : Fasto.Type))
;
(* Rule 10, file Parser.grm, line 58 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 3 : Fasto.Type
val d__2__ = peekVal 2 : string*(int*int)
val d__3__ = peekVal 1 : (int*int)
val d__4__ = peekVal 0 : Fasto.Param list
in
( Param (#1 (d__2__), (d__1__)) :: (d__4__) ) end : Fasto.Param list))
;
(* Rule 11, file Parser.grm, line 59 *)
val _ = update_ yyact 11
(fn () => repr(let
val d__1__ = peekVal 1 : Fasto.Type
val d__2__ = peekVal 0 : string*(int*int)
in
( Param (#1 (d__2__), (d__1__)) :: [] ) end : Fasto.Param list))
;
(* Rule 12, file Parser.grm, line 62 *)
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
(* Rule 13, file Parser.grm, line 71 *)
val _ = update_ yyact 13
(fn () => repr(let
val d__1__ = peekVal 0 : int*(int*int)
in
( Constant (IntVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 14, file Parser.grm, line 72 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : char*(int*int)
in
( Constant (CharVal (#1 (d__1__)), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 15, file Parser.grm, line 73 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( Var (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 16, file Parser.grm, line 74 *)
val _ = update_ yyact 16
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( StringLit (d__1__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 17, file Parser.grm, line 76 *)
val _ = update_ yyact 17
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__3__ = peekVal 0 : (int*int)
in
( ArrayLit ((d__2__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 18, file Parser.grm, line 77 *)
val _ = update_ yyact 18
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Plus ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 19, file Parser.grm, line 78 *)
val _ = update_ yyact 19
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Minus((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 20, file Parser.grm, line 79 *)
val _ = update_ yyact 20
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Mult((d__1__), (d__3__), (d__2__))  ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 21, file Parser.grm, line 80 *)
val _ = update_ yyact 21
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Div((d__1__), (d__3__), (d__2__))   ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 22, file Parser.grm, line 81 *)
val _ = update_ yyact 22
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Equal((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 23, file Parser.grm, line 82 *)
val _ = update_ yyact 23
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( Less ((d__1__), (d__3__), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 24, file Parser.grm, line 84 *)
val _ = update_ yyact 24
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
(* Rule 25, file Parser.grm, line 86 *)
val _ = update_ yyact 25
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp list
val d__4__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), (d__3__), #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 26, file Parser.grm, line 88 *)
val _ = update_ yyact 26
(fn () => repr(let
val d__1__ = peekVal 2 : string*(int*int)
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : (int*int)
in
( Apply (#1 (d__1__), [], #2 (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 27, file Parser.grm, line 91 *)
val _ = update_ yyact 27
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.Type
val d__4__ = peekVal 0 : (int*int)
in
( Read ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 28, file Parser.grm, line 93 *)
val _ = update_ yyact 28
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Write ((d__3__), (), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 29, file Parser.grm, line 95 *)
val _ = update_ yyact 29
(fn () => repr(let
val d__1__ = peekVal 3 : (int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Iota ((d__3__), (d__1__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 30, file Parser.grm, line 97 *)
val _ = update_ yyact 30
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
(* Rule 31, file Parser.grm, line 99 *)
val _ = update_ yyact 31
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
(* Rule 32, file Parser.grm, line 101 *)
val _ = update_ yyact 32
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
(* Rule 33, file Parser.grm, line 103 *)
val _ = update_ yyact 33
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
(* Rule 34, file Parser.grm, line 104 *)
val _ = update_ yyact 34
(fn () => repr(let
val d__1__ = peekVal 2 : (int*int)
val d__2__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__3__ = peekVal 0 : (int*int)
in
( (d__2__) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 35, file Parser.grm, line 106 *)
val _ = update_ yyact 35
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
(* Rule 36, file Parser.grm, line 108 *)
val _ = update_ yyact 36
(fn () => repr(let
val d__1__ = peekVal 3 : string*(int*int)
val d__2__ = peekVal 2 : (int*int)
val d__3__ = peekVal 1 : Fasto.UnknownTypes.Exp
val d__4__ = peekVal 0 : (int*int)
in
( Index (#1 (d__1__), (d__3__), (), (d__2__)) ) end : Fasto.UnknownTypes.Exp))
;
(* Rule 37, file Parser.grm, line 111 *)
val _ = update_ yyact 37
(fn () => repr(let
val d__1__ = peekVal 2 : Fasto.UnknownTypes.Exp
val d__2__ = peekVal 1 : (int*int)
val d__3__ = peekVal 0 : Fasto.UnknownTypes.Exp list
in
( (d__1__) :: (d__3__) ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 38, file Parser.grm, line 112 *)
val _ = update_ yyact 38
(fn () => repr(let
val d__1__ = peekVal 0 : Fasto.UnknownTypes.Exp
in
( (d__1__) :: [] ) end : Fasto.UnknownTypes.Exp list))
;
(* Rule 39, file Parser.grm, line 115 *)
val _ = update_ yyact 39
(fn () => repr(let
val d__1__ = peekVal 0 : string*(int*int)
in
( FunName (#1 (d__1__)) ) end : Fasto.UnknownTypes.FunArg))
;
(* Entry Prog *)
val _ = update_ yyact 40 (fn () => raise yyexit (peekVal 0));
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
