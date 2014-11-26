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

val Prog :
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Fasto.UnknownTypes.Prog;
