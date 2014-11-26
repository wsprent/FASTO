local open Obj Lexing in


  (* A lexer definition for Fasto, for use with mosmllex. *)

  (* boilerplate code for all lexer files... *)

 open Lexing;

 exception Error of string * (int * int) (* (message, (line, column)) *)

 val currentLine = ref 1
 val lineStartPos = ref [0]

 fun resetPos () = (currentLine :=1; lineStartPos := [0])

 fun getPos lexbuf = getLineCol (getLexemeStart lexbuf)
        (!currentLine)
        (!lineStartPos)

 and getLineCol pos line (p1::ps) =
       if pos>=p1 then (line, pos-p1)
       else getLineCol pos (line-1) ps
   | getLineCol pos line [] = raise Error ("",(0,0))

 fun lexerError lexbuf s =
     raise Error (s, getPos lexbuf)

(* This one is language specific, yet very common. Alternative would
   be to encode every keyword as a regexp. This one is much easier. *)
 fun keyword (s, pos) =
     case s of
         "if"           => Parser.IF pos
       | "then"         => Parser.THEN pos
       | "else"         => Parser.ELSE pos
       | "let"          => Parser.LET pos
       | "in"           => Parser.IN pos
       | "int"          => Parser.INT pos
       | "bool"         => Parser.BOOL pos
       | "char"         => Parser.CHAR pos
       | "fun"          => Parser.FUN pos

(* specials: *)
       | "iota"         => Parser.IOTA pos
       | "replicate"    => Parser.REPLICATE pos
       | "map"          => Parser.MAP pos
       | "reduce"       => Parser.REDUCE pos
       | "filter"       => Parser.FILTER pos
       | "scan"         => Parser.SCAN pos
       | "read"         => Parser.READ pos
       | "write"        => Parser.WRITE pos
       | "op"           => Parser.OP pos
       | _              => Parser.ID (s, pos)

 
fun action_20 lexbuf = (
 lexerError lexbuf "Illegal symbol in input" )
and action_19 lexbuf = (
 Parser.EOF (getPos lexbuf) )
and action_18 lexbuf = (
 Parser.COMMA (getPos lexbuf) )
and action_17 lexbuf = (
 Parser.RCURLY (getPos lexbuf) )
and action_16 lexbuf = (
 Parser.LCURLY (getPos lexbuf) )
and action_15 lexbuf = (
 Parser.RBRACKET (getPos lexbuf) )
and action_14 lexbuf = (
 Parser.LBRACKET (getPos lexbuf) )
and action_13 lexbuf = (
 Parser.RPAR   (getPos lexbuf) )
and action_12 lexbuf = (
 Parser.LPAR   (getPos lexbuf) )
and action_11 lexbuf = (
 Parser.LTH    (getPos lexbuf) )
and action_10 lexbuf = (
 Parser.EQ     (getPos lexbuf) )
and action_9 lexbuf = (
 Parser.DEQ    (getPos lexbuf) )
and action_8 lexbuf = (
 Parser.MINUS  (getPos lexbuf) )
and action_7 lexbuf = (
 Parser.PLUS   (getPos lexbuf) )
and action_6 lexbuf = (
 Parser.STRINGLIT
			    ((case String.fromCString (getLexeme lexbuf) of
			       NONE => lexerError lexbuf "Bad string constant"
			     | SOME s => String.substring(s,1,
							  String.size s - 2)),
			     getPos lexbuf) )
and action_5 lexbuf = (
 Parser.CHARLIT
        ((case String.fromCString (getLexeme lexbuf) of
             NONE => lexerError lexbuf "Bad char constant"
           | SOME s => String.sub(s,1)),
           getPos lexbuf) )
and action_4 lexbuf = (
 keyword (getLexeme lexbuf,getPos lexbuf) )
and action_3 lexbuf = (
 case Int.fromString (getLexeme lexbuf) of
                               NONE   => lexerError lexbuf "Bad integer"
                             | SOME i => Parser.NUM (i, getPos lexbuf) )
and action_2 lexbuf = (
 currentLine := !currentLine+1;
                          lineStartPos :=  getLexemeStart lexbuf
                           :: !lineStartPos;
                          Token lexbuf )
and action_1 lexbuf = (
 Token lexbuf )
and action_0 lexbuf = (
 Token lexbuf )
and state_0 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_16 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_16 lexbuf
 else if currChar >= #"0" andalso currChar <= #"9" then  state_13 lexbuf
 else case currChar of
    #"\t" => state_3 lexbuf
 |  #"\r" => state_3 lexbuf
 |  #" " => state_3 lexbuf
 |  #"\n" => action_2 lexbuf
 |  #"\f" => action_2 lexbuf
 |  #"}" => action_17 lexbuf
 |  #"{" => action_16 lexbuf
 |  #"]" => action_15 lexbuf
 |  #"[" => action_14 lexbuf
 |  #"=" => state_15 lexbuf
 |  #"<" => action_11 lexbuf
 |  #"/" => state_12 lexbuf
 |  #"-" => action_8 lexbuf
 |  #"," => action_18 lexbuf
 |  #"+" => action_7 lexbuf
 |  #")" => action_13 lexbuf
 |  #"(" => action_12 lexbuf
 |  #"'" => state_6 lexbuf
 |  #"\"" => state_5 lexbuf
 |  #"\^@" => action_19 lexbuf
 |  _ => action_20 lexbuf
 end)
and state_3 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_31 lexbuf
 |  #"\r" => state_31 lexbuf
 |  #" " => state_31 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_5 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_20);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_28 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_28 lexbuf
 else case currChar of
    #"!" => state_28 lexbuf
 |  #" " => state_28 lexbuf
 |  #"&" => state_28 lexbuf
 |  #"%" => state_28 lexbuf
 |  #"$" => state_28 lexbuf
 |  #"#" => state_28 lexbuf
 |  #"\\" => state_30 lexbuf
 |  #"\"" => action_6 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_6 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_20);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_25 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_25 lexbuf
 else case currChar of
    #"!" => state_25 lexbuf
 |  #" " => state_25 lexbuf
 |  #"&" => state_25 lexbuf
 |  #"%" => state_25 lexbuf
 |  #"$" => state_25 lexbuf
 |  #"#" => state_25 lexbuf
 |  #"\\" => state_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_12 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_20);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"/" => state_24 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_13 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_23 lexbuf
 else backtrack lexbuf
 end)
and state_15 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_10);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"=" => action_9 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_16 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_21 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_21 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_21 lexbuf
 else case currChar of
    #"_" => state_21 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_21 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_21 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_21 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_21 lexbuf
 else case currChar of
    #"_" => state_21 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_23 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_3);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_23 lexbuf
 else backtrack lexbuf
 end)
and state_24 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_1);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\^@" => backtrack lexbuf
 |  #"\n" => backtrack lexbuf
 |  _ => state_24 lexbuf
 end)
and state_25 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"'" => action_5 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_26 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #" " andalso currChar <= #"~" then  state_25 lexbuf
 else backtrack lexbuf
 end)
and state_28 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"(" andalso currChar <= #"[" then  state_28 lexbuf
 else if currChar >= #"]" andalso currChar <= #"~" then  state_28 lexbuf
 else case currChar of
    #"!" => state_28 lexbuf
 |  #" " => state_28 lexbuf
 |  #"&" => state_28 lexbuf
 |  #"%" => state_28 lexbuf
 |  #"$" => state_28 lexbuf
 |  #"#" => state_28 lexbuf
 |  #"\\" => state_30 lexbuf
 |  #"\"" => action_6 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_30 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #" " andalso currChar <= #"~" then  state_28 lexbuf
 else backtrack lexbuf
 end)
and state_31 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_0);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\t" => state_31 lexbuf
 |  #"\r" => state_31 lexbuf
 |  #" " => state_31 lexbuf
 |  _ => backtrack lexbuf
 end)
and Token lexbuf =
  (setLexLastAction lexbuf (magic dummyAction);
   setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_0 lexbuf)

(* The following checks type consistency of actions *)
val _ = fn _ => [action_20, action_19, action_18, action_17, action_16, action_15, action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6, action_5, action_4, action_3, action_2, action_1, action_0];

end
