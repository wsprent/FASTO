(* Types and utilities for the abstract syntax of MIPS. *)

structure Mips = struct

datatype Instr =
    LABEL of string
  | EQU of string*string
  | GLOBL of string
  | TEXT of string
  | DATA of string
  | SPACE of string
  | ASCII of string
  | ASCIIZ of string
  | ALIGN of string
  | COMMENT of string
  | LA of string*string
  | LUI of string*string
  | ADD of string*string*string
  | ADDI of string*string*string
  | SUB of string*string*string
  | MUL of string*string*string (* low bytes of result in dest., no overflow *)
  | DIV of string*string*string (* quotient in dest., no remainder *)
  | AND of string*string*string
  | ANDI of string*string*string
  | OR of string*string*string
  | ORI of string*string*string
  | XOR of string*string*string
  | XORI of string*string*string
  | SLL of string*string*string
  | SRA of string*string*string
  | SLT of string*string*string
  | SLTI of string*string*string
  | BEQ  of string*string*string
  | BNE  of string*string*string
  | BGEZ of string*string
  | J of string
  | JAL of string * string list (* label + arg. reg.s *)
  | JR of string * string list (* jump reg. + result reg.s *)
  | LW of string*string*string (* lw rd,i(rs), encoded as LW (rd,rs,i) *)
  | SW of string*string*string (* sw rd,i(rs) encoded as SW (rd,rs,i) *)
  | LB of string*string*string (* lb rd,i(rs) encoded as LB (rd,rs,i) *)
  | SB of string*string*string (* sb rd,i(rs) encoded as SB (rd,rs,i) *)
  | NOP
  | SYSCALL

fun MOVE (rd,rs) = ORI (rd,rs,"0")

fun LI (rd,v) = ORI (rd,"0",v)

type Prog = Instr list

fun ppMips inst
 = case inst of
     LABEL l => l ^ ":"
   | GLOBL s => "\t.globl\t" ^ s
   | TEXT s => "\t.text\t" ^ s
   | DATA s => "\t.data\t" ^ s
   | SPACE s => "\t.space\t" ^ s
   | ASCII s => "\t.ascii\t\"" ^ String.toCString s ^"\""
   | ASCIIZ s => "\t.asciiz\t\"" ^ String.toCString s ^"\""
   | ALIGN s => "\t.align\t" ^ s
   | EQU (l,s) => l ^ "\t=\t" ^ s
   | COMMENT s => "# " ^ s
   | LA (rt,v) => "\tla\t" ^ ppReg rt ^ ", " ^ v
   | LUI (rt,v) => "\tlui\t" ^ ppReg rt ^ ", " ^ v
   | ADD (rd,rs,rt) => "\tadd\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | ADDI (rd,rs,v) => "\taddi\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ v
   | SUB (rd,rs,rt) => "\tsub\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | MUL (rd,rs,rt) => "\tmul\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | DIV (rd,rs,rt) => "\tdiv\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | AND (rd,rs,rt) => "\tand\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | ANDI (rd,rs,v) => "\tandi\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ v
   | OR (rd,rs,rt) => "\tor\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | ORI (rd,rs,v) => "\tori\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ v
   | XOR (rd,rs,rt) => "\txor\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | XORI (rd,rs,v) => "\txori\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ v
   | SLL (rd,rt,v) => "\tsll\t" ^ ppReg rd ^ ", " ^ ppReg rt ^ ", " ^ v
   | SRA (rd,rt,v) => "\tsra\t" ^ ppReg rd ^ ", " ^ ppReg rt ^ ", " ^ v
   | SLT (rd,rs,rt) => "\tslt\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ ppReg rt
   | SLTI (rd,rs,v) => "\tslti\t" ^ ppReg rd ^ ", " ^ ppReg rs ^ ", " ^ v
   | BEQ (rs,rt,v) => "\tbeq\t" ^ ppReg rs ^ ", " ^ ppReg rt ^ ", " ^ v
   | BNE (rs,rt,v) => "\tbne\t" ^ ppReg rs ^ ", " ^ ppReg rt ^ ", " ^ v
   | BGEZ(rs,rt)   => "\tbgez\t"^ ppReg rs ^ ", " ^ ppReg rt
   | J l => "\tj\t" ^ l
   | JAL (l,argRegs) => "\tjal\t" ^ l
   | JR (r,resRegs) => "\tjr\t" ^ ppReg r
   | LW (rd,rs,v) => "\tlw\t" ^ ppReg rd ^ ", " ^ v ^ "(" ^ ppReg rs ^ ")"
   | SW (rd,rs,v) => "\tsw\t" ^ ppReg rd ^ ", " ^ v ^ "(" ^ ppReg rs ^ ")"
   | LB (rd,rs,v) => "\tlb\t" ^ ppReg rd ^ ", " ^ v ^ "(" ^ ppReg rs ^ ")"
   | SB (rd,rs,v) => "\tsb\t" ^ ppReg rd ^ ", " ^ v ^ "(" ^ ppReg rs ^ ")"
   | NOP => "\tnop"
   | SYSCALL => "\tsyscall"

and ppReg r =
  if numerical r then "$" ^ r else r

and numerical s =
  foldl (fn (c,i) => i andalso ord c >= ord #"0" andalso ord c <= ord #"9")
        true (explode s)

and intOfString s =
  foldl ( fn (c,i) => 10*i + ord c- ord #"0" ) 0 (explode s)

  (* output a string in the format accepted by e.g. MARS *)
and ppMipsList [] = ""
  | ppMipsList (i::is) = ppMips i ^ "\n" ^ ppMipsList is

end
