open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Single instruction evaluation
     
     val evalInstruction : config -> insn -> config
   Takes a configuration and an instruction, and returns a configuration
   as a result
 *)
let evalInstruction conf instruction =
  let (stack, stmtConf) = conf in
  let (state, input, output) = stmtConf in
  match instruction with
  | BINOP(op) -> (match stack with
    | rhs :: lhs :: tail ->
      ((Language.Expr.evalBinop op lhs rhs) :: tail, stmtConf)
    | _ -> conf)
  | CONST(value) -> (value :: stack, stmtConf)
  | READ -> (match input with
    | head :: tail -> (head :: stack, (state, tail, output))
    | [] -> failwith (Printf.sprintf "Reached EOF"))
  | WRITE -> (match stack with
    | value :: tail -> (tail, (state, input, output @ [value]))
    | _ -> conf)
  | LD(var) -> ((state var) :: stack, stmtConf)
  | ST(var) -> (match stack with
    | head :: tail -> (tail, (Language.Expr.update var head state, input, output))
    | _ -> conf)

(* Stack machine interpreter
     val eval : config -> prg -> config
   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval conf program = match program with
| [] -> conf
| instruction :: rest -> eval (evalInstruction conf instruction) rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine expression compiler
     val compileExpr = Language.Expr.t -> prg
   A helper that takes an expression in the source language and returns
   an equivalent program for the  stack machine
 *)
let rec compileExpr expr = match expr with
| Language.Expr.Const(value) -> [CONST value]
| Language.Expr.Var(name) -> [LD name]
| Language.Expr.Binop(op, lhs, rhs) ->
  (compileExpr lhs) @ (compileExpr rhs) @ [BINOP op]

(* Stack machine compiler
     val compile : Language.Stmt.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt = match stmt with
| Language.Stmt.Read(var) -> [READ; ST var]
| Language.Stmt.Write(expr) -> (compileExpr expr) @ [WRITE]
| Language.Stmt.Assign(var, expr) -> (compileExpr expr) @ [ST var]
| Language.Stmt.Seq(stmt1, stmt2) -> (compile stmt1) @ (compile stmt2)
