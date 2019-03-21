open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of bool * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf program =
  let (stack, stmtConf)      = conf     in
  let (state, input, output) = stmtConf in
  match program with
  | [] -> conf
  | BINOP(op) :: rest ->
    (match stack with
     | rhs :: lhs :: tail ->
       eval env ((Language.Expr.evalBinop op lhs rhs) :: tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | CONST(value) :: rest -> eval env (value :: stack, stmtConf) rest
  | READ :: rest ->
    (match input with
     | head :: tail -> eval env (head :: stack, (state, tail, output)) rest
     | [] -> failwith "Empty stack")
  | WRITE :: rest -> 
    (match stack with
     | head :: tail -> eval env (tail, (state, input, output @ [head])) rest
     | [] -> failwith "Empty stack")
  | LD(var) :: rest -> eval env ((state var) :: stack, stmtConf) rest
  | ST(var) :: rest ->
    (match stack with
     | head :: tail ->
       eval env (tail, (Language.Expr.update var head state, input, output)) rest
     | [] -> failwith "Empty stack")
  | LABEL(_) :: rest -> eval env conf rest
  | JMP(l) :: rest -> eval env conf (env#labeled l)
  | CJMP(jumpOnZero, l) :: rest ->
    (match stack with
     | head :: tail -> if (Expr.bool_from_int head) != jumpOnZero
                       then eval env conf (env#labeled l)
                       else eval env conf rest
     | [] -> failwith "Empty stack")

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile stmt =
  let label n = Printf.sprintf "L%d" n in
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  let rec compileWithLabels n = function
  | Stmt.Seq (s1, s2) ->
    let (n1, prg1) = compileWithLabels n  s1 in
    let (n2, prg2) = compileWithLabels n1 s2 in
    (n2, prg1 @ prg2)
  | Stmt.Read x ->
    (n, [READ; ST x])
  | Stmt.Write e ->
    (n, expr e @ [WRITE])
  | Stmt.Assign (x, e) ->
    (n, expr e @ [ST x])
  | Stmt.Skip -> (n, [])
  | Stmt.If(cond, then_branch, else_branch) ->
    let (n, then_prg) = compileWithLabels n then_branch in
    let (n, else_branch) = compileWithLabels n else_branch in
    (n + 2,
     expr cond @ [CJMP(true, label n)] @
     then_prg @
     [JMP(label (n + 1)); LABEL(label n)] @
     else_branch @
     [LABEL(label (n + 1))])
  | Stmt.While(cond, body) ->
    let (n, body_prg) = compileWithLabels n body in
    (n + 2,
    [JMP(label n); LABEL(label (n + 1))] @ body_prg @ [LABEL(label n)] @
    expr cond @ [CJMP(false, label (n + 1))])
  | Stmt.RepeatUntil(body, cond) ->
    let (n, body_prg) = compileWithLabels n body in
    (n + 1, [LABEL(label n)] @ body_prg @ expr cond @ [CJMP(true, label n)])
  in
  let (_, p) = compileWithLabels 1 stmt in
  p
