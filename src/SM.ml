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
(* conditional jump                *) | CJMP  of bool * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf program =
  let (controlStack, stack, stmtConf) = conf     in
  let (state, input, output)          = stmtConf in
  match program with
  | [] -> conf
  | BINOP(op) :: rest ->
    (match stack with
     | rhs :: lhs :: tail ->
       eval env (controlStack, (Expr.evalBinop op lhs rhs) :: tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | CONST(value) :: rest -> eval env (controlStack, value :: stack, stmtConf) rest
  | READ :: rest ->
    (match input with
     | head :: tail -> eval env (controlStack, head :: stack, (state, tail, output)) rest
     | [] -> failwith "Empty stack")
  | WRITE :: rest -> 
    (match stack with
     | head :: tail -> eval env (controlStack, tail, (state, input, output @ [head])) rest
     | [] -> failwith "Empty stack")
  | LD(var) :: rest -> eval env (controlStack, (State.eval state var) :: stack, stmtConf) rest
  | ST(var) :: rest ->
    (match stack with
     | head :: tail ->
       eval env (controlStack, tail, (State.update var head state, input, output)) rest
     | [] -> failwith "Empty stack")
  | LABEL(_) :: rest -> eval env conf rest
  | JMP(l) :: _ -> eval env conf (env#labeled l)
  | CJMP(jumpOnZero, l) :: rest ->
    (match stack with
     | head :: tail -> if (Expr.bool_from_int head) != jumpOnZero
                       then eval env conf (env#labeled l)
                       else eval env conf rest
     | [] -> failwith "Empty stack")
  | CALL(callee) :: rest ->
    eval env ((rest, state) :: controlStack, stack, stmtConf) (env#labeled callee)
  | BEGIN(argNames, localVars) :: rest ->
    let localState = State.push_scope state (argNames @ localVars) in
    let bind argName (state, stack) = match stack with
    | [] -> failwith "Empty stack"
    | head :: tail -> (State.update argName head state, tail)
    in
    let (localStateInitialized, stack) = List.fold_right bind argNames (localState, stack) in
    eval env (controlStack, stack, (localStateInitialized, input, output)) rest
  | END :: _ ->
    (match controlStack with
    | [] -> conf
    | (rest, oldState) :: controlStack ->
      eval env (controlStack, stack, (State.drop_scope state oldState, input, output)) rest)

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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (functions, main) =
  let label n = Printf.sprintf "L%d" n in
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in
  (* l is a number that we can start labels in the current code being compiled
     with *)
  (* ctx_l is a label number that marks the code after the current code
     being compiled *)
  (* Returns:
     1) The next free label number to be passed to subsequent invocations
        of this function
     2) The flag whether the context label ctx_l has been jumped to
     3) Compiled instructions *)
  let rec compileWithLabels l ctx_l = function
  | Stmt.Seq (s1, s2) ->
    let (l1, f1, prg1) = compileWithLabels (l + 1) l s1 in
    let (l2, f2, prg2) = compileWithLabels l1 ctx_l s2 in
    (l2, f2, prg1 @ (if f1 then [LABEL(label l)] else []) @ prg2)
  | Stmt.Read x ->
    (l, false, [READ; ST x])
  | Stmt.Write e ->
    (l, false, expr e @ [WRITE])
  | Stmt.Assign (x, e) ->
    (l, false, expr e @ [ST x])
  | Stmt.Skip ->
    (l, false, [])
  | Stmt.If(cond, then_branch, else_branch) ->
    let (l1, _, then_prg) = compileWithLabels (l + 1) ctx_l then_branch in
    let (l2, _, else_prg) = compileWithLabels l1 ctx_l else_branch in
    (l2,
     true,
     expr cond @ [CJMP(true, label l)] @
     then_prg @
     [JMP(label ctx_l); LABEL(label l)] @
     else_prg)
  | Stmt.While(cond, body) ->
    let (l1, _, body_prg) = compileWithLabels (l + 2) l body in
    (l1,
     false,
     [JMP(label l); LABEL(label (l + 1))] @
     body_prg @
     [LABEL(label l)] @
     expr cond @
     [CJMP(false, label (l + 1))])
  | Stmt.Repeat(body, cond) ->
    let (l1, f, body_prg) = compileWithLabels (l + 2) l body in
    (l1,
     false,
     [LABEL(label l)] @
     body_prg @
     (if f then [LABEL(label (l + 1))] else []) @
     expr cond @ [CJMP(true, label l)])
  | Stmt.Call(callee, args) ->
    (l, false, List.fold_right (fun arg rest -> expr arg @ rest) args [CALL(callee)])
  in
  let compileFuncDef (name, (argNames, localVars, body)) (l, rest) = 
    let (l1, f, p) = compileWithLabels (l + 1) l body in
    (l1,
     [LABEL(name); BEGIN(argNames, localVars)] @
     p @
     (if f then [LABEL(label l); END] else [END]) @
     rest)
  in
  let (l, f, p) = compileWithLabels 2 1 main in
  p @ (if f then [LABEL(label 1); END] else [END]) @
  snd (List.fold_right compileFuncDef functions (l, []))
