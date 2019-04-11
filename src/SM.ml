open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of bool * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
(* comment                         *) | COMMENT of string
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let printStack stack = Printf.printf
  "[%s]\n\n"
  (String.concat ", " (List.map Value.show stack))
  
let printInsn i = Printf.printf "%s\n" (GT.transform(insn) (new @insn[show]) () i)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((controlStack, stack, ((state, input, output) as stmtConf)) as conf) program =
  (* printStack stack; (match program with [] -> () | head :: _ -> printInsn head); *)
  match program with
  | [] -> conf
  | BINOP(op) :: rest ->
    (match stack with
     | (Value.Int rhs) :: (Value.Int lhs) :: tail ->
       eval env (controlStack, (Value.of_int @@ Expr.evalBinop op lhs rhs) :: tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | CONST(num) :: rest -> eval env (controlStack, (Value.of_int num) :: stack, stmtConf) rest
  | STRING(str) :: rest ->
    eval env (controlStack, (Value.of_string (Bytes.of_string str)) :: stack, stmtConf) rest
  | SEXP(tag, len) :: rest -> 
    let (values, stack) = split len stack in
    eval env (controlStack, (Value.sexp tag (List.rev values)) :: stack, stmtConf) rest
  | LD(var) :: rest -> eval env (controlStack, (State.eval state var) :: stack, stmtConf) rest
  | ST(var) :: rest ->
    (match stack with
     | head :: tail ->
       eval env (controlStack, tail, (State.update var head state, input, output)) rest
     | _ -> failwith "Empty stack")
  | STA(var, k) :: rest -> (match split k stack with
    | (indices, value :: tail) ->
      eval env (controlStack, tail, (Stmt.update state var value indices, input, output)) rest
    | _ -> failwith "Empty stack")
  | LABEL(_) :: rest -> eval env conf rest
  | JMP(l) :: _ -> eval env conf (env#labeled l)
  | CJMP(jumpOnZero, l) :: rest ->
    (match stack with
     | (Value.Int head) :: tail ->
       if (Expr.bool_from_int head) != jumpOnZero
       then eval env (controlStack, tail, stmtConf) (env#labeled l)
       else eval env (controlStack, tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | CALL(callee, argCount, hasRetVal) :: rest ->
    if env#is_label callee
    then eval env ((rest, state) :: controlStack, stack, stmtConf) (env#labeled callee)
    else eval env (env#builtin conf callee argCount (not hasRetVal)) rest
  | BEGIN(_, argNames, localVars) :: rest ->
    let localState = State.enter state (argNames @ localVars) in
    let bind (state, stack) argName = match stack with
    | [] -> failwith "Empty stack"
    | head :: tail -> (State.update argName head state, tail)
    in
    let (localStateInitialized, stack) = List.fold_left bind (localState, stack) argNames in
    eval env (controlStack, stack, (localStateInitialized, input, output)) rest
  | END :: _ | RET(_) :: _ ->
    (match controlStack with
     | [] -> conf
     | (rest, oldState) :: controlStack ->
       eval env (controlStack, stack, (State.leave state oldState, input, output)) rest)
  | DROP :: rest -> (match stack with
     | _ :: tail ->
       eval env (controlStack, tail, stmtConf) rest
     | [] -> failwith "Empty stack")
  | DUP :: rest -> (match stack with
     | head :: _ ->
       eval env (controlStack, head :: stack, stmtConf) rest
     | [] -> failwith "Empty stack")
  | SWAP :: rest -> (match stack with
     | x :: y :: tail ->
       eval env (controlStack, y :: x :: tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | TAG(t) :: rest -> (match stack with
     | Value.Sexp(t', _) :: tail when t' = t ->
       eval env (controlStack, (Value.of_int 1) :: tail, stmtConf) rest
     | _ :: tail -> eval env (controlStack, (Value.of_int 0) :: tail, stmtConf) rest
     | _ -> failwith "Empty stack")
  | ENTER(scoped_names) :: rest ->
    let bind (state, stack) name = match stack with
    | [] -> failwith "Empty stack"
    | head :: tail -> (State.bind name head state, tail)
    in
    let (local_state, stack) = List.fold_left bind (State.undefined, stack) scoped_names in
    let state = State.push state local_state scoped_names in
    eval env (controlStack, stack, (state, input, output)) rest
  | LEAVE :: rest -> eval env (controlStack, stack, (State.drop state, input, output)) rest
  | COMMENT(_) :: rest -> eval env conf rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.printf "Builtin:\n";*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (functions, main) =
  let label n = Printf.sprintf "L%d" n in
  let rec expr = function
  | Expr.Const  n             -> [CONST n]
  | Expr.Array  elems         -> callExpr ".array" (List.rev elems) true
  | Expr.String s             -> [STRING s]
  | Expr.Sexp   (tag, elems)  -> List.concat (List.map expr elems) @ [SEXP(tag, List.length elems)]
  | Expr.Var    x             -> [LD x]
  | Expr.Binop (op, x, y)     -> expr x @ expr y @ [BINOP op]
  | Expr.Elem  (arr, i)       -> callExpr ".elem" [i; arr] true
  | Expr.Length(arr)          -> callExpr ".length" [arr] true
  | Expr.Call  (callee, args) -> callExpr callee args true
  and callExpr callee args hasRetVal =
    let trueCallee =
      if List.exists (fun (name, _) -> name == callee) functions
      then callee
      else match callee with
      | "read"  -> "Lread"
      | "write" -> "Lwrite"
      | _       -> callee
    in
    List.fold_left
      (fun rest arg -> expr arg @ rest)
      [CALL(trueCallee, List.length args, hasRetVal)]
      args
  in

  let pattern' patterns f = 
    let handleSubpatterns i subpattern = 
      [DUP; CONST(i); CALL(".elem", 2, true);] @ f subpattern
    in
    List.concat @@ List.mapi handleSubpatterns patterns
  in

  (* Generates code for a single branch of pattern matching statement.
     lfalse is a label to jump to if pattern matching fails. 
     Returns the flag whether lfalse has been used, and a list of instructions. *)
  let pattern lfalse patt = 
    let rec inner depth = function
    | Stmt.Pattern.Wildcard            -> [DROP]
    | Stmt.Pattern.Ident(_)            -> [DROP]
    | Stmt.Pattern.Sexp(tag, patterns) ->
      [DUP; TAG(tag); CJMP((*on zero*)true, label (lfalse + depth))] @
      (pattern' patterns (inner (depth + 1))) @ [DROP]
    in
    match patt with
    | Stmt.Pattern.Wildcard -> (false, [])
    | Stmt.Pattern.Ident(_) -> (false, [])
    | Stmt.Pattern.Sexp(tag, patterns)  ->
      (true,
       [DUP; TAG(tag); CJMP((*on zero*)true, label lfalse)] @
       (pattern' patterns (inner 1)))
  and bindings patt =
    let rec inner = function
    | Stmt.Pattern.Wildcard          -> [DROP]
    | Stmt.Pattern.Ident(_)          -> []
    | Stmt.Pattern.Sexp(tag, patterns) -> 
      let elemsCode = (List.concat @@
          List.rev
            (List.mapi (fun i subpatt -> [DUP; CONST(i); CALL(".elem", 2, true); SWAP]) patterns)
      ) @ [DROP]
      in
      [COMMENT(Printf.sprintf "extracting elements from `%s" tag)] @
      elemsCode @
      [COMMENT(Printf.sprintf "matching subpatterns of `%s" tag)] @
      (List.concat @@ List.map inner patterns)
    in
    (match patt with
     | Stmt.Pattern.Wildcard -> [DROP]
     | Stmt.Pattern.Ident(_) -> []
     | Stmt.Pattern.Sexp(_)  -> inner patt) @ [ENTER(List.rev @@ Stmt.Pattern.vars patt)]
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
  | Stmt.Assign (x, [], e) ->
    (l, false, expr e @ [ST x])
  | Stmt.Assign (x, subscripts, e) ->
    let indicesInstructions = (List.fold_left (fun rest e -> expr e @ rest) [] (subscripts @ [e]))
    in
    (l,
    false,
    indicesInstructions @ [STA(x, List.length subscripts)])
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
  | Stmt.Case(value, branches) ->
    let i_branches = List.mapi (fun i x -> (i, x)) branches in
    let num_branches = List.length branches in
    let compileBranch (i, (patt, body)) (l, instructions) =
      let depth = Stmt.Pattern.depth patt in
      
      let rec dropLabels l = function
      | 0 -> (l + 1, [LABEL (label l)])
      | n -> let (l', ls) = dropLabels l (n - 1) in (l' + 1, LABEL(label l') :: DROP :: ls)
      in

      let (l', nextBranchLabels) = dropLabels l depth in

      let (_, compiledMatching) = pattern l patt in
      let (l', f, compiledBody) = compileWithLabels l' ctx_l (Stmt.Seq(body, Stmt.Leave)) in

      (l',
       [COMMENT("---------- matching ----------")] @
       compiledMatching @
       [COMMENT("---------- binding ----------")] @
       bindings patt @
       [COMMENT("---------- body ----------")] @
       compiledBody @
       [JMP(label ctx_l)] @
       [COMMENT("---------- cleanup ----------")] @
       nextBranchLabels @
       instructions)
    in
    let (l, compiledBranches) =
      List.fold_right compileBranch i_branches (l, [])
    in
    (l,
     num_branches != 0,
     expr value @ compiledBranches)
  | Stmt.Leave -> (l, false, [LEAVE])
  | Stmt.Call(callee, args) -> (l, false, callExpr callee args false)
  | Stmt.Return(None) -> (l, false, [RET(false)])
  | Stmt.Return(Some(retExpr)) ->
    (l, false, expr retExpr @ [RET(true)])
  in
  let compileFuncDef (name, (argNames, localVars, body)) (l, rest) = 
    let (l1, f, p) = compileWithLabels (l + 1) l body in
    (l1,
     [LABEL(name);
      COMMENT(Printf.sprintf "---------- definition: %s ----------" name);
      BEGIN(name, argNames, localVars)] @
     p @
     (if f then [LABEL(label l); END] else [END]) @
     rest)
  in
  let (l, f, p) = compileWithLabels 2 1 main in
  p @ (if f then [LABEL(label 1); END] else [END]) @
  snd (List.fold_right compileFuncDef functions (l, []))
