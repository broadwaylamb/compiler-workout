(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream,
       an optional return value *)
    type config = State.t * int list * int list * int option

    let int_from_bool b = if b then 1 else 0
    let bool_from_int i = i != 0

    (* Binary operation evaluator
         val evalBinop : string -> int -> int -> int
       Evaluates the given binary operator on lhs and rhs as its arguments
     *)
    let evalBinop name lhs rhs = match name with
    | "+" -> lhs + rhs
    | "-" -> lhs - rhs
    | "*" -> lhs * rhs
    | "/" -> lhs / rhs
    | "%" -> lhs mod rhs
    | "<" -> int_from_bool (lhs < rhs)
    | ">" -> int_from_bool (lhs > rhs)
    | "<=" -> int_from_bool (lhs <= rhs)
    | ">=" -> int_from_bool (lhs >= rhs)
    | "==" -> int_from_bool (lhs = rhs)
    | "!=" -> int_from_bool (lhs <> rhs)
    | "&&" -> int_from_bool ((bool_from_int lhs) && (bool_from_int rhs))
    | "!!" -> int_from_bool ((bool_from_int lhs) || (bool_from_int rhs))
    | _ -> failwith (Printf.sprintf "Unsupported binary operator %s" name)

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration.
       The environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual
       parameters and a configuration, an returns resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) = function
    | Const(num) -> (st, i, o, Some(num))
    | Var(name) -> (st, i, o, Some(State.eval st name))
    | Call(callee, args) -> (
      let (conf, argValues) = evalSequentially env conf args in
      env#definition env callee argValues conf)
    | Binop(name, e1, e2) -> (
      let ((st, i, o, _), lhs :: rhs :: []) = evalSequentially env conf [e1; e2] in
      (st, i, o, Some(evalBinop name lhs rhs)))
    and evalSequentially env conf expressions =
      let (conf, values) = List.fold_left
      (fun (conf, acc) e ->
        let (_, _, _, Some(r)) as newConf = eval env conf e in
        (newConf, r :: acc))
      (conf, [])
      expressions
      in
      (conf, List.rev values)
         
    let parseBinop op = (ostap ($(op)), fun lhs rhs -> Binop(op, lhs, rhs))               

    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (
      parse: expr;
      expr: 
        !(Util.expr
            (fun x -> x)
            [|
              `Lefta, [parseBinop "!!"];
              `Lefta, [parseBinop "&&"];
              `Nona, [parseBinop "==";
                      parseBinop "!=";
                      parseBinop "<=";
                      parseBinop "<" ;
                      parseBinop ">=";
                      parseBinop ">"];
              `Lefta, [parseBinop "+"; parseBinop "-"];
              `Lefta, [parseBinop "*"; parseBinop "/"; parseBinop "%"]
            |]
            primary
         );
      primary:
        callee: IDENT -"(" args: !(Util.list0)[expr] -")" { Call(callee, args) } |
        x: IDENT { Var x }                                                       |
        n: DECIMAL { Const n }                                                   |
        -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((st, i, o, r) as conf) continuation = function
      | Read(var) -> (match i with
        | [] -> failwith "Reached EOF"
        | head :: tail -> eval env (State.update var head st, tail, o, None) Skip continuation)
      | Write(expr) -> (
        let (st, i, o, Some(num)) = Expr.eval env conf expr in
        eval env (st, i, o @ [num], None) Skip continuation)
      | Assign(var, expr) -> (
        let (st, i, o, Some(num)) = Expr.eval env conf expr in
        eval env (State.update var num st, i, o, None) Skip continuation)
      | Seq(stmt1, stmt2) -> eval env conf (appendContinuation stmt2 continuation) stmt1
      | Skip -> (match continuation with
        | Skip -> conf
        | _ -> eval env conf Skip continuation)
      | If(cond, then_branch, else_branch) -> (
        let (st, i, o, Some(num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) continuation then_branch
        else eval env (st, i, o, None) continuation else_branch)
      | While(cond, body) -> (
        let (st, i, o, Some(num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) (appendContinuation (While(cond, body)) continuation) body
        else eval env (st, i, o, None) Skip continuation)
      | Repeat(body, cond) -> (
        let (st, i, o, _) as conf = eval env conf Skip body in
        let (st, i, o, Some(num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) Skip continuation
        else eval env (st, i, o, None) continuation (Repeat(body, cond)))
      | Return(None) -> (st, i, o, None)
      | Return(Some(expr)) -> Expr.eval env conf expr
      | Call(callee, args) -> (
        let (st, i, o, _) = Expr.eval env conf (Expr.Call(callee, args)) in
        eval env (st, i, o, None) Skip continuation)
    and appendContinuation stmt = function
      | Skip -> stmt
      | continuation -> Seq(stmt, continuation)
         
    (* Statement parser *)
    ostap (
      parse:
        top_level_stmt;
      top_level_stmt:
        stmt1: stmt -";" stmt2: top_level_stmt { Seq(stmt1, stmt2) } | stmt;
      stmt: 
        read_stmt   |
        write_stmt  |
        assign_stmt |
        skip_stmt   |
        return_stmt |
        if_stmt     |
        while_stmt  |
        repeat_stmt |
        for_stmt    |
        call_stmt;
      assign_stmt:
        x: IDENT -":=" e: !(Expr.parse) { Assign(x, e) };
      read_stmt:
        - !(Util.keyword)["read"] -"(" x: IDENT -")" { Read(x) };
      write_stmt:
        - !(Util.keyword)["write"] -"(" e: !(Expr.parse) -")" { Write(e) };
      skip_stmt:
        - !(Util.keyword)["skip"] { Skip };
      return_stmt:
        - !(Util.keyword)["return"]
        expr: (!(Expr.parse))?
        { Return(expr) };
      condition_part:
        cond: !(Expr.parse)
        - !(Util.keyword)["then"] then_branch: top_level_stmt
        { (cond, then_branch) };
      if_stmt:
        - !(Util.keyword)["if"] first_cond: condition_part
        elif_branches: (- !(Util.keyword)["elif"] condition_part)*
        else_branch: (- !(Util.keyword)["else"] top_level_stmt)?
        - !(Util.keyword)["fi"]
        {
          let (cond, body) = first_cond in
          let else_branch = match else_branch with
          | None -> Skip
          | Some stmt -> stmt
          in
          let fold_elif (cond, then_branch) else_branch = 
            If(cond, then_branch, else_branch)
          in
          let elif_bodies =
            List.fold_right fold_elif elif_branches else_branch
          in
          If(cond, body, elif_bodies)
        };
      while_stmt:
        - !(Util.keyword)["while"] cond: !(Expr.parse)
        - !(Util.keyword)["do"]
        body: top_level_stmt
        - !(Util.keyword)["od"]
        { While(cond, body) };
      repeat_stmt:
        - !(Util.keyword)["repeat"]
        body: top_level_stmt
        - !(Util.keyword)["until"]
        cond: !(Expr.parse)
        { Repeat(body, cond) };
      for_stmt:
        - !(Util.keyword)["for"]
        init: stmt -"," cond: !(Expr.parse) -"," inc: stmt
        - !(Util.keyword)["do"] body: top_level_stmt - !(Util.keyword)["od"]
        { Seq(init, While(cond, Seq(body, inc))) };
      call_stmt:
        callee: IDENT -"(" args: !(Util.list0)[Expr.parse] -")"
        { Call(callee, args) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (     
      parse:
        - !(Util.keyword)["fun"]
        name: IDENT
        -"("
        args: !(Util.list0)[ostap (IDENT)]
        -")"
        local_vars: (- !(Util.keyword)["local"] !(Util.list)[ostap (IDENT)])?
        -"{"
        body: !(Stmt.parse)
        -"}"
        { (name, (args, (match local_vars with None -> [] | Some vars -> vars), body)) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =                                                                      
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
