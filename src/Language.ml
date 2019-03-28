(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

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
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

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

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval s e = match e with
      | Const(num) -> num
      | Var(name) -> State.eval s name
      | Binop(name, e1, e2) -> evalBinop name (eval s e1) (eval s e2)

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
      primary: x: IDENT { Var x } | n: DECIMAL { Const n } | -"(" expr -")"
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env conf stmt =
      let (st, i, o) = conf in
      match stmt with
      | Read(var) -> (match i with
        | [] -> failwith (Printf.sprintf "Reached EOF")
        | head :: tail -> (State.update var head st, tail, o))
      | Write(expr) -> (st, i, o @ [Expr.eval st expr])
      | Assign(var, expr) -> (State.update var (Expr.eval st expr) st, i, o)
      | Seq(stmt1, stmt2) -> eval env (eval env conf stmt1) stmt2
      | Skip -> conf
      | If(cond, then_branch, else_branch) ->
        if Expr.bool_from_int (Expr.eval st cond)
        then eval env conf then_branch
        else eval env conf else_branch
      | While(cond, body) -> 
        let rec evalWhile conf =
          let (st, _, _) = conf in
          if Expr.bool_from_int (Expr.eval st cond)
          then evalWhile (eval env conf body)
          else conf
        in
        evalWhile conf
      | Repeat(body, cond) ->
        let rec evalRepeatUntil conf =
          let conf = eval env conf body in
          let (st, _, _) = conf in
          if Expr.bool_from_int (Expr.eval st cond)
          then conf
          else evalRepeatUntil conf
        in
        evalRepeatUntil conf
      | Call(callee, args) ->
        let (argNames, localVars, body) = env#definition callee in
        let localState = State.push_scope st (argNames @ localVars) in
        let bindings = List.combine argNames args in
        let localStateInitialized =
          List.fold_right
            (fun (argName, argExpr) s -> State.update argName (Expr.eval st argExpr) s)
            bindings
            localState
        in
        let (expiredLocalState, i, o) = eval env (localStateInitialized, i, o) body in
        (State.drop_scope expiredLocalState st, i, o)

                                
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
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
