(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let rec show = function
    | Int n -> Printf.sprintf "%d" n
    | String s -> Printf.sprintf "\"%s\"" @@ Bytes.to_string s
    | Array arr -> Printf.sprintf "[%s]" (String.concat ", " (List.map show (Array.to_list arr)))
    | Sexp (tag, []) -> Printf.sprintf "`%s" tag
    | Sexp (tag, l) -> Printf.sprintf "`%s (%s)" tag (String.concat ", " (List.map show l))

    let to_int = function 
    | Int n -> n 
    | _     -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a                                          

    let string_val v =
      let buf      = Buffer.create 128 in
      let append s = Buffer.add_string buf s in
      let rec inner = function
      | Int    n    -> append (string_of_int n)
      | String s    -> append "\""; append @@ Bytes.to_string s; append "\""
      | Array  a    -> let n = Array.length a in
                       append "["; Array.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append "]"
      | Sexp (t, a) -> let n = List.length a in
                       append "`"; append t; (if n > 0 then (append " ("; List.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append ")"))
      in
      inner v;
      Bytes.of_string @@ Buffer.contents buf
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st mapping names = L (names, mapping, st)

    (* Drop a local scope *)
    let drop (L (_, _, enclosing)) = enclosing
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read" -> (match i with 
      | z :: i' -> (st, i', o, Some (Value.of_int z))
      | _       -> failwith "Unexpected end of input")
    | "write" -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem" ->
      let [b; j] = args in
      (st, i, o, let i = Value.to_int j in
        Some (match b with
              | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
              | Value.Array    a  -> a.(i)
              | Value.Sexp (_, a) -> List.nth a i)
      )         
    | ".length" ->
      let length = (match List.hd args with
      | Value.Sexp (_, a) -> List.length a
      | Value.Array a     -> Array.length a
      | Value.String s    -> Bytes.length s)
      in
      (st, i, o, Some (Value.of_int length))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | ".stringval"  -> 
      let stringRepr = Value.show @@ List.hd args in
      (st, i, o, Some (Value.of_string @@ Bytes.of_string stringRepr))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const     of int
    (* array              *) | Array     of t list
    (* string             *) | String    of string
    (* S-expressions      *) | Sexp      of string * t list
    (* variable           *) | Var       of string
    (* binary operator    *) | Binop     of string * t * t
    (* element extraction *) | Elem      of t * t
    (* length             *) | Length    of t
    (* string conversion  *) | StringVal of t
    (* function call      *) | Call      of string * t list with show

    type member = MLength | MString

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option

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

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expression, and returns another configuration.
       The environment supplies the following method

           method definition : env -> string -> Value.t list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual
       parameters and a configuration, an returns a pair: the return value for the call and
       the resulting configuration
    *)                                                       
    let rec eval env ((st, i, o, r) as conf) = function
      | Const(num) -> (st, i, o, Some(Value.of_int num))
      | Array(expressions) -> eval env conf (Call(".array", expressions))
      | String(s) -> (st, i, o, Some(Value.of_string (Bytes.of_string s)))
      | Sexp(tag, expressions) ->
        let ((st, i, o, _), values) = evalSequentially env conf expressions in
        (st, i, o, Some(Value.sexp tag values))
      | Var(name) -> (st, i, o, Some(State.eval st name))
      | Binop(name, e1, e2) ->
        let ((st, i, o, _), lhs :: rhs :: []) = evalSequentially env conf [e1; e2] in
        (st, i, o, Some(Value.of_int @@ evalBinop name (Value.to_int lhs) (Value.to_int rhs)))
      | Elem(arr, index) -> eval env conf (Call(".elem", [arr; index]))
      | Length(arr) -> eval env conf (Call(".length", [arr]))
      | Call(callee, args) -> (
        let (conf, argValues) = evalSequentially env conf args in
        (* Printf.printf "calling %s(%s)\n" callee (String.concat ", " (List.map Value.show argValues)); *)
        env#definition env callee argValues conf)
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
            binaryOperand
         );
      binaryOperand:
        obj: subscript m: member? { 
          match m with
          | Some MLength -> Length obj
          | Some MString -> Call(".string", [obj])
          | None         -> obj
        };
      primary:
        callee: IDENT -"(" args: !(Util.list0)[expr] -")" { Call(callee, args) } |
        x: IDENT { Var x }                                                       |
        n: DECIMAL { Const n }                                                   |
        -"[" arr: !(Util.list0)[expr] -"]" { Array arr }                         |
        str: STRING { String (String.sub str 1 (String.length str - 2)) }        |
        ch: CHAR { Const(Char.code ch) }                                         |
        -"`" tag: IDENT values: (-"(" !(Util.list0)[expr] -")")?
          { Sexp(tag, match values with None -> [] | Some l -> l) }              |
        -"(" expr -")";
      subscript:
        arr: primary
        is: ( -"[" !(expr) -"]" )*
        { match is with
          | [] -> arr
          | i :: is -> List.fold_left (fun e index -> Elem(e, index)) (Elem(arr, i)) is };
      member:
        mlength | mstring;
      mlength:
        -".length" { MLength };
      mstring:
        -".string" { MString }
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "_"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse:
            wildcard | sexp | identifier;
          wildcard:
            -"_" { Wildcard };
          sexp:
            -"`" tag: IDENT values: (-"(" !(Util.list0)[parse] -")")?
            { Sexp(tag, match values with None -> [] | Some l -> l) };
          identifier:
            id: IDENT { Ident id }
        )
        
        let rec vars = function
        | Wildcard -> []
        | Ident(name) -> [name]
        | Sexp(_, ps) -> List.fold_left (fun acc p -> vars p @ acc) [] ps

        let rec depth = function
        | Wildcard | Ident(_) -> 0
        | Sexp(_, ps)         -> List.fold_left (fun d p -> max d (depth p) + 1) 0 ps

      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    (* Takes a value to match, a state and a pattern and returns some local state
       if matching succeeds and None otherwise *)
    let match_pattern value pattern =
      let rec match_pattern' value local_state = function
        | Pattern.Wildcard -> Some(local_state)
        | Pattern.Ident(x) -> Some(State.bind x value local_state)
        | Pattern.Sexp(pattern_tag, pattern_elems) -> (match value with
          | Value.Sexp(tag, elements)
            when tag = pattern_tag && List.length pattern_elems = List.length elements ->
            List.fold_left
              match_sexp_payload
              (Some(local_state))
              (List.combine elements pattern_elems)
          | _ -> None)
      and match_sexp_payload res (elem, patt) = match res with
        | Some(s) -> match_pattern' elem s patt
        | None -> None
      in
      match_pattern' value State.undefined pattern

    let rec eval env ((st, i, o, r) as conf) continuation = function
      | Assign(var, subscripts, expr) -> (
        let (conf, indices) = Expr.evalSequentially env conf subscripts in
        let (st, i, o, Some(num)) = Expr.eval env conf expr in
        eval env (update st var num indices, i, o, None) Skip continuation)
      | Seq(stmt1, stmt2) -> eval env conf (appendContinuation stmt2 continuation) stmt1
      | Skip -> (match continuation with
        | Skip -> conf
        | _ -> eval env conf Skip continuation)
      | If(cond, then_branch, else_branch) -> (
        let (st, i, o, Some(Value.Int num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) continuation then_branch
        else eval env (st, i, o, None) continuation else_branch)
      | While(cond, body) -> (
        let (st, i, o, Some(Value.Int num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) (appendContinuation (While(cond, body)) continuation) body
        else eval env (st, i, o, None) Skip continuation)
      | Repeat(body, cond) -> (
        let (st, i, o, _) as conf = eval env conf Skip body in
        let (st, i, o, Some(Value.Int num)) = Expr.eval env conf cond in
        if Expr.bool_from_int num
        then eval env (st, i, o, None) Skip continuation
        else eval env (st, i, o, None) continuation (Repeat(body, cond)))
      | Case (cond, branches) ->
        
        let (st, i, o, Some(value)) = Expr.eval env conf cond in
        
        let rec perform_patternmatching = function
        | [] -> eval env conf Skip continuation
        | (pattern, body) :: remaining_patterns -> (match match_pattern value pattern with
          | Some(local_state) ->
            let st = State.push st local_state (Pattern.vars pattern) in
            eval env (st, i, o, None) continuation (Seq(body, Leave))
          | None -> perform_patternmatching remaining_patterns)
        in
        perform_patternmatching branches
      | Return(None) -> (st, i, o, None)
      | Return(Some(expr)) -> Expr.eval env conf expr
      | Call(callee, args) -> (
        let (st, i, o, _) = Expr.eval env conf (Expr.Call(callee, args)) in
        eval env (st, i, o, None) Skip continuation)
      | Leave -> eval env (State.drop st, i, o, None) Skip continuation
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
        assign_stmt |
        skip_stmt   |
        return_stmt |
        if_stmt     |
        while_stmt  |
        repeat_stmt |
        for_stmt    |
        call_stmt   |
        case_stmt;
      assign_stmt:
        x: IDENT
        subscripts: ( -"[" !(Expr.parse) -"]" )*
        -":="
        e: !(Expr.parse) { Assign(x, subscripts, e) };
      skip_stmt:
        %"skip" { Skip };
      return_stmt:
        %"return"
        expr: (!(Expr.parse))?
        { Return(expr) };
      condition_part:
        cond: !(Expr.parse)
        %"then" then_branch: top_level_stmt
        { (cond, then_branch) };
      if_stmt:
        %"if" first_cond: condition_part
        elif_branches: (%"elif" condition_part)*
        else_branch: (%"else" top_level_stmt)?
        %"fi"
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
        %"while" cond: !(Expr.parse)
        %"do"
        body: top_level_stmt
        %"od"
        { While(cond, body) };
      repeat_stmt:
        %"repeat"
        body: top_level_stmt
        %"until"
        cond: !(Expr.parse)
        { Repeat(body, cond) };
      for_stmt:
        %"for"
        init: stmt -"," cond: !(Expr.parse) -"," inc: stmt
        %"do" body: top_level_stmt %"od"
        { Seq(init, While(cond, Seq(body, inc))) };
      call_stmt:
        callee: IDENT -"(" args: !(Util.list0)[Expr.parse] -")"
        { Call(callee, args) };
      case_stmt:
        %"case" cond: !(Expr.parse) %"of"
        branches: !(Util.list0By)[ostap ("|")][ostap ( !(Pattern.parse) -"->" top_level_stmt )]
        %"esac"
        { Case(cond, branches) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse:
        %"fun"
        name: IDENT
        -"("
        args: !(Util.list0)[ostap(IDENT)]
        -")"
        local_vars: (%"local" !(Util.list)[ostap (IDENT)])?
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      = snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
