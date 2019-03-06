(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

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
    | Var(name) -> s name
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
              `Nona,  [parseBinop "==";
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
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval conf stmt =
      let (st, i, o) = conf in
      match stmt with
      | Read(var) -> (match i with
        | [] -> failwith (Printf.sprintf "Reached EOF")
        | head :: tail -> (Expr.update var head st, tail, o))
      | Write(expr) -> (st, i, o @ [Expr.eval st expr])
      | Assign(var, expr) -> (Expr.update var (Expr.eval st expr) st, i, o)
      | Seq(stmt1, stmt2) -> eval (eval conf stmt1) stmt2

    (* Statement parser *)
    ostap (
      parse: top_level_stmt;
      top_level_stmt: stmt1: stmt -";"
        stmt2: top_level_stmt { Seq(stmt1, stmt2) } | stmt;
      stmt: read_stmt | write_stmt | assign_stmt;
      assign_stmt: x: IDENT -":=" e: !(Expr.expr) { Assign(x, e) };
      read_stmt: - !(Util.keyword)["read"] -"(" x: IDENT -")" { Read(x) };
      write_stmt: - !(Util.keyword)["write"]
        -"(" e: !(Expr.expr) -")" { Write(e) }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o