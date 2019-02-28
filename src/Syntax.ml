(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
