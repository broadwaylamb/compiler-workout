open GT
       
(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4;;

(* We need to distinguish the following operand types: *)
@type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)
with show

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* A comment in assembly                                *) | Comment of string
(* directive                                            *) | Meta  of string

(* arithmetic correction: decrement                     *) | Dec   of opnd
(* arithmetic correction: or 0x0001                     *) | Or1   of opnd
(* arithmetic correction: shl 1                         *) | Sal1  of opnd
(* arithmetic correction: shr 1                         *) | Sar1  of opnd
                                                                                                                                   
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Comment s           -> Printf.sprintf "\t# %s" s
  | Meta   s           -> Printf.sprintf "%s\n" s
  | Dec    s           -> Printf.sprintf "\tdecl\t%s" (opnd s)
  | Or1    s           -> Printf.sprintf "\torl\t$0x0001,\t%s" (opnd s)
  | Sal1   s           -> Printf.sprintf "\tsall\t%s" (opnd s)
  | Sar1   s           -> Printf.sprintf "\tsarl\t%s" (opnd s)
                                         
(* Opening stack machine to use instructions without fully qualified names *)
open SM

let compileFunctionCall env callee argc hasRetVal =
  let pushr, popr = List.split
    (List.map (fun r -> (Push(r), Pop(r))) (env#live_registers 1))
  in
  let env, code =
    if argc = 0
    then env, pushr @ [Call(callee)] @ (List.rev popr)
    else
      let rec pushArgs env instructions = function
        | 0 -> env, instructions
        | argc -> let s, env = env#pop in pushArgs env (Push(s) :: instructions) (argc - 1)
      in
      let env, pushs = pushArgs env [] argc in
      env,
      pushr @
      pushs @
      [Call(callee); Binop("+", L(argc * word_size), esp)] @
      (List.rev popr)
  in
  let env, code =
    if hasRetVal
    then let s, env = env#allocate in env, code @ [Mov(eax, s)]
    else env, code
  in
  env, code

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Takes an environment, a stack machine program, and returns a pair — the updated environment
   and the list of x86 instructions
*)
let rec compile env scode = match scode with
| [] -> env, []
| instr :: scode' ->
  let env, asm =
    (* Printf.printf "\n%s\n\n" env#show_stack; *)
    (* printInsn instr; *)
    match instr with
    | CONST n ->
      let s, env = env#allocate in
      env, [Comment(Printf.sprintf "CONST %d" n); Mov(L ((n lsl 1) lor 1), s)]
    | STRING s ->
      let loc, env = env#string s in
      let s', env = env#allocate in
      let env, code = compileFunctionCall env "Bstring" 1 true in
      env,
      Comment(Printf.sprintf "STRING \"%s\"" s) :: Mov(M ("$" ^ loc), s') :: code
    | SEXP (tag, len) ->
      let tagLoc, env = env#allocate in
      let lenLoc, env = env#allocate in
      let env, code = compileFunctionCall env "Bsexp" (len + 2) true in
      env, 
      [Comment(Printf.sprintf "SEXP (\"`%s\", %d)" tag len);
       Mov(L len, lenLoc);
       Mov(L (env#hash tag), tagLoc)] @ code
    | ARRAY len ->
      let s, env = env#allocate in
      let env, code = compileFunctionCall env "Barray" (len + 1) true in
      env, 
      Comment(Printf.sprintf "ARRAY (%d)" len) :: Mov(L len, s) :: code
    | LD x ->
      let s, env = (env#global x)#allocate in
      env,
      Comment(Printf.sprintf "LD \"%s\"" x) :: (match s with
        | R _ -> [Mov(env#loc x, s)]
        | _   -> [Mov(env#loc x, eax); Mov(eax, s)])
    | ST x ->
      let s, env = (env#global x)#pop in
      let name = env#loc x in
      env,
      Comment(Printf.sprintf "ST \"%s\"" x) :: (match s with
        | R _ -> [Mov(s, name)]
        | _   -> [Mov(s, eax); Mov(eax, name)])
    | STA(var, k) ->
      let varloc  = env#loc var in
      let s,  env = env#allocate in
      let s', env = env#allocate in
      let env, code = compileFunctionCall env "Bsta" (k + 3) false in
      let code = match s with
      | R _ -> Mov(varloc, s) :: code
      | _   -> Mov(varloc, edx) :: Mov(edx, s) :: code
      in
      env,
      Comment(Printf.sprintf "STA(\"%s\", %d)" var k) :: Mov(L k, s') :: code
    | BINOP op -> 
      let rhs, lhs, env = env#pop2 in
      let cmp suff =
        (env#push lhs, (match rhs with
          | R _ -> [Mov(L 0, eax);
                    Sar1 lhs;
                    Sar1 rhs;
                    Binop ("cmp", rhs, lhs)]
          | _   -> [Mov(rhs, edx);
                    Mov(L 0, eax);
                    Sar1 edx;
                    Sal1 lhs;
                    Binop ("cmp", edx, lhs)]) @
        [Set(suff, "%al"); Sal1 eax; Or1 eax; Mov(eax, lhs)])
      in
      let logical op = env#push lhs, [Mov(L 0, eax);
                                      Mov(L 0, edx);
                                      Sar1 lhs;
                                      Sar1 rhs;
                                      Binop("cmp", L 0, lhs);
                                      Set("ne", "%al");
                                      Binop("cmp", L 0, rhs);
                                      Set("ne", "%dl");
                                      Binop(op, eax, edx);
                                      Sal1 edx;
                                      Or1 edx;
                                      Mov(edx, lhs)]
      in
      let env, instructions = match op with
       | "+" -> (env#push lhs, (match rhs with
          | R _ -> [Binop ("+", rhs, lhs);
                    Dec lhs]
          | _   -> [Mov(rhs, eax);
                    Binop ("+", eax, lhs);
                    Dec lhs]))
       | "-" -> (env#push lhs, (match rhs with
          | R _ -> [Binop ("-", rhs, lhs);
                    Or1 lhs]
          | _   -> [Mov(rhs, eax);
                    Binop ("-", eax, lhs);
                    Or1 lhs]))
       | "*" -> (env#push lhs, (match lhs with
          | R _ -> [Sar1 rhs;
                    Sar1 lhs;
                    Binop ("*", rhs, lhs);
                    Sal1 lhs;
                    Or1 lhs]
          | _   -> [Mov(lhs, eax);
                    Sar1 rhs;
                    Sar1 eax;
                    Binop ("*", rhs, eax);
                    Sal1 eax;
                    Or1 eax;
                    Mov(eax, lhs)]))
       | "/" ->
         let s, env = env#allocate in
         env, [Mov (lhs, eax);
               Sar1 rhs;
               Sar1 eax;
               Cltd;
               IDiv rhs;
               Sal1 eax;
               Or1 eax;
               Mov(eax, s)]
       | "%" ->
         let s, env = env#allocate in
         env, [Mov (lhs, eax);
               Sar1 rhs;
               Sar1 eax;
               Cltd;
               IDiv rhs;
               Sal1 edx;
               Or1 edx;
               Mov(edx, s)]
       | "<" ->  cmp "l"
       | ">" ->  cmp "g"
       | "<=" -> cmp "le"
       | ">=" -> cmp "ge"
       | "==" -> cmp "e"
       | "!=" -> cmp "ne"
       | "&&" -> logical "&&"
       | "!!" -> logical "!!"
       | _ -> failwith (Printf.sprintf "Unsupported binary operator %s" op)
      in
      env, Comment(Printf.sprintf "BINOP \"%s\"" op) :: instructions
    | LABEL(l) ->
      env#retrieve_stack l,
      [Comment(Printf.sprintf "LABEL \"%s\"" l); Label(l)]
    | COMMENT(s) ->
      env, [Comment(s)]
    | JMP(l) ->
      env#set_stack l, [Comment(Printf.sprintf "JMP \"%s\"" l); Jmp(l)]
    | CJMP(jumpOnZero, l) ->
      let s, env = env#pop in
      let suff = if jumpOnZero then "e" else "ne" in
      env#set_stack l,
      [Comment(Printf.sprintf "CJMP(onZero: %B, \"%s\")" jumpOnZero l);
       Sar1 s;
       Binop("cmp", L 0, s);
       CJmp(suff, l)]
    | BEGIN(symbol, argNames, localVars) ->
      let env = env#enter symbol argNames localVars in
      let commentStr = Printf.sprintf "BEGIN(\"%s\", [%s], [%s])"
        symbol
        (String.concat ", " argNames)
        (String.concat ", " localVars)
      in
      env, [Comment(commentStr); Push(ebp); Mov(esp, ebp); Binop("-", M("$" ^ env#lsize), esp)]
    | END ->
      env, [Comment("END");
            Label(env#epilogue);
            Mov(ebp, esp);
            Pop(ebp);
            Ret;
            Meta(Printf.sprintf "\t.set\t%s, \t%d" env#lsize (env#allocated * word_size))]
    | CALL(callee, argc, hasRetVal) ->
      let env, code = compileFunctionCall env callee argc hasRetVal in
      env, Comment(Printf.sprintf "CALL(\"%s\", %d, hasRetVal: %B)" callee argc hasRetVal) :: code
    | RET(hasRetVal) -> 
      let comment = Comment(Printf.sprintf "RET(hasRetVal: %B)" hasRetVal) in
      if hasRetVal
      then
        let r, env = env#pop in
        env, [comment; Mov(r, eax); Jmp(env#epilogue)]
      else
        env, [comment; Jmp(env#epilogue)]
    | DROP ->
      let env = if env#is_stack_empty
      then env
      else let _, env = env#pop in env
      in
      env, [Comment "DROP"]
    | DUP ->
      let top = env#peek in
      let s, env = env#allocate in
      env, [Comment "DUP"; Mov(top, s)]
    | SWAP ->
      let x, y = env#peek2 in
      env, [Comment "SWAP"; Mov(x, eax)] @
            (match (x, y) with
            | (R _, _) | (_, R _) -> [Mov(y, x)]
            | _ -> [Mov(y, edx); Mov(edx, x)]) @
           [Mov(eax, y)]
    | TAG(tag) ->
      let s, env = env#allocate in
      let hash = env#hash tag in
      let env, code = compileFunctionCall env "Btag" 2 true in
      env, Comment(Printf.sprintf "TAG(\"%s\")" tag) :: Mov(L hash, s) :: code
    | ENTER(vars) ->
      let env, code =
        List.fold_left
          (fun (env, code) var ->
             let s, env = env#pop in
             let copyFromSymbolicStackToLocalVariable = match s with
             | R _ -> [Mov(s, env#loc var)]
             | _   -> [Mov(s, eax); Mov(eax, env#loc var)]
             in
             env, copyFromSymbolicStackToLocalVariable :: code
          )
          (env#scope @@ List.rev vars, [])
          vars
      in
      env,
      Comment(Printf.sprintf "ENTER([%s])" @@ String.concat ", " vars) :: (List.flatten @@ List.rev code)
    | LEAVE -> env#unscope, [Comment "LEAVE"]
  in
  let env, asm' = compile env scode' in
  env, asm @ asm'

(* A set of strings *)           
module S = Set.Make (String) 

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)           
class env =
  let chars = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in

  let make_assoc l i = 
	  let rec enumerate n = function
	    | [] -> []
	    | h :: t -> (h, n) :: enumerate (n + 1) t
	  in
	  enumerate i l
  in

  let rec assoc  x = function
  | [] -> raise Not_found
  | l :: ls -> try List.assoc x l with Not_found -> assoc x ls
  in

  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    val stackmap    = M.empty (* labels to stack map               *)
    val barrier     = false   (* barrier condition                 *)
                        
    method show_stack =
      GT.show(list) (GT.show(opnd)) stack

    method is_stack_empty = List.length stack == 0
             
    method print_locals =
      Printf.printf "LOCALS: size = %d\n" static_size;
      List.iter
        (fun l ->
          Printf.printf "(";
          List.iter (fun (a, i) -> Printf.printf "%s=%d " a i) l;
          Printf.printf ")\n"
        ) locals;
      Printf.printf "END LOCALS\n"

    (* check barrier condition *)
    method is_barrier = barrier

    (* set barrier *)
    method set_barrier = {< barrier = true >}

    (* drop barrier *)
    method drop_barrier = {< barrier = false >}
                            
    (* associates a stack to a label *)
    method set_stack l =
      (* Printf.printf "Setting stack for %s: %s\n" l self#show_stack; *)
      {< stackmap = M.add l stack stackmap >}
                               
    (* retrieves a stack for a label *)
    method retrieve_stack l =
      let res = try {< stack = M.find l stackmap >} with Not_found -> self in
      (* Printf.printf "Retrieving stack for %s: %s\n" l res#show_stack; *)
      res
                               
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
      	let rec allocate' = function
      	| []                            -> ebx          , 0
      	| (S n)::_                      -> S (n+1)      , n+2
      	| (R n)::_ when n < num_of_regs -> R (n+1)      , stack_slots
      	| _                             -> S static_size, static_size+1
      	in
      	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = match stack with
    | x :: stack' -> x, {< stack = stack' >}
    | _ -> failwith "Error when popping: empty symbolic stack"

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* peeks the top of the stack (the stack does not change) *)
    method peek = List.hd stack

    (* peeks two topmost values from the stack (the stack itself does not change) *)
    method peek2 = let x::y::_ = stack in x, y

    (* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = Pervasives.ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
             
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter fname argNames localNames =
      let n = List.length localNames in
      {< static_size = n;
         stack_slots = n;
         stack = [];
         locals = [make_assoc localNames 0];
         args = make_assoc argNames 0;
         fname = fname >}

    (* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size';
         static_size = static_size';
         locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}
        
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Call ("raw", [Language.Expr.Const 0])))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -g -O0 -m32 -o %s %s/runtime.o %s.s" name inc name)
 
