open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions
  Helpful for creating an environment. You can do this with references 
  (not taught) or without. 
  You do not have to use these and you can modify them if you want. 
  If you do not use references, you will need the following data type:
*)
(*type values = Int of int|Bool of bool|String of string*)

(* Adds mapping [x:v] to environment [env] *)
let ref_extend env x v = (x, ref v)::env

let extend env x v = (x,v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec ref_lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else ref_lookup t x

let rec lookup env x = 
  match env with
  [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let ref_extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec ref_update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else ref_update t x v
        
(* Removes the most recent variable,value binding from the environment *)
let rec remove env x = match env with
  [] -> []
  | (var,value)::t -> if x = var then t else (var,value)::(remove t x)

(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)


let not_helper expr = 
  match expr with
    |Bool woop -> Bool (not woop)
    |_ -> raise (TypeError "haha")
  

let add_binop expr1 expr2 = 
  match expr1, expr2 with
    |Int a, Int b -> Int (a + b)
    |_, _ -> raise (TypeError "haha")
let sub_binop expr1 expr2 = 
  match expr1, expr2 with
    |Int a, Int b -> Int (a - b)
    |_, _ -> raise (TypeError "haha")
    
let mult_binop expr1 expr2 = 
  match expr1, expr2 with
    |Int a, Int b -> Int (a * b)
    |_, _ -> raise (TypeError "haha")

let div_binop expr1 expr2 = 
  match expr1, expr2 with
    |Int a, Int b -> 
      if b <> 0 then Int (a / b)
      else raise (DivByZeroError)
    |_, _ -> raise (TypeError "haha")

let greater_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool (a > b)
          |_, _ -> raise (TypeError "haha")

let less_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool (a < b)
          |_, _ -> raise (TypeError "haha")

let greater_equal_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool (a >= b)
          |_, _ -> raise (TypeError "haha")

let less_equal_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool (a <= b)
          |_, _ -> raise (TypeError "haha")

let concat_binop expr1 expr2 = 
  match expr1, expr2 with
          |String a, String b -> String (a ^ b)
          |_, _ -> raise (TypeError "haha")

let equal_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool(a = b)
          |String a, String b -> Bool(a = b)
          |Bool a, Bool b -> Bool(a = b)
          |_, _ -> raise (TypeError "haha")

let not_equal_binop expr1 expr2 = 
  match expr1, expr2 with
          |Int a, Int b -> Bool(a <> b)
          |String a, String b -> Bool(a <> b)
          |Bool a, Bool b -> Bool(a <> b)
          |_, _ -> raise (TypeError "haha")

let or_binop expr1 expr2 = 
  match expr1, expr2 with
          |Bool a, Bool b -> Bool(a || b)
          |_, _ -> raise (TypeError "haha")

let and_binop expr1 expr2 = 
  match expr1, expr2 with
  |Bool a, Bool b -> Bool(a && b)
  |_, _ -> raise (TypeError "haha")

let binop_helper op expr1 expr2 = 
    match op with
      |Add -> add_binop expr1 expr2
      |Sub -> sub_binop expr1 expr2
      |Mult -> mult_binop expr1 expr2
      |Div -> div_binop expr1 expr2
      |Greater -> greater_binop expr1 expr2
      |Less -> less_binop expr1 expr2
      |GreaterEqual -> greater_equal_binop expr1 expr2
      |LessEqual ->less_equal_binop expr1 expr2
      |Concat -> concat_binop expr1 expr2
      |Equal -> equal_binop expr1 expr2
      |NotEqual -> not_equal_binop expr1 expr2
      |Or -> or_binop expr1 expr2
      |And -> and_binop expr1 expr2
        

  
let rec eval_expr env e = match e with
  |Value v -> v
  |ID id -> ref_lookup env id
  |Fun (var, expr) -> Closure (env, var, expr)
  |Not expr -> 
    let evaluated = eval_expr env expr in 
    not_helper evaluated
  |Binop (op, expr1, expr2) ->
    let expr1 = eval_expr env expr1 in
    let expr2 = eval_expr env expr2 in
    binop_helper op expr1 expr2
    
  |If (exprBool, expr1, expr2) ->
    let exprBool = eval_expr env exprBool in
    eval_if env exprBool expr1 expr2

  |FunctionCall (expr1, expr2) -> 
    eval_function_call env expr1 expr2
    

  |Let (var, boool, expr1, expr2) ->
    if boool then
      let env = ref_extend_tmp env var in
      let value = eval_expr env expr1 in
      let _ = ref_update env var value in
      eval_expr env expr2
    else
      let value = eval_expr env expr1 in 
      eval_expr (ref_extend env var value) expr2

and 
eval_if env exprBool expr1 expr2 = 
  match exprBool with
    |Bool result -> 
      if result = true then
        eval_expr env expr1
      else eval_expr env expr2
    |_ -> raise (TypeError "haha")

and 
eval_function_call env expr1 expr2 = 
  let expr1 = eval_expr env expr1 in 
  let expr2 = eval_expr env expr2 in
  match expr1, expr2 with 
    |Closure (a, b, expr3), value -> 
      let extended = ref_extend a b value in
      eval_expr extended expr3
    |_ -> raise (TypeError "haha")
  


(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
let eval_mutop env m = match m with
  |Def (var, expr)-> 
    let temp = ref_extend_tmp env var in 
    let hmm = eval_expr temp expr in
    let _ = ref_update temp var hmm in
    (temp, Some (hmm))
  |Expr (expr) -> (env, Some (eval_expr env expr))
  |NoOp -> (env, None)

