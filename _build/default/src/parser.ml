open MicroCamlTypes
open Utils
open TokenTypes

(* Provided functions - DO NOT MODIFY *)

(* Matches the next token in the list, throwing an error if it doesn't match the given token *)
let match_token (toks: token list) (tok: token) =
  match toks with
  | [] -> raise (InvalidInputException(string_of_token tok))
  | h::t when h = tok -> t
  | h::_ -> raise (InvalidInputException(
      Printf.sprintf "Expected %s from input %s, got %s"
        (string_of_token tok)
        (string_of_list string_of_token toks)
        (string_of_token h)))

(* Matches a sequence of tokens given as the second list in the order in which they appear, throwing an error if they don't match *)
let match_many (toks: token list) (to_match: token list) =
  List.fold_left match_token toks to_match

(* Return the next token in the token list as an option *)
let lookahead (toks: token list) = 
  match toks with
  | [] -> None
  | h::t -> Some h

(* Return the token at the nth index in the token list as an option*)
let rec lookahead_many (toks: token list) (n: int) = 
  match toks, n with
  | h::_, 0 -> Some h
  | _::t, n when n > 0 -> lookahead_many t (n-1)
  | _ -> None

(* Part 2: Parsing expressions *)

let rec parse_expr toks = 
  match lookahead toks with
  | Some Tok_Let -> parse_let toks
  | Some Tok_If -> parse_if toks
  | Some Tok_Fun -> parse_fun toks
  | _ -> parse_or toks
  
  and
  parse_let toks = 
    let token_let = match_token toks Tok_Let in
    let exists_rec = (lookahead token_let = Some Tok_Rec) in
    let token_rec = if exists_rec then match_token token_let Tok_Rec else token_let in
    match lookahead token_rec with
      | Some Tok_ID id -> 
        let token_id = match_token token_rec (Tok_ID id) in
        let token_equals = match_token token_id Tok_Equal in
        let (token_list, expr1) = parse_expr token_equals in
        let token_in = match_token token_list Tok_In in 
        let (token_list, expr2) = parse_expr token_in in 
        (token_list, Let (id, exists_rec, expr1, expr2))
      |_ -> raise (InvalidInputException "haha")

  and
  parse_if toks = 
    let token_if = match_token toks Tok_If in
    let (token_list, expr1) = parse_expr token_if in
    let token_then = match_token token_list Tok_Then in 
    let (token_list, expr2) = parse_expr token_then in
    let token_else = match_token token_list Tok_Else in 
    let (token_list, expr3) = parse_expr token_else in 
    (token_list, If (expr1, expr2, expr3))
  
  and
  parse_fun toks =
    let token_fun = match_token toks Tok_Fun in 
    match lookahead token_fun with
    | Some Tok_ID id -> 
      let token_id = match_token token_fun (Tok_ID id) in
      let token_arrow = match_token token_id Tok_Arrow in 
      let (token_list, expr) = parse_expr token_arrow in
      (token_list, Fun (id, expr))
    |_ -> raise (InvalidInputException "haha")

  and
  parse_or toks = 
      let (token_list, expr1) = parse_and toks in 
      if lookahead token_list = Some Tok_Or then
        let token_or = match_token token_list Tok_Or in 
        let (token_list, expr2) = parse_or token_or in 
        (token_list, Binop (Or, expr1, expr2))
      else
        (token_list, expr1)
  
  and
  parse_and toks = 
      let (token_list, expr1) = parse_equality toks in 
      if lookahead token_list = Some Tok_And then
        let token_and = match_token token_list Tok_And in 
        let (token_list, expr2) = parse_and token_and in 
        (token_list, Binop (And, expr1, expr2))
      else
        (token_list, expr1)

  and
  parse_equality toks = 
      let (token_list, expr1) = parse_relational toks in
      if lookahead token_list = Some Tok_Equal then 
        let token_equals = match_token token_list Tok_Equal in
        let (token_list, expr2) = parse_equality token_equals in 
        (token_list, Binop (Equal, expr1, expr2))
      else if lookahead token_list = Some Tok_NotEqual then
        let token_equals = match_token token_list Tok_NotEqual in
        let (token_list, expr2) = parse_equality token_equals in 
        (token_list, Binop (NotEqual, expr1, expr2))
      else
        (token_list, expr1)
  and
  parse_relational toks = 
    let (token_list, expr1) = parse_additive toks in
    if lookahead token_list = Some Tok_Greater then 
      let token_equals = match_token token_list Tok_Greater in
      let (token_list, expr2) = parse_relational token_equals in 
      (token_list, Binop (Greater, expr1, expr2))
    else if lookahead token_list = Some Tok_Less then 
      let token_equals = match_token token_list Tok_Less in
      let (token_list, expr2) = parse_relational token_equals in 
      (token_list, Binop (Less, expr1, expr2))
    else if lookahead token_list = Some Tok_GreaterEqual then 
      let token_equals = match_token token_list Tok_GreaterEqual in
      let (token_list, expr2) = parse_relational token_equals in 
      (token_list, Binop (GreaterEqual, expr1, expr2))
    else if lookahead token_list = Some Tok_LessEqual then
      let token_equals = match_token token_list Tok_LessEqual in
      let (token_list, expr2) = parse_relational token_equals in 
      (token_list, Binop (LessEqual, expr1, expr2))
    else
      (token_list, expr1)


  and
  parse_additive toks = 
      let (token_list, expr1) = parse_mult toks in
      if lookahead token_list = Some Tok_Add then 
        let token_add = match_token token_list Tok_Add in 
        let (token_list, expr2) = parse_additive token_add in 
        (token_list, Binop (Add, expr1, expr2))
      else if lookahead token_list = Some Tok_Sub then 
        let token_add = match_token token_list Tok_Sub in 
        let (token_list, expr2) = parse_additive token_add in 
        (token_list, Binop (Sub, expr1, expr2))
      else 
        (token_list, expr1)

  and
  parse_mult toks = 
      let (token_list, expr1) = parse_concat toks in 
      if lookahead token_list = Some Tok_Mult then 
        let token_mult = match_token token_list Tok_Mult in 
        let (token_list, expr2) = parse_mult token_mult in 
        (token_list, Binop (Mult, expr1, expr2))
      else if lookahead token_list = Some Tok_Div then 
        let token_mult = match_token token_list Tok_Div in 
        let (token_list, expr2) = parse_mult token_mult in 
        (token_list, Binop (Div, expr1, expr2))
      else
        (token_list, expr1)

  and
  parse_concat toks = 
      let (token_list, expr1) = parse_unary toks in 
      if lookahead token_list = Some Tok_Concat then 
        let token_concat = match_token token_list Tok_Concat in 
        let (token_list, expr2) = parse_concat token_concat in
        (token_list, Binop (Concat, expr1, expr2))
      else
        (token_list, expr1)
  
  and
  parse_unary toks = match lookahead toks with
      |Some Tok_Not ->
        let token_not = match_token toks Tok_Not in 
        let (token_list, expr) = parse_unary token_not in 
        (token_list, Not (expr))
      |_ -> 
        parse_func toks
  
  and
  parse_func toks = 
      let (token_list, expr1) = parse_primary toks in match lookahead token_list with
      Some Tok_Int _ | Some Tok_Bool _ | Some Tok_String _ | Some Tok_ID _ | Some Tok_LParen -> 
          let (token_list, expr2) = parse_primary token_list in 
          (token_list, FunctionCall (expr1, expr2))
      |_ ->
        (token_list, expr1)



  and
  parse_primary toks = match lookahead toks with
      |Some Tok_Int id -> (match_token toks (Tok_Int id), Value (Int (id)))
      |Some Tok_Bool id -> (match_token toks (Tok_Bool id), Value (Bool (id)))
      |Some Tok_String id -> (match_token toks (Tok_String id), Value (String (id)))
      |Some Tok_ID id -> (match_token toks (Tok_ID id), ID (id))
      |Some Tok_LParen-> 
        let l_paren = match_token toks Tok_LParen in 
        let (token_list, expr) = parse_expr l_paren in 
        let r_paren = match_token token_list Tok_RParen in 
        (r_paren, expr)
      |_ -> raise (InvalidInputException "haha")





(* Part 3: Parsing mutop *)

let rec parse_mutop toks = match lookahead toks with
    |Some Tok_DoubleSemi -> (match_token toks Tok_DoubleSemi, NoOp)
    |Some Tok_Def -> parse_def toks
    |_ -> let (token_list, expr1) = parse_expr toks in 
    (match_token token_list Tok_DoubleSemi, Expr (expr1))

  and
  parse_def toks = 
      let token_def = match_token toks Tok_Def in 
      match lookahead token_def with 
      |Some Tok_ID id -> 
        let token_id = match_token token_def (Tok_ID id) in
        let kill_equalsign = match_token token_id Tok_Equal in 
        let (token_list, expr1) = parse_expr kill_equalsign in 
        (match_token token_list Tok_DoubleSemi, Def (id, expr1))
      |_ -> raise (InvalidInputException "haha")