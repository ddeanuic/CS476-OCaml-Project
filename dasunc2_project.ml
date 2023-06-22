(*
Daniel Dean Asuncion
dasunc2
CS476
Project
*)

open List
open String

type ident = string

type exp = Var of ident | Num of int | Add of exp * exp | Sub of exp * exp
         | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp
         | Char of char 
         | String of string
         | Concat of exp * exp
         | Strlen of exp
         | Strcmp of exp * exp
         | StrAt of exp * exp
         | StrLower of exp
         | StrUpper of exp

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
           | IfC of exp * cmd * cmd | While of exp * cmd
           | Call of ident * ident * exp list | Return of exp
           | Strcpy of ident * exp

type value = IntVal of int | BoolVal of bool | CharVal of char | StringVal of string

type entry = Val of value | Fun of ident list * cmd

type state = ident -> entry option
let empty_state = fun x -> None
let lookup (s : state) (x : ident) : entry option = s x
let update (s : state) (x : ident) (e : entry) : state = fun y -> if y = x then Some e else s y

let rec eval_exp (e : exp) (s : state) : value option =
  match e with
  | Var x -> (match lookup s x with Some (Val v) -> Some v | _ -> None)
  | Num i -> Some (IntVal i)
  | Char c -> Some (CharVal c)
  | String str -> Some (StringVal str)
  | Add (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 + i2))
                     | _, _ -> None)
  | Sub (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (IntVal i1), Some (IntVal i2) -> Some (IntVal (i1 - i2))
                     | _, _ -> None)
  | Bool b -> Some (BoolVal b)
  | And (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (BoolVal b1), Some (BoolVal b2) -> Some (BoolVal (b1 && b2))
                     | _, _ -> None)
  | Or (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (BoolVal b1), Some (BoolVal b2) -> Some (BoolVal (b1 || b2))
                     | _, _ -> None)
  | Eq (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some v1, Some v2 -> Some (BoolVal (v1 = v2))
                     | _, _ -> None)
  | Concat (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                       | Some (StringVal s1), Some (StringVal s2) -> Some (StringVal (s1 ^ s2))
                       | _, _ -> None)
  | Strlen str -> (match eval_exp str s with
                  | Some (StringVal s1) -> Some (IntVal (length s1))
                  | _ -> None)
  | Strcmp (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                       | Some v1, Some v2 -> Some (BoolVal (v1 = v2))
                       | _, _ -> None)
  | StrAt (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                      | Some (StringVal s1), Some (IntVal i1) -> Some (CharVal (get s1 i1))
                      | _ -> None)
  | StrLower str -> (match eval_exp str s with
                    | Some (StringVal s1) -> Some (StringVal (lowercase_ascii s1))
                    | _ -> None)
  | StrUpper str -> (match eval_exp str s with
                    | Some (StringVal s1) -> Some (StringVal (uppercase_ascii s1))
                    | _ -> None)

let rec eval_exps (es : exp list) (s : state) : value list option =
  match es with
  | [] -> Some []
  | e :: rest -> (match eval_exp e s, eval_exps rest s with
                  | Some v, Some vs -> Some (v :: vs)
                  | _, _ -> None)

let rec add_args (s : state) (li : ident list) (lv : value list) : state =
  match li, lv with
  | i :: irest, v :: vrest -> add_args (update s i (Val v)) irest vrest
  | _, _ -> s

type stack = (state * ident) list

type config = cmd * stack * state

let rec step_cmd (c : cmd) (k : stack) (s : state) : config option =
  match c with
  | Assign (x, e) -> (match eval_exp e s with
                      | Some v -> Some (Skip, k, update s x (Val v))
                      | None -> None)
  | Seq (Skip, c2) -> Some (c2, k, s)
  | Seq (c1, c2) -> (match step_cmd c1 k s with
                     | Some (c1', k', s') -> Some (Seq (c1', c2), k', s')
                     | None -> None)
  | Skip -> None
  | IfC (e, c1, c2) -> (match eval_exp e s with
                        | Some (BoolVal true) -> Some (c1, k, s)
                        | Some (BoolVal false) -> Some (c2, k, s)
                        | _ -> None)
  | While (e, c) -> Some (IfC (e, Seq (c, While (e, c)), Skip), k, s)
  | Call (x, f, es) -> (match eval_exps es s with
                        | Some vs -> (match lookup s f with
                                      | Some (Fun (params, c)) -> Some (c, (s, x) :: k, add_args s params vs)
                                      | _ -> None)
                        | None -> None)
  | Return e -> (match eval_exp e s, k with
                 | Some v, (s', x) :: k' -> Some (Skip, k', update s' x (Val v))
                 | _, _ -> None)
  | Strcpy (x, e) -> (match eval_exp e s with
                     | Some v -> Some (Skip, k, update s x (Val v))
                     | None -> None)

let rec run_config (con : config) : config =
  let (c, k, s) = con in
  match step_cmd c k s with
  | Some con' -> run_config con'
  | None -> con

let run_prog (c : cmd) s =
  run_config (c, [], s)

(*State and Command to demonstrate String Concatenation*)
let state0 = update empty_state "f" (Fun (["x"; "y"], Return (Concat (Var "x", Var "y"))))
let prog1 = Call ("x", "f", [String "Hello"; String "World"])

(*State and Command to demonstrate String Length*)
let state1 = update empty_state "f" (Fun (["x"], Return (Strlen (Var "x"))))
let prog2 = Call ("x", "f", [String "Dean"])

(*State and Command to demonstrate String Compare*)
let state2 = update empty_state "f" (Fun (["x"; "y"], Return (Strcmp (Var "x", Var "y"))))
let prog3 = Call ("x", "f", [String "Same"; String "Same"])

(*State and Command to demonstrate String Copy*)
let state3 = update empty_state "f" (Fun (["x"; "y"], Seq (Assign ("y", String "String2"), Strcpy ("x", Var "y"))))
let prog4 = Call ("x", "f", [String "String1"; String "String2"])

(*State and Command to demonstrate String At (Equivalent to [] operator to access a string at index i)*)
let state4 = update empty_state "f" (Fun (["x"; "i"], Return (StrAt (Var "x", Var "i"))))
let prog5 = Call ("x", "f", [String "abcDefg"; Num 3])

(*State and Command to demonstrate String Upper. Converts a string to all upper case*)
let state5 = update empty_state "f" (Fun (["x"], Return (StrLower (Var "x"))))
let prog6 = Call ("x", "f", [String "XTUVWXYZ"])

(*State and Command to demonstrate String Upper. Converts a string to all lower case*)
let state6 = update empty_state "f" (Fun (["x"], Return (StrUpper (Var "x"))))
let prog7 = Call ("x", "f", [String "xtuvwxyz"])

(*----------------Executing Programs----------------*)

let (res_c, res_k, res_s) = run_prog prog1 state0;;
lookup res_s "x";; (*should return (Val (StringVal "HelloWorld"))*)

let (res_c, res_k, res_s) = run_prog prog2 state1;;
lookup res_s "x";; (*should return Some (Val (IntVal 4))*)

let (res_c, res_k, res_s) = run_prog prog3 state2;;
lookup res_s "x";; (*should return Some (Val (BoolVal true))*)

let (res_c, res_k, res_s) = run_prog prog4 state3;;
lookup res_s "x";; (*should return Some (Val (StringVal "String2"))*)

let (res_c, res_k, res_s) = run_prog prog5 state4;;
lookup res_s "x";; (*should return Some (Val (CharVal 'D'))*)

let (res_c, res_k, res_s) = run_prog prog6 state5;;
lookup res_s "x";; (*should return Some (Val (StringVal "xtuvwxyz"))*)

let (res_c, res_k, res_s) = run_prog prog7 state6;;
lookup res_s "x";; (*should return Some (Val (StringVal "XTUVWXYZ"))*)