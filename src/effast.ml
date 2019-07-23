(** AST type definitions  *)

type variable = string
type eff = bool * bool
type typevar = int

let make_counter of_int =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      of_int old )
;;

let resettypevar, newtypevar = make_counter (fun n -> n)
let resetvar, newvar = make_counter (Printf.sprintf "var%d")
let reseteffvar, neweffvar = make_counter (Printf.sprintf "eff%d")

(** {!etype} is used to represent OCaml types that are present in our generator *)
type etype =
  | Typevar of typevar
  | Unit
  | Int
  | Float
  | Bool
  | String
  | Option of etype
  | Ref of etype
  | List of etype
  | Fun of etype * eff * etype

(* [ftv expr] returns free typevariables in {!expr} *)
let rec ftv = function
  | Typevar a -> [ a ]
  | Unit | Int | Float | Bool | String -> []
  | Option e -> ftv e
  | Ref t -> ftv t
  | List et -> ftv et
  | Fun (a, _, r) -> ftv a @ ftv r
;;

type lit =
  | LitUnit
  | LitInt of int
  | LitFloat of float
  | LitBool of bool
  | LitStr of string

(** type term is used to represent all syntax constructs (of OCaml) available in our
generator  *)
type term =
  | Lit of lit
  | Variable of etype * variable
  | ListTrm of etype * term list * eff
  (* [Constructor (type, name, payload_lst)] is used to construct ADT variants *)
  | Constructor of etype * string * term list * eff
  (* [PatternMatch typ matched_trm cases eff] *)
  | PatternMatch of etype * term * (pattern * term) list * eff
  | Lambda of etype * variable * etype * term
  | App of etype * term * etype * term * eff
  | Let of variable * etype * term * term * etype * eff
  | If of etype * term * term * term * eff

and pattern =
  | PattVar of variable
  | PattConstr of etype * string * pattern list

let no_eff = (false, false)
let eff_join (ef, ev) (ef', ev') = (ef || ef', ev || ev')

let eff_leq eff eff_exp =
  match (eff, eff_exp) with
  | (false, true), _ | _, (false, true) -> failwith "eff_leq: this should not happen"
  | (false, false), _ -> true (* no eff, compat with anything *)
  | (true, false), (true, _) -> true
  | (true, true), (true, true) -> true
  | _, _ -> false
;;

(** checks if given type variable (represented as int) occurs in given type expression *)
let rec occurs tvar = function
  | Typevar a -> tvar = a
  | Option a -> occurs tvar a
  | Ref a -> occurs tvar a
  | List a -> occurs tvar a
  | Fun (a, _, b) -> occurs tvar a || occurs tvar b
  | Unit | Int | Float | Bool | String -> false
;;

(** [arity f_typ] determines arity of a function type {!f_typ} *)
let rec arity = function
  | Fun (_, _, b) -> 1 + arity b
  | _ -> 0
;;

(** [subst repl t] substitutes all type variables in [t] with mapping from type variables
    to types given in [repl] *)
let rec subst replacements t =
  match t with
  | Unit | Int | Float | Bool | String -> t
  | Typevar i -> (try List.assoc i replacements with Not_found -> t)
  | Option t' -> Option (subst replacements t')
  | Ref t' -> Ref (subst replacements t')
  | List t' -> List (subst replacements t')
  | Fun (l, e, r) -> Fun (subst replacements l, e, subst replacements r)
;;

let imm_type t =
  let lit_type l =
    match l with
    | LitUnit -> Unit
    | LitInt _ -> Int
    | LitFloat _ -> Float
    | LitBool _ -> Bool
    | LitStr _ -> String
  in
  match t with
  | Lit l -> lit_type l
  | Variable (typ, _) -> typ
  | ListTrm (typ, _, _) -> typ
  | Constructor (typ, _, _, _) -> typ
  | PatternMatch (typ, _, _, _) -> typ
  | Lambda (typ, _, _, _) -> typ
  | App (typ, _, _, _, _) -> typ
  | Let (_, _, _, _, typ, _) -> typ
  | If (typ, _, _, _, _) -> typ
;;

let imm_eff t =
  match t with
  | Lit _ | Variable (_, _) | Lambda (_, _, _, _) -> no_eff
  | Constructor (_, _, _, e) -> e
  | ListTrm (_, _, e) -> e
  | PatternMatch (_, _, _, e) -> e
  | App (_, _, _, _, e) -> e
  | Let (_, _, _, _, _, e) -> e
  | If (_, _, _, _, e) -> e
;;

let rec normalize_eff t =
  match t with
  | Typevar _ | Unit | Int | Float | Bool | String -> t
  | Option t' ->
    let t'' = normalize_eff t' in
    Option t''
  | Ref t' ->
    let t'' = normalize_eff t' in
    Ref t''
  | List t' ->
    let t'' = normalize_eff t' in
    List t''
  | Fun (s, _, t) -> Fun (normalize_eff s, no_eff, normalize_eff t)
;;

let some typ payload eff = Constructor (typ, "Some", [ payload ], eff)
let none typ = Constructor (typ, "None", [], (false, false))
