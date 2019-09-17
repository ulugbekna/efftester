(** AST type definitions  *)

(* SECTION: handling type variables *)

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

(* SECTION: handling types and effects *)

type variable = string
type eff = bool * bool

(* types *)

(** type [etype] is used to represent OCaml types that are present in Efftester *)
type etype =
  | Typevar of typevar
  | Unit
  | Int
  | Int32
  | Int64
  | NativeInt
  | Float
  | Bool
  | String
  | Option of etype
  | Ref of etype
  | Tuple of etype list
  | List of etype
  | Fun of etype * eff * etype

(** [ftv expr] returns free type variables in [expr] *)
let rec ftv = function
  | Typevar a -> [ a ]
  | Unit | Int | Int32 | Int64 | NativeInt | Float | Bool | String -> []
  | Option e -> ftv e
  | Ref t -> ftv t
  | Tuple t_lst -> List.map ftv t_lst |> List.concat (* duplicate elements allowed? *)
  | List et -> ftv et
  | Fun (a, _, r) -> ftv a @ ftv r
;;

(** checks if given type variable (represented as int) occurs in given type expression *)
let rec occurs tvar = function
  | Typevar a -> tvar = a
  | Option a -> occurs tvar a
  | Ref a -> occurs tvar a
  | Tuple t_lst -> List.exists (fun t -> occurs tvar t) t_lst
  | List a -> occurs tvar a
  | Fun (a, _, b) -> occurs tvar a || occurs tvar b
  | Unit | Int | Int32 | Int64 | NativeInt | Float | Bool | String -> false
;;

(** [arity fn_typ] determines arity of a function type [fn_typ] *)
let rec arity = function
  | Fun (_, _, b) -> 1 + arity b
  | _ -> 0
;;

(** [subst repl t] substitutes all type variables in [t] with mapping from type variables
    to types given in [repl] *)
let rec subst replacements t =
  match t with
  | Unit | Int | Int32 | Int64 | NativeInt | Float | Bool | String -> t
  | Typevar i -> (try List.assoc i replacements with Not_found -> t)
  | Option t' -> Option (subst replacements t')
  | Ref t' -> Ref (subst replacements t')
  | Tuple t_lst -> Tuple (List.map (fun t -> subst replacements t) t_lst)
  | List t' -> List (subst replacements t')
  | Fun (l, e, r) -> Fun (subst replacements l, e, subst replacements r)
;;

(* effects *)
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

let rec normalize_eff t =
  match t with
  | Typevar _ | Unit | Int | Int32 | Int64 | NativeInt | Float | Bool | String -> t
  | Option t' -> Option (normalize_eff t')
  | Ref t' -> Ref (normalize_eff t')
  | Tuple t_lst -> Tuple (List.map normalize_eff t_lst)
  | List t' -> List (normalize_eff t')
  | Fun (s, _, t) -> Fun (normalize_eff s, no_eff, normalize_eff t)
;;

(* SECTION: handle terms *)

(** type [lit] is used to represent literal values present in OCaml and available in Efftester *)
type lit =
  | LitUnit
  | LitInt of int
  | LitInt32 of int32
  | LitInt64 of int64
  | LitNativeInt of nativeint
  | LitFloat of float
  | LitBool of bool
  | LitStr of string

(* type [constr_descr] is used to differentiate between use of [Constructor] for tuples and variants *)
type constr_descr =
  | TupleArity of int
  | Variant of string

(* variant name *)

(** type [pattern] is used to represent patterns in OCaml *)
type pattern =
  | PattVar of etype * variable
  | PattConstr of etype * constr_descr * pattern list

(** type [term] is used to represent terms of OCaml available Efftester *)
type term =
  | Lit of lit
  | Variable of etype * variable
  | ListTrm of etype * term list * eff
  (* [Constructor (type, descr, payload_lst)] is used to construct ADT variants and tuples *)
  | Constructor of etype * constr_descr * term list * eff
  (* [PatternMatch typ matched_trm cases eff] *)
  | PatternMatch of etype * term * (pattern * term) list * eff
  | Lambda of etype * variable * etype * term
  (* [App (return_type, fn, arg_type, arg, eff)] *)
  | App of etype * term * etype * term * eff
  | Let of variable * etype * term * term * etype * eff
  | If of etype * term * term * term * eff

(* SECTION: handle typing and effect-bookkeeping of syntax constructs *)

let imm_type t =
  let lit_type l =
    match l with
    | LitUnit -> Unit
    | LitInt _ -> Int
    | LitInt32 _ -> Int32
    | LitInt64 _ -> Int64
    | LitNativeInt _ -> NativeInt
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

let imm_pat_type = function
  | PattVar (t, _) -> t
  | PattConstr (t, _, _) -> t
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

(* SECTION: helper functions to create terms *)

let tuple_arity = function
  | Constructor (_, TupleArity i, _, _) -> i
  | _ -> failwith "Effast.tuple_arity: tuple_arity is applied to a non-tuple"
;;

let some typ payload eff = Constructor (typ, Variant "Some", [ payload ], eff)
let none typ = Constructor (typ, Variant "None", [], no_eff)

module Ref = struct
  let ref_t =
    let new_tv = newtypevar () in
    Fun (Typevar new_tv, (true, false), Ref (Typevar new_tv))
  ;;

  let ref_f = Variable (ref_t, "ref")

  let deref_t =
    let new_tv = newtypevar () in
    Fun (Ref (Typevar new_tv), (true, false), Typevar new_tv)
  ;;

  let deref_f = Variable (deref_t, "(!)")

  let update_t =
    let new_tv = newtypevar () in
    Fun (Ref (Typevar new_tv), (false, false), Fun (Typevar new_tv, (true, false), Unit))
  ;;

  let update_f = Variable (update_t, "(:=)")
end
