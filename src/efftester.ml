(* *************************************************************** *)
(* OCaml compiler backend tester                                   *)
(* Initial version by Patrick Kasting and Mathias Nygaard Justesen *)
(* Type and effect extension by Jan Midtgaard                      *)
(* *************************************************************** *)

open QCheck

(** Helpers *)

let make_logger file_path =
  let file_out = open_out file_path in
  let counter = ref 0 in
  fun fmt ->
    incr counter;
    Printf.fprintf file_out ("(* %d *) " ^^ fmt ^^ ";;\n%!") !counter
;;

let no_logger = Printf.ifprintf stdout

let rec bprint_list ~sep elt_printer buf lst =
  match lst with
  | [] -> ()
  | [ elt ] -> elt_printer buf elt
  | elt :: rest ->
    Printf.bprintf
      buf
      "%a%a%a"
      elt_printer
      elt
      sep
      ()
      (bprint_list ~sep elt_printer)
      rest
;;

(* [list_elems shrink l yield] shrinks a list of elements [l] given a shrinker [shrink]
  TODO: use QCheck version of [list_elems] when @gasche's PR gets merged *)
let list_elems shrink l yield =
  (* try to shrink each element of the list *)
  let rec elem_loop rev_prefix suffix =
    match suffix with
    | [] -> ()
    | x :: xs ->
      shrink x (fun x' -> yield (List.rev_append rev_prefix (x' :: xs)));
      elem_loop (x :: rev_prefix) xs
  in
  elem_loop [] l
;;

(** Compilation *)

(* Write OCaml source to file *)
let write_prog src filename =
  let ostr = open_out filename in
  let () = output_string ostr src in
  close_out ostr
;;

let run srcfile compil_filename compil_comm =
  let exefile = "generated_tests/" ^ compil_filename in
  let exitcode = Sys.command (compil_comm ^ " " ^ srcfile ^ " -o " ^ exefile) in
  (* Check that compilation was successful *)
  if exitcode <> 0
  then
    failwith
      (compil_filename ^ " compilation failed with error code " ^ string_of_int exitcode)
  else (
    (* Run the compiled program *)
    let runcode = Sys.command ("./" ^ exefile ^ " >" ^ exefile ^ ".out 2>&1") in
    (runcode, exefile ^ ".out"))
;;

let is_native_byte_equiv (*printFunction*) src =
  (* Write OCaml source to file *)
  let file = "generated_tests/test.ml" in
  let () = write_prog src file in
  let ncode, nout = run file "native" "ocamlopt -O3 -w -5-26" in
  (* -w -5@20-26 *)
  (* Silence warnings for partial applications and unused variables *)
  let bcode, bout = run file "byte" "ocamlc -w -5-26" in
  let comp = Sys.command ("diff -q " ^ nout ^ " " ^ bout ^ " > /dev/null") in
  ncode = bcode && comp = 0
;;

(** AST type definitions  *)

type variable = string
type eff = bool * bool
type typevar = int

let resettypevar, newtypevar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      old )
;;

let resetvar, newvar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      "var" ^ string_of_int old )
;;

let reseteffvar, neweffvar =
  let count = ref 0 in
  ( (fun () -> count := 0),
    fun () ->
      let old = !count in
      incr count;
      "eff" ^ string_of_int old )
;;

(** {!etype} is used to represent OCaml types that are present in our generator *)
type etype =
  | Typevar of typevar
  | Unit
  | Int
  | Float
  | Bool
  | String
  | Option of etype
  | List of etype
  | Fun of etype * eff * etype

(* [ftv expr] returns free typevariables in {!expr} *)
let rec ftv = function
  | Typevar a -> [ a ]
  | Unit | Int | Float | Bool | String -> []
  | Option e -> ftv e
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

let some typ payload eff = Constructor (typ, "Some", [ payload ], eff)
let none typ = Constructor (typ, "None", [], (false, false))

(** Printing functions  *)

let rec type_to_ocaml ?(effannot = false) sb = function
  | Typevar a -> Printf.bprintf sb "'a%d" a
  | Unit -> Printf.bprintf sb "unit"
  | Int -> Printf.bprintf sb "int"
  | Float -> Printf.bprintf sb "float"
  | Bool -> Printf.bprintf sb "bool"
  | String -> Printf.bprintf sb "string"
  | Option e -> Printf.bprintf sb "(%a) option" (type_to_ocaml ~effannot) e
  | List s -> Printf.bprintf sb "(%a) list" (type_to_ocaml ~effannot) s
  | Fun (s, e, t) ->
    let print_simple_type sb s =
      match s with
      | Unit | Int | Float | Bool | String | Option _ | List _ | Typevar _ ->
        Printf.bprintf sb "%a" (type_to_ocaml ~effannot) s
      | Fun _ -> Printf.bprintf sb "(%a)" (type_to_ocaml ~effannot) s
    in
    let print_effannot sb = function
      | None -> ()
      | Some (ef, ev) -> Printf.bprintf sb "%B/%B" ef ev
    in
    let print_type sb t = Printf.bprintf sb "%a" (type_to_ocaml ~effannot) t in
    Printf.bprintf
      sb
      "%a -%a> %a"
      print_simple_type
      s
      print_effannot
      (if effannot then Some e else None)
      print_type
      t
;;

let type_to_str ?(effannot = false) typ =
  let sb = Buffer.create 20 in
  let () = type_to_ocaml ~effannot sb typ in
  Buffer.contents sb
;;

let eff_to_str ((ef, ev) : eff) = Printf.sprintf "(%B,%B)" ef ev

(* BNF grammar:

    exp ::= l
          | x
          | fun (x:t) -> exp
          | exp exp
          | let (x:t) = exp in exp
          | constr (exp, exp, ...)
          | begin match exp with pat -> arg | pat -> arg | ... end

   Same language but unambiguously formulated grammar:

    exp ::= app
          | fun (x:t) -> exp
          | let (x:t) = exp in exp
          | if exp then exp else exp
          | constr (exp, exp, ...)
          | begin match exp with pat -> arg | pat -> arg | ... end

    app ::= arg | app arg
    arg ::= l | x | (exp)

   The following prettyprinter is structured according to this grammar to cut down on
   the needless parentheses
*)
let rec term_to_ocaml ?(typeannot = true) term =
  let lit_to_ocaml_sb sb = function
    | LitUnit -> Printf.bprintf sb "()"
    | LitInt i -> if i < 0 then Printf.bprintf sb "(%d)" i else Printf.bprintf sb "%d" i
    | LitFloat f ->
      if f <= 0. then Printf.bprintf sb "(%F)" f else Printf.bprintf sb "%F" f
    (* We want parentheses when f equals (-0.);
        Without parentheses -0. is interpreted as an arithmetic operation function. *)
    | LitBool b -> Printf.bprintf sb "%B" b
    | LitStr s -> Printf.bprintf sb "%S" s
  in
  let rec exp sb t =
    let type_to_ocaml_noannot = type_to_ocaml ~effannot:false in
    let print_binder sb (x, t) =
      if typeannot
      then Printf.bprintf sb "(%s: %a)" x type_to_ocaml_noannot t
      else Printf.bprintf sb "%s" x
    in
    match t with
    | Constructor (_, name, payload_lst, _) ->
      (match payload_lst with
      | [] -> Printf.bprintf sb "%s" name
      | trms ->
        let sep sb () = Printf.bprintf sb ", " in
        Printf.bprintf sb "(%s (%a))" name (bprint_list ~sep exp) trms)
    | PatternMatch (_, match_trm, branches, _) ->
      let case_to_str sb (pattern, body) =
        Printf.bprintf sb "| %a -> %a" pattern_to_ocaml pattern exp body
      in
      Printf.bprintf
        sb
        "(match %a with %a)"
        exp
        match_trm
        (fun sb branches -> List.iter (case_to_str sb) branches)
        branches
    | Lambda (_, x, t, m) -> Printf.bprintf sb "(fun %a -> %a)" print_binder (x, t) exp m
    | Let (x, t, m, n, _, _) ->
      Printf.bprintf sb "let %a = %a in %a" print_binder (x, t) exp m exp n
    | If (_, b, m, n, _) -> Printf.bprintf sb "if %a then %a else %a" exp b exp m exp n
    | Lit _ | Variable _ | ListTrm _ | App _ -> app sb t
  and app sb t =
    match t with
    | App (_, m, _, n, _) -> Printf.bprintf sb "%a %a" app m arg n
    | _ -> arg sb t
  and arg sb t =
    match t with
    | Lit l -> lit_to_ocaml_sb sb l
    | Variable (_, s) -> Printf.bprintf sb "%s" s
    | ListTrm (_, ls, _) ->
      let print_lst sb ls = List.iter (fun elt -> Printf.bprintf sb "%a; " app elt) ls in
      Printf.bprintf sb "[%a]" print_lst ls
    | _ -> Printf.bprintf sb "(%a)" exp t
  in
  let sb = Buffer.create 80 in
  let () = exp sb term in
  Buffer.contents sb

and pattern_to_ocaml sb patt =
  let print_patt_list sb patt_lst =
    match patt_lst with
    | [] -> ()
    | [ patt ] -> Printf.bprintf sb " %a" pattern_to_ocaml patt
    | _patt_lst ->
      let sep sb () = Printf.bprintf sb ", " in
      Printf.bprintf sb " (%a)" (bprint_list ~sep pattern_to_ocaml) patt_lst
  in
  match patt with
  | PattVar v -> Printf.bprintf sb "%s" v
  | PattConstr (_typ, name, patt_lst) ->
    Printf.bprintf sb "%s%a" name print_patt_list patt_lst
;;

(** Effect system function *)

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

let rec occurs tvar = function
  | Typevar a -> tvar = a
  | Option a -> occurs tvar a
  | List a -> occurs tvar a
  | Fun (a, _, b) -> occurs tvar a || occurs tvar b
  | Unit | Int | Float | Bool | String -> false
;;

(** [arity f_typ] determines arity of a function type {!f_typ} *)
let rec arity = function
  | Fun (_, _, b) -> 1 + arity b
  | _ -> 0
;;

let rec subst repl t =
  match t with
  | Unit | Int | Float | Bool | String -> t
  | Typevar a -> (try List.assoc a repl with Not_found -> t)
  | Option e -> Option (subst repl e)
  | List u -> List (subst repl u)
  | Fun (l, e, r) -> Fun (subst repl l, e, subst repl r)
;;

type unify_solution =
  | No_sol
  | Sol of (typevar * etype) list

exception No_solution

let rec unify_list = function
  | [] -> []
  | (l, r) :: rest ->
    let sub = unify_list rest in
    (match (subst sub l, subst sub r) with
    | Unit, Unit -> sub
    | Int, Int -> sub
    | Float, Float -> sub
    | Bool, Bool -> sub
    | String, String -> sub
    | Option a, Option b -> unify_list [ (a, b) ] @ sub
    | Typevar a, Typevar b -> if a = b then sub else (a, r) :: sub
    | List a, List b ->
      let sub' = unify_list [ (a, b) ] in
      sub' @ sub
    | Fun (a, _, b), Fun (c, _, d) ->
      let sub' = unify_list [ (a, c); (b, d) ] in
      sub' @ sub
    | Typevar a, _ -> if occurs a r then raise No_solution else (a, r) :: sub
    | _, Typevar a -> if occurs a l then raise No_solution else (a, l) :: sub
    | Unit, _
    | Int, _
    | Float, _
    | Bool, _
    | String, _
    | Option _, _
    | List _, _
    | Fun _, _ ->
      raise No_solution)
;;

let unify r t = try Sol (unify_list [ (r, t) ]) with No_solution -> No_sol

(* determines whether the first arg is a generalization of the second *)
(* or framed differently: whether the second is a particular instance of the first *)
let rec types_compat t t' =
  match (t, t') with
  | Unit, Unit -> true
  | Unit, _ -> false
  | Int, Int -> true
  | Int, _ -> false
  | Float, Float -> true
  | Float, _ -> false
  | Bool, Bool -> true
  | Bool, _ -> false
  | String, String -> true
  | String, _ -> false
  | Option a, Option b -> types_compat a b
  | Option _, _ -> false
  | Fun (at, e, rt), Fun (at', e', rt') ->
    types_compat at' at && types_compat rt rt' && eff_leq e e'
  | Fun _, _ -> false
  | List et, List et' -> types_compat et et'
  | List _, _ -> false
  | Typevar _, _ ->
    (match unify t t' with
    | No_sol -> false
    | Sol _ -> true)
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

(** Environment type definitions and functions *)

module TypeSet = Set.Make (struct
  type t = etype

  let compare = Pervasives.compare
end)

module VarSet = Set.Make (struct
  type t = variable

  let compare = String.compare
end)

module VarMap = Map.Make (struct
  type t = variable

  let compare = String.compare
end)

module TypeMap = Map.Make (struct
  type t = etype

  let compare = Pervasives.compare
end)

let rec normalize_eff t =
  match t with
  | Typevar _ | Unit | Int | Float | Bool | String -> t
  | Option t' ->
    let t'' = normalize_eff t' in
    Option t''
  | List t' ->
    let t'' = normalize_eff t' in
    List t''
  | Fun (s, _, t) -> Fun (normalize_eff s, no_eff, normalize_eff t)
;;

let add_multi_map key value map =
  (* assume key has been normalized *)
  match TypeMap.find key map with
  | exception Not_found -> TypeMap.add key (VarSet.singleton value) map
  | s ->
    let new_set = VarSet.add value s in
    TypeMap.add key new_set map
;;

let remove_multi_map key value map =
  (* assume key has been normalized *)
  let old_key_set = TypeMap.find key map in
  let fixed_old_type_set = VarSet.remove value old_key_set in
  if VarSet.is_empty fixed_old_type_set
  then TypeMap.remove key map
  else TypeMap.add key fixed_old_type_set map
;;

(** maps a variable to its type *)
type type_env = etype VarMap.t

(** maps a type to a set of variables with that type *)
type binding_env = VarSet.t TypeMap.t

(** Includes three elements:
  env (Gamma) : maps variables to types
  rev_env : maps types to sets of variables
  ret_env : maps return types to sets of variables
*)
type tridir_env = type_env * binding_env * binding_env

let rec get_return_types = function
  | Fun (s, e, t) -> Fun (s, e, t) :: get_return_types t
  | t -> [ t ]
;;

(* special entry Typevar (-1) holds all vars with polymorphic return type *)
let polyentry = Typevar (-1)

let add_var var new_type (env, rev_env, ret_env) =
  let env' = VarMap.add var new_type env in
  (* Overrides existing entry *)
  let norm_new_type = normalize_eff new_type in
  let old_type = try Some (VarMap.find var env) with Not_found -> None in
  let rev_env' =
    let fixed_rev_env =
      match old_type with
      | Some old_type -> remove_multi_map (normalize_eff old_type) var rev_env
      | None -> rev_env
    in
    add_multi_map norm_new_type var fixed_rev_env
  in
  let ret_env' =
    let rts = get_return_types norm_new_type in
    let fixed_ret_env =
      match old_type with
      | None -> ret_env
      | Some s ->
        List.fold_left
          (fun r_env rt ->
            if ftv rt = []
               (* return type polymorphic? Then syntactic comp. will not find it *)
            then remove_multi_map rt var r_env
            else remove_multi_map polyentry var r_env)
          ret_env
          (get_return_types (normalize_eff s))
    in
    List.fold_left
      (fun r_env rt ->
        if ftv rt = []
           (* return type polymorphic? Then syntactic comp. will not find it *)
        then add_multi_map rt var r_env
        else add_multi_map polyentry var r_env)
      fixed_ret_env
      rts
  in
  (env', rev_env', ret_env')
;;

let lookup_var x (env, _, _) = try Some (VarMap.find x env) with Not_found -> None

let lookup_type s (_, rev_env, _) =
  try TypeMap.find s rev_env with Not_found -> VarSet.empty
;;

let lookup_return s (env, _, ret_env) =
  let concrete_set = try TypeMap.find s ret_env with Not_found -> VarSet.empty in
  let arity_s = arity s in
  let rec has_compat_rt t =
    (arity t = arity_s && types_compat t s)
    ||
    match t with
    | Fun (_, _, rt) -> has_compat_rt rt
    | _ -> false
  in
  let poly_set =
    VarSet.fold
      (fun x acc -> if has_compat_rt (VarMap.find x env) then VarSet.add x acc else acc)
      (try TypeMap.find polyentry ret_env with Not_found -> VarSet.empty)
      VarSet.empty
  in
  VarSet.union concrete_set poly_set
;;

(** Initial environment *)

let init_tri_env =
  List.fold_left
    (fun acc (var, t) -> add_var var t acc)
    (VarMap.empty, TypeMap.empty, TypeMap.empty)
    [ (* These follow the order and specification of the Pervasives module
         	  https://caml.inria.fr/pub/docs/manual-ocaml/libref/Pervasives.html *)
      (* Comparisons *)
      ( "(=)",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Bool)) );
      ( "(<>)",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Bool)) );
      ("(<)", Fun (Int, no_eff, Fun (Int, (true, false), Bool)));
      ("(>)", Fun (Int, no_eff, Fun (Int, (true, false), Bool)));
      (*
        ("(<=)", let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), Bool)));
        ("(>=)",
        let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), Bool)));
      *)
      ( "compare",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Fun (a, (true, false), Int)) );
      (*
        ("min", let a = Typevar (newtypevar()) in
        Fun (a, no_eff, Fun (a, (true,false), a)));
        ("max",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), a)));
        ("(==)",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), Bool)));
        ("(!=)",
          let a = Typevar (newtypevar()) in
          Fun (a, no_eff, Fun (a, (true,false), Bool)));
      *)
      (* Boolean operations *)
      ("not", Fun (Bool, no_eff, Bool));
      ("(&&)", Fun (Bool, no_eff, Fun (Bool, no_eff, Bool)));
      ("(||)", Fun (Bool, no_eff, Fun (Bool, no_eff, Bool)));
      (* Integer arithmetic *)
      (*
        ("(~-)", Fun (Int, no_eff, Int));
        ("(~+)", Fun (Int, no_eff, Int));
      *)
      ("succ", Fun (Int, no_eff, Int));
      ("pred", Fun (Int, no_eff, Int));
      ("(+)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(-)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("( * )", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(/)", Fun (Int, no_eff, Fun (Int, (true, false), Int)));
      ("(mod)", Fun (Int, no_eff, Fun (Int, (true, false), Int)));
      ("abs", Fun (Int, no_eff, Int));
      (*
        ("max_int", Int);
        ("min_int",        Int);
      *)
      (* Bitwise operations *)
      ("(land)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lor)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lxor)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("lnot", Fun (Int, no_eff, Int));
      ("(lsl)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(lsr)", Fun (Int, no_eff, Fun (Int, no_eff, Int)));
      ("(asr)", Fun (Int, no_eff, Fun (Int, no_eff, Int)))
      (* Floating-point arithmetic *)
      (*
        ("(~-.)",          Fun (Float, no_eff, Float));
        ("(~+.)",          Fun (Float, no_eff, Float));
      *);
      ("(+.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(-.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("( *. )", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(/.)", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("( ** )", Fun (Float, no_eff, Fun (Float, no_eff, Float)));
      ("(sqrt)", Fun (Float, no_eff, Float));
      ("(exp)", Fun (Float, no_eff, Float));
      (* TODO: add other floating-point operations? *)
      (* String operations *)
      ("(^)", Fun (String, no_eff, Fun (String, no_eff, String)));
      (* Character operations *)
      (* Unit operations *)
      ( "ignore",
        let a = Typevar (newtypevar ()) in
        Fun (a, no_eff, Unit) );
      (* String conversion functions *)
      ("string_of_bool", Fun (Bool, no_eff, String));
      ("bool_of_string", Fun (String, (true, false), Bool));
      ("string_of_int", Fun (Int, no_eff, String));
      ("int_of_string", Fun (String, (true, false), Int));
      ("string_of_float", Fun (Float, no_eff, String));
      ("float_of_string", Fun (String, (true, false), Float));
      (* Pair operations *)
      (* List operations *)
      ( "(@)",
        let a = Typevar (newtypevar ()) in
        Fun (List a, no_eff, Fun (List a, no_eff, List a)) );
      (* Input/output *)
      (* Output functions on standard output *)
      ("print_string", Fun (String, (true, false), Unit));
      ("print_int", Fun (Int, (true, false), Unit));
      ("print_float", Fun (Float, (true, false), Unit));
      ("print_endline", Fun (String, (true, false), Unit));
      ("print_newline", Fun (Unit, (true, false), Unit));
      (* Output functions on standard error *)
      (*
        ("prerr_string",   Fun (String, (true,false), Unit));
        ("prerr_int",      Fun (Int, (true,false), Unit));
        ("prerr_endline",  Fun (String, (true,false), Unit));
        ("prerr_newline",  Fun (Unit, (true,false), Unit));
      *)
      (* Input functions on standard input *)
      (* General output functions *)
      (* General input functions *)
      (* Operations on large files *)
      (* References *)
      (* Result type *)
      (* Operations on format strings *)
      (* Program termination *)
      ( "exit",
        let a = Typevar (newtypevar ()) in
        Fun (Int, (true, false), a) );
      (*
        ("at_exit",        Fun (Fun (Unit, (true,false), Unit), (true,false), Unit));
      *)
      (* More list operations from List module *)
      ( "List.hd",
        let a = Typevar (newtypevar ()) in
        Fun (List a, (true, false), a) );
      ( "List.tl",
        let a = Typevar (newtypevar ()) in
        Fun (List a, (true, false), List a) )
      (*
        ("List.concat",    let a = Typevar (newtypevar()) in
        Fun (List (List a), no_eff, List a));
      *)
    ]
;;

(** Generators *)

(* Provides operations over a local cache that is used by a generator  *)
let new_cache () =
  let cache = ref [] in
  let to_cache fl = cache := fl :: !cache in
  let get_cache_lst () = !cache in
  let clear_cache () = cache := [] in
  (to_cache, get_cache_lst, clear_cache)
;;

module StaticGenerators = struct
  let alpha_gen =
    let a_code = int_of_char 'a' in
    let z_code = int_of_char 'z' in
    Gen.map char_of_int (Gen.int_range a_code z_code)
  ;;

  let var_gen = Gen.map (String.make 1) alpha_gen
  let string_gen = Gen.small_string ~gen:alpha_gen
  let str_to_str = Printf.sprintf "%S"
  let sqrt i = int_of_float (Pervasives.sqrt (float_of_int i))

  let int_gen =
    Gen.(
      frequency [ (10, small_int); (5, int); (1, oneofl [ min_int; -1; 0; 1; max_int ]) ])
  ;;

  let float_gen =
    Gen.frequency
      [ (5, Gen.float);
        ( 5,
          Gen.oneofl
            [ Float.nan;
              Float.neg_infinity;
              min_float;
              -1.;
              -0.;
              0.;
              Float.epsilon;
              1.;
              max_float;
              Float.infinity
            ] )
      ]
  ;;

  (* Generate a possibly repeated floating-point number *)
  let float_gen_with_rep_thunk () =
    let to_cache, get_cache_lst, _ = new_cache () in
    let from_cache_gen rs = (Gen.oneofl @@ get_cache_lst ()) rs in
    fun rs ->
      match get_cache_lst () with
      | [] ->
        Gen.map
          (fun fl ->
            to_cache fl;
            fl)
          float_gen
          rs
      | _xs ->
        Gen.map
          (fun fl ->
            if List.mem fl (get_cache_lst ())
            then fl
            else (
              to_cache fl;
              fl))
          (Gen.frequency [ (2, float_gen); (8, from_cache_gen) ])
          rs
  ;;

  (* TODO: Include more base types - requires also changing `printer_by_etype` *)
  let basetype_gen = Gen.oneofl [ Int; Float; String ]
  let eff_gen = Gen.oneofl [ (false, false); (true, false) ]

  let type_gen =
    (* Generates ground types (sans type variables) *)
    Gen.fix (fun recgen n ->
        let base_types = [ Unit; Int; Float; Bool; String ] in
        if n = 0
        then Gen.oneofl base_types
        else
          Gen.frequency
            [ (* Generate no alphas *)
              (4, Gen.oneofl base_types);
              (1, Gen.map (fun t -> List t) (recgen (n / 2)));
              ( 1,
                Gen.map3
                  (fun t e t' -> Fun (t, e, t'))
                  (recgen (n / 2))
                  eff_gen
                  (recgen (n / 2)) )
            ])
  ;;
end

(** {!Context} is used to store the state of generator for the program that is being
  generated *)
module type Context = sig
  (** stateful float generator with value repetitions *)
  val float_gen_with_rep : float Gen.t
end

module FreshContext () : Context = struct
  let float_gen_with_rep = StaticGenerators.float_gen_with_rep_thunk ()
end

module GeneratorsWithContext (Ctx : Context) = struct
  open StaticGenerators

  (* Type-directed literal generator *)
  let literal_gen t _eff _size =
    match t with
    | Unit -> Gen.return LitUnit
    | Int -> Gen.map (fun i -> LitInt i) int_gen
    | Float -> Gen.map (fun f -> LitFloat f) float_gen
    | Bool -> Gen.map (fun b -> LitBool b) Gen.bool
    | String -> Gen.map (fun s -> LitStr s) string_gen
    | Option _ -> failwith "literal_gen: option arg. should not happen"
    | List _ -> failwith "literal_gen: list arg. should not happen"
    | Typevar _ -> failwith "literal_gen: typevar arg. should not happen"
    | Fun _ -> failwith "literal_gen: funtype arg. should not happen"
  ;;

  (* Sized generator of variables according to the LIT rule
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

   --------------------- (LIT)
       env |- l : s
*)
  let lit_rules _env s eff size =
    let rec list_of_fun = function
      | List s -> list_of_fun s
      | Fun _ -> true
      | _ -> false
    in
    match s with
    | List s when list_of_fun s -> []
    | Unit | Int | Float | Bool | String ->
      [ (6, Gen.map (fun l -> Some (Lit l)) (literal_gen s eff size)) ]
    | List _ | Option _ | Fun _ | Typevar _ -> []
  ;;

  (* Sized generator of variables according to the VAR rule
   @param env  : surrounding environment
   @param s    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

      (t:s) \in env
   --------------------- (VAR)
       env |- t : s
*)
  let var_rules env s _eff _size =
    (* vars have no immediate effect, so 'eff' param is ignored *)
    let candvars = VarSet.elements (lookup_type (normalize_eff s) env) in
    let arity_s = arity s in
    let candvars' =
      List.filter
        (fun x ->
          match lookup_var x env with
          | Some t -> arity t = arity_s && types_compat t s
          | None ->
            failwith ("var_rules: found variable " ^ x ^ " without associated type"))
        candvars
    in
    List.map (fun var -> (1, Gen.return (Some (Variable (s, var))))) candvars'
  ;;

  (* Sized generator of lambda terms according to the LAM rule
   @param env  : surrounding environment
   @param u    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

               (x:s), env |- m : t
    -------------------------------------------- (LAM)
       env |- (fun (x:s) -> m) : s -> t
*)
  let rec lam_rules env u _eff size =
    (* lams have no immediate effect, so 'eff' param is ignored *)
    let gen s eff t =
      Gen.(
        var_gen >>= fun x ->
        term_gen_sized (add_var x s env) t eff (size / 2) >>= function
        | None -> return None
        | Some m ->
          let myeff = imm_eff m in
          return (Some (Lambda (Fun (s, myeff, imm_type m), x, s, m))))
    in
    match u with
    | Unit | Int | Float | Bool | String | Option _ | List _ | Typevar _ -> []
    | Fun (s, e, t) -> [ (8, gen s e t) ]

  (* Sized generator of applications (calls) according to the APP rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- f : s -> t     env |- x : s
    ---------------------------------------- (APP)
                 env |- f x : t
*)
  and app_rules env t eff size =
    let open Gen in
    let from_type funeff argeff s =
      term_gen_sized env (Fun (s, eff, t)) funeff (size / 2) >>= function
      | None -> Gen.return None
      | Some f ->
        term_gen_sized env s argeff (size / 2) >>= function
        | None -> Gen.return None
        | Some x ->
          (match imm_type f with
          | Fun (_, e, frange) ->
            let funeff = imm_eff f in
            let argeff = imm_eff x in
            let ef, ev = eff_join e (eff_join funeff argeff) in
            let eff' = (ef, ev || (fst funeff && fst argeff)) in
            if eff_leq eff' eff
            then Gen.return (Some (App (frange, f, imm_type x, x, eff')))
            else
              (*Gen.return None*)
              failwith "app_rules generated application with too big effect"
          | _ ->
            failwith
              ("app_rules generated application with non-function  "
              ^ " t is "
              ^ type_to_str ~effannot:true t
              ^ " f is "
              ^ term_to_ocaml ~typeannot:false f
              ^ " imm_type f is "
              ^ type_to_str ~effannot:true (imm_type f)))
    in
    (* May generate eff in either operator or operand *)
    [ (4, type_gen (size / 2) >>= from_type eff no_eff);
      (4, type_gen (size / 2) >>= from_type no_eff eff)
    ]

  (* Sized generator of multi-argument applications (calls) according to the INDIR rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

     (f : rho1 -> ... -> rhon -> t) in env     env |- m1 : rho1  ...  env |- mn : rhon
   ------------------------------------------------------------------------------------- (INDIR)
                                  env |- f m1 ... mn : t
*)
  and indir_rules env t eff size =
    let mgu s t =
      let rec loop = function
        | [] -> None
        | r :: rs ->
          (match unify r t with
          | Sol u -> Some u
          | No_sol -> loop rs)
      in
      loop (get_return_types s)
    in
    let rec get_arg_types s t =
      match s with
      | s when types_compat s t -> []
      | Fun (s', _, t') -> s' :: get_arg_types t' t
      | s ->
        failwith
          ("get_arg_types: should not happen  s is "
          ^ type_to_str ~effannot:true s
          ^ " t is "
          ^ type_to_str ~effannot:true t)
    in
    (* returns the index of the first effect - or else the number of arguments *)
    let rec first_eff = function
      | s when types_compat s t || types_compat t s -> 0
      | Fun (_, e, t) -> if e = no_eff then 1 + first_eff t else 1
      | s -> failwith ("first_eff: should not happen  " ^ type_to_str ~effannot:true s)
    in
    (* recursively build application term argument by argument *)
    let rec apply term r_type n effacc = function
      | [] -> Gen.return (Some term)
      | arg :: args ->
        (* arg 'n' may have effect 'eff' *)
        let myeff = if n = 0 then eff else no_eff in
        Gen.( >>= )
          (term_gen_sized env arg myeff (size / 2))
          (function
            | None -> Gen.return None
            | Some a ->
              (match r_type with
              | Fun (_, funeff, new_rtype) ->
                let my_actual_eff = eff_join funeff (imm_eff a) in
                (* actual effect *)
                let effacc' = eff_join my_actual_eff effacc in
                if eff_leq effacc' eff
                then
                  apply
                    (App (new_rtype, term, imm_type a, a, effacc'))
                    new_rtype
                    (n - 1)
                    effacc'
                    args
                else
                  failwith
                    "apply: overly effectful program generated. This should not happen."
              | _ ->
                failwith
                  "apply: non-function type expecting argument. This should not happen")
            )
    in
    let application s f =
      (* s is the unnormalized, effect-full type *)
      let f_term = Variable (s, f) in
      match mgu s t with
      | None ->
        failwith
          ("indir_rules, application: the return types of chosen variable "
          ^ f
          ^ ":"
          ^ type_to_str ~effannot:true s
          ^ " do not match goal type "
          ^ type_to_str ~effannot:true t)
      | Some sub ->
        (* goal type and candidate unify with some subst *)
        let goal_type = subst sub s in
        (* goal type may have free variables, which we need to inst. *)
        let ftvs = ftv goal_type in
        let rec build_subst vs =
          match vs with
          | [] -> Gen.return []
          | v :: vs ->
            Gen.map2 (fun sub t -> (v, t) :: sub) (build_subst vs) (type_gen (sqrt size))
        in
        Gen.( >>= ) (build_subst ftvs) (fun sub' ->
            let goal_type = subst sub' goal_type in
            let arg_types =
              try get_arg_types goal_type (subst sub t)
              with Failure exc ->
                print_endline ("s is " ^ type_to_str ~effannot:true s);
                print_endline
                  ("sub is "
                  ^ Print.list
                      (Print.pair
                         (fun id -> "'a" ^ string_of_int id)
                         (type_to_str ~effannot:true))
                      sub);
                print_endline
                  ("(subst sub s) is " ^ type_to_str ~effannot:true (subst sub s));
                print_endline ("t is " ^ type_to_str ~effannot:true t);
                failwith exc
            in
            let first_eff_index = first_eff goal_type in
            Gen.(
              (if first_eff_index = 0 then return 0 else int_bound (first_eff_index - 1))
              >>= fun n -> apply f_term goal_type n no_eff arg_types))
    in
    let normalized_t = normalize_eff t in
    let suitable_vars = lookup_return normalized_t env in
    (* this returns a set of cand. sans effects *)
    let f_type_map =
      let rec acc_rt_and_effect eff ty =
        (* check that all effects are leq eff and that rt is compat *)
        (if types_compat (normalize_eff ty) normalized_t
            (* (sans effects) types agree here *)
        then types_compat ty t
        else true)
        &&
        match ty with
        | Fun (_, e, ty') -> eff_leq e eff && acc_rt_and_effect eff ty'
        | _ -> true
      in
      (* there may be several variables with the same type *)
      VarSet.fold
        (fun f acc ->
          match lookup_var f env with
          | Some ty ->
            (match mgu ty t with
            (* some rt of receiver (sans effects) matches here *)
            | None ->
              failwith "f_type_pairs: couldn't find a subst, which should not happen"
            | Some sub ->
              let ty' = subst sub ty in
              (* receiver may have poly type, which is too effectful when inst *)
              if acc_rt_and_effect eff ty' then add_multi_map ty f acc else acc)
          | None -> failwith "f_type_pairs: lookup_var failed, which should not happen")
        suitable_vars
        TypeMap.empty
    in
    TypeMap.fold
      (fun s fs acc ->
        (4, Gen.( >>= ) (Gen.oneofl (VarSet.elements fs)) (application s)) :: acc)
      f_type_map
      []

  (* Sized generator of let according to the LET rule
   @param env  : surrounding environment
   @param t    : desired goal type
   @param eff  : desired effect
   @param size : size parameter

       env |- m : s     env, (x:s) |- n : t
    ------------------------------------------ (LET)
           env |- let x:s = m in n : t
*)
  and let_rules env t eff size =
    let open Gen in
    let from_type s =
      var_gen >>= fun x ->
      term_gen_sized env s eff (size / 2) >>= function
      | None -> return None
      | Some m ->
        term_gen_sized (add_var x s env) t eff (size / 2) >>= function
        | None -> return None
        | Some n ->
          let myeff = eff_join (imm_eff m) (imm_eff n) in
          return (Some (Let (x, s, m, n, imm_type n, myeff)))
    in
    [ (6, type_gen (size / 2) >>= from_type) ]

  and if_rules env t eff size =
    let open Gen in
    let gen =
      (* predicate is generated *)
      term_gen_sized env Bool eff (size / 3) >>= function
      | None -> return None
      | Some b ->
        (* then branch is generated *)
        term_gen_sized env t eff (size / 3) >>= function
        | None -> return None
        | Some m ->
          let then_type = imm_type m in
          (match unify then_type t with
          | No_sol ->
            failwith
              ("if_rules: generated type "
              ^ type_to_str ~effannot:true then_type
              ^ " in then branch does not unify with goal type "
              ^ type_to_str ~effannot:true t)
          | Sol sub ->
            let subst_t = subst sub t in
            (* else branch is generated *)
            term_gen_sized env subst_t eff (size / 3) >>= function
            | None -> return None
            | Some n ->
              let else_type = imm_type n in
              (match unify else_type subst_t with
              | No_sol ->
                failwith
                  ("if_rules: generated else branch type "
                  ^ type_to_str ~effannot:true else_type
                  ^ " does not unify with subst goal type "
                  ^ type_to_str ~effannot:true subst_t)
              | Sol sub' ->
                let mytype = subst sub' subst_t in
                let myeff = eff_join (imm_eff b) (eff_join (imm_eff m) (imm_eff n)) in
                return (Some (If (mytype, b, m, n, myeff)))))
    in
    [ (3, gen) ]

  and option_intro_rules env t eff size =
    let gen =
      let open Gen in
      match t with
      | Option t' ->
        Gen.frequencyl [ (2, "Some"); (1, "None") ] >>= fun name ->
        (match name with
        | "None" -> return (Some (none t))
        | "Some" ->
          term_gen_sized env t' eff (size - 1) >>= fun trm ->
          (match trm with
          | None -> return None
          | Some trm' -> return (Some (some t trm' eff)))
        | _ -> failwith "option_intro_rules: impossible option adt_constr name")
      | _ -> return None
    in
    [ (3, gen) ]

  and option_elim_rules env t eff size =
    let gen =
      let open Gen in
      StaticGenerators.basetype_gen >>= fun bt ->
      term_gen_sized env (Option bt) eff (size / 3) >>= function
      | None -> return None
      | Some match_trm ->
        var_gen >>= fun var_name ->
        let extended_env = add_var var_name bt env in
        term_gen_sized extended_env t eff (size / 3) >>= function
        | None -> return None
        | Some some_branch_trm ->
          term_gen_sized env t eff (size / 3) >>= function
          | None -> return None
          | Some none_branch_trm ->
            return
            @@ Some
                 (PatternMatch
                    ( t,
                      match_trm,
                      [ (PattConstr (bt, "Some", [ PattVar var_name ]), some_branch_trm);
                        (PattConstr (bt, "None", []), none_branch_trm)
                      ],
                      eff ))
    in
    [ (3, gen) ]

  and list_intro_rules env goal_typ eff size : (int * term option Gen.t) list =
    let open Gen in
    match goal_typ with
    | List elt_typ ->
      let gen =
        match elt_typ with
        | Typevar _ -> return @@ Some (ListTrm (goal_typ, [], no_eff))
        | _ ->
          if size = 0
          then return @@ Some (ListTrm (goal_typ, [], no_eff))
          else
            int_bound (sqrt size) >>= fun lst_size ->
            let lst_size = if lst_size = 0 then 1 else lst_size in
            Gen.list_size
              (return lst_size)
              (term_gen_sized env elt_typ eff (size / (lst_size * 10)))
            >>= fun opt_lst ->
            let lst =
              List.fold_left
                (fun acc_lst elt ->
                  match elt with
                  | Some x -> x :: acc_lst
                  | None -> acc_lst)
                []
                opt_lst
            in
            return @@ Some (ListTrm (goal_typ, lst, eff))
      in
      [ (3, gen) ]
    | _ -> []

  (* [gen_term_from_rules env goal size rules] returns a constant generator with a term
     wrapped in an option, in which the term was generated using a randomly picked
     generator from the {!rules} list

     Generators are picked according to their weights.
  *)
  and gen_term_from_rules _env _goal _size rules =
    let int_below_gen bound st = Random.State.int st bound in
    let weights_sum = List.fold_left (fun acc (w, _g) -> acc + w) 0 rules in
    (* we reimplement QCheck.Gen.frequency because we want it to also return the weight of
       the picked element (to update weights sum) and the list without that element *)
    let gen_freq lst rand_k =
      let rec pick lst (acc_lst, acc_sum) =
        match lst with
        | [] -> failwith "gen_term_from_rules: gen_freq: too large rand_k"
        | ((w, _g) as curr) :: rest ->
          if rand_k < acc_sum + w
          then (curr, List.rev_append acc_lst rest)
          else pick rest (curr :: acc_lst, acc_sum + w)
      in
      pick lst ([], 0)
    in
    let rec pick_all rules w_sum : term option Gen.t =
      match rules with
      | [] -> Gen.return None
      | rls ->
        let open Gen in
        int_below_gen w_sum >|= gen_freq rls >>= fun ((w, g), new_rls) ->
        g >>= function
        | Some _ as t_opt -> Gen.return t_opt
        | None -> pick_all new_rls (w_sum - w)
    in
    pick_all rules weights_sum

  and term_gen_sized env goal eff size =
    if size = 0
    then (
      let rules =
        List.concat [ lit_rules env goal eff size; var_rules env goal eff size ]
      in
      gen_term_from_rules env goal size rules)
    else (
      let rules =
        List.concat
          [ lit_rules env goal eff size;
            option_intro_rules env goal eff size;
            option_elim_rules env goal eff size;
            list_intro_rules env goal eff size;
            (*var_rules env goal eff size;*)
            (* var rule is covered by indir with no args *)
            app_rules env goal eff size;
            lam_rules env goal eff size;
            indir_rules env goal eff size;
            let_rules env goal eff size;
            if_rules env goal eff size
          ]
      in
      gen_term_from_rules env goal size rules)
  ;;

  let list_permute_term_gen_rec_wrapper env goal eff =
    Gen.sized (term_gen_sized env goal eff)
  ;;

  let term_gen = list_permute_term_gen_rec_wrapper init_tri_env

  let dep_term_gen =
    Gen.(
      basetype_gen >>= fun typ ->
      term_gen typ (true, false) >>= fun trm_opt ->
      match trm_opt with
      | None -> return None
      | Some trm -> return (Some (typ, trm)))
  ;;
end

(** Shrinker and actual testing *)

module Shrinker = struct
  let create_lit t =
    let to_term s = Some (Lit s) in
    match t with
    | Unit -> to_term LitUnit
    | Int -> to_term (LitInt (Gen.generate1 small_int.gen))
    | Float -> to_term (LitFloat (Gen.generate1 float.gen))
    | Bool -> to_term (LitBool (Gen.generate1 bool.gen))
    | String -> to_term (LitStr (Gen.generate1 StaticGenerators.string_gen))
    | Option _ | List _ | Fun _ | Typevar _ -> None
  ;;

  let rec occurs_in_pat var pat =
    match pat with
    | PattVar x -> x = var
    | PattConstr (_, _, lst) -> List.exists (fun pt -> occurs_in_pat var pt) lst
  ;;

  (* determines whether x occurs free (outside a binding) in the arg. exp *)
  let rec fv x trm =
    let has_fv lst = List.exists (fun trm -> fv x trm) lst in
    match trm with
    | Lit _ -> false
    | Variable (_, y) -> x = y
    | ListTrm (_, lst, _) -> has_fv lst
    | Constructor (_typ, _name, args, _eff) -> has_fv args
    | PatternMatch (_typ, match_trm, cases, _eff) ->
      let fv_in_case (pat, trm) = if occurs_in_pat x pat then false else fv x trm in
      fv x match_trm || List.exists fv_in_case cases
    | Lambda (_, y, _, m) -> if x = y then false else fv x m
    | App (_, m, _, n, _) -> fv x m || fv x n
    | Let (y, _, m, n, _, _) -> fv x m || if x = y then false else fv x n
    | If (_, b, m, n, _) -> fv x b || fv x m || fv x n
  ;;

  (* renames free occurrences of 'x' into 'y' *)
  let rec alpharename m x y =
    match m with
    | Lit _ -> m
    | Variable (t, z) -> if x = z then Variable (t, y) else m
    | ListTrm (typ, lst, eff) ->
      let new_lst = List.map (fun trm -> alpharename trm x y) lst in
      ListTrm (typ, new_lst, eff)
    | Constructor (typ, name, payload_lst, eff) ->
      let new_payload_lst = List.map (fun trm -> alpharename trm x y) payload_lst in
      Constructor (typ, name, new_payload_lst, eff)
    | PatternMatch (typ, matched_trm, cases, eff) ->
      let matched_trm' = alpharename matched_trm x y in
      let cases' =
        List.map
          (fun (patt, body) ->
            (* all variables in patterns are bound, so rename only if var is not in pattern *)
            if occurs_in_pat x patt then (patt, body) else (patt, alpharename body x y))
          cases
      in
      PatternMatch (typ, matched_trm', cases', eff)
    | Lambda (t, z, t', m') -> if x = z then m else Lambda (t, z, t', alpharename m' x y)
    | App (rt, m, at, n, e) -> App (rt, alpharename m x y, at, alpharename n x y, e)
    | Let (z, t, m, n, t', e) ->
      let m' = alpharename m x y in
      if x = z then Let (z, t, m', n, t', e) else Let (z, t, m', alpharename n x y, t', e)
    | If (t, b, n, n', e) ->
      If (t, alpharename b x y, alpharename n x y, alpharename n' x y, e)
  ;;

  let shrink_lit = function
    | LitInt i -> Iter.map (fun i' -> Lit (LitInt i')) (Shrink.int i)
    (* TODO how to shrink floats? *)
    | LitStr s -> Iter.map (fun s' -> Lit (LitStr s')) (Shrink.string s)
    | _ -> Iter.empty
  ;;

  let rec term_shrinker term =
    let ( <+> ) = Iter.( <+> ) in
    match term with
    | Lit l -> shrink_lit l
    | Variable (t, _) ->
      (match create_lit t with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
    | ListTrm (t, lst, e) -> Iter.map (fun l -> ListTrm (t, l, e)) (Shrink.list lst)
    | Constructor (typ, name, args, eff) ->
      let open Iter in
      list_elems term_shrinker args >|= fun args' -> Constructor (typ, name, args', eff)
    | PatternMatch (typ, matched_trm, cases, eff) ->
      let open Iter in
      term_shrinker matched_trm >>= fun matched_trm' ->
      list_elems (fun (pat, body) -> Iter.pair (return pat) (term_shrinker body)) cases
      >|= fun cases' -> PatternMatch (typ, matched_trm', cases', eff)
    | Lambda (t, x, s, m) -> Iter.map (fun m' -> Lambda (t, x, s, m')) (term_shrinker m)
    | App (rt, m, at, n, e) ->
      (match create_lit rt with
      | Some c -> Iter.return c
      | None -> Iter.empty)
      <+> (if types_compat at rt then Iter.return n else Iter.empty)
      <+> (match m with
          | App (_, _, at', n', _) when types_compat at' rt -> Iter.return n'
          | Lambda (_, x, s, m') ->
            if fv x m'
            then Iter.return (Let (x, s, n, m', rt, e))
            else Iter.of_list [ m'; Let (x, s, n, m', rt, e) ]
          | Let (x, t, m', n', _, _) ->
            if fv x n
            then (
              (* potential var capt.*)
              let x' = newvar () in
              Iter.return
                (Let (x', t, m', App (rt, alpharename n' x x', at, n, e), rt, e)))
            else Iter.return (Let (x, t, m', App (rt, n', at, n, e), rt, e))
          | _ -> Iter.empty)
      <+> Iter.map (fun m' -> App (rt, m', at, n, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> App (rt, m, at, n', e)) (term_shrinker n)
    | Let (x, t, m, n, s, e) ->
      (match create_lit s with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
      <+> (match (fv x n, m) with
          | false, Let (x', t', m', _, _, _) ->
            if fv x' n
            then (
              (* potential var capt.*)
              let y = newvar () in
              Iter.of_list [ n; Let (y, t', m', n, s, e) ])
            else Iter.of_list [ n; Let (x', t', m', n, s, e) ]
          | false, _ -> Iter.return n
          | true, _ -> Iter.empty)
      <+> Iter.map (fun m' -> Let (x, t, m', n, s, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> Let (x, t, m, n', s, e)) (term_shrinker n)
    | If (t, b, m, n, e) ->
      (match create_lit t with
      | Some c -> Iter.return c
      | _ -> Iter.empty)
      <+> Iter.of_list [ n; m ]
      <+> (match b with
          | Lit _ -> Iter.empty
          | Variable (_, _) -> Iter.empty
          | _ ->
            let x = newvar () in
            Iter.return (Let (x, Bool, b, If (t, Variable (Bool, x), m, n, e), t, e)))
      <+> Iter.map (fun b' -> If (t, b', m, n, e)) (term_shrinker b)
      <+> Iter.map (fun m' -> If (t, b, m', n, e)) (term_shrinker m)
      <+> Iter.map (fun n' -> If (t, b, m, n', e)) (term_shrinker n)
  ;;

  let dep_term_shrinker (typ, term) = Iter.pair (Iter.return typ) (term_shrinker term)

  let wrapper shrinker op_term =
    match op_term with
    | None -> Iter.empty
    | Some term -> Iter.map (fun t -> Some t) (shrinker term)
  ;;

  let shrinker term = wrapper term_shrinker term
  let wrapped_dep_term_shrinker dep_term = wrapper dep_term_shrinker dep_term
end

(*
          (t:s) \in env
   ---------------------------- (VAR)
       env |- t : s/ff/ff

              (x:s), env |- m : t/ef/ev
   ----------------------------------------------------- (LAM)
     env |- (fun (x:s) -> m) : s -ef/ev-> t/ff/ff

      env |- f : s -ef/ev-> t/fef/fev     env |- x : s/xef/xev
    ------------------------------------------------------------ (APP)
       env |- f x : t/ef or fef or xef/(fef and xef) || fev

      env |- m : s/mef/mev     env, (x:s) |- n : t/nef/nev
    -------------------------------------------------------- (LET)
        env |- let x:s = m in n : t/mef or nef/mev or nev

 *)

(* First version, checks type-and-effect annotation *)
let tcheck_lit l =
  match l with
  | LitUnit -> (Unit, no_eff)
  | LitInt _ -> (Int, no_eff)
  | LitFloat _ -> (Float, no_eff)
  | LitBool _ -> (Bool, no_eff)
  | LitStr _ -> (String, no_eff)
;;

let check_opt_invariants (typ, name, payload_lst) =
  (* invariants:
    - typ must be Option _
    - name must be either "Some" or "None"
    - match name with
      | "Some" -> payload list must be a list of one element &&
        unwrapped type t of option must be same as (imm_type payload)
      | "None" -> payload list must be an empty list
      | _ -> "option adt name invariant failed"
   *)
  match typ with
  | Option t ->
    (match name with
    | "Some" ->
      (match payload_lst with
      | [ payload ] ->
        if t = imm_type payload
        then Ok typ
        else Error "check_opt_invariants: some payload type invariant failed"
      | _ -> Error "check_opt_invariants: some payload arity failed")
    | "None" ->
      (match payload_lst with
      | [] -> Ok typ
      | _ -> Error "check_opt_invariants: none payload arity failed")
    | _ -> Error "check_opt_invariants: name invariant failed")
  | _ -> Error "check_opt_invariants: option type invariant failed"
;;

let rec tcheck env term =
  match term with
  | Lit l -> tcheck_lit l
  | Variable (t, v) ->
    (try
       let et = VarMap.find v env in
       if types_compat et t (* annotation may be more concrete then inferred type *)
       then (et, no_eff)
       else failwith "tcheck: variable types disagree"
     with Not_found -> failwith "tcheck: unknown variable")
  | ListTrm (typ, lst, eff) ->
    (match typ with
    | List elem_typ ->
      List.iter
        (fun e ->
          if not (imm_type e = elem_typ)
          then failwith "tcheck: a list type mismatches its element's type")
        lst;
      (typ, eff)
    | _ -> failwith "tcheck: ListTrm must have a list type")
  | Constructor (typ, name, payload_lst, eff) ->
    (match check_opt_invariants (typ, name, payload_lst) with
    | Ok _ ->
      (try
         List.iter (fun trm -> tcheck env trm |> ignore) payload_lst;
         (typ, eff)
       with Failure msg -> failwith msg)
    | Error msg -> failwith msg)
  | PatternMatch (typ, _matched_trm, cases, eff) ->
    let has_type_mismatch typ1 typ2 = if types_compat typ1 typ2 then false else true in
    let has_type_mismatch_lst =
      List.exists (fun (_pat, body) -> has_type_mismatch typ (imm_type body)) cases
    in
    (* FIXME: it fails to typecheck with seed 430633514
      Debugging using printing shows that types are same but it still fails *)
    if has_type_mismatch_lst
    then failwith "tcheck: PatternMatch has a type mismatch"
    else (typ, eff)
  | App (rt, m, at, n, ceff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck env n in
    (match mtyp with
    | Fun (_, e, _) ->
      if meff = no_eff || neff = no_eff
      then (
        match unify mtyp (Fun (at, ceff, rt)) with
        | Sol sub ->
          if types_compat (subst sub mtyp) (Fun (at, ceff, rt))
             (* we obtain annot by instantiating inferred type *)
          then (
            match unify ntyp at with
            | Sol sub' ->
              if types_compat (subst sub' ntyp) at
                 (* we obtain annot by instantiating inferred type *)
              then (
                let j_eff = eff_join e (eff_join meff neff) in
                if eff_leq j_eff ceff
                then (rt, j_eff)
                else
                  failwith
                    ("tcheck: effect annotation disagree in application"
                    ^ "  ceff is "
                    ^ eff_to_str ceff
                    ^ "  j_eff is "
                    ^ eff_to_str j_eff))
              else
                failwith
                  ("tcheck: argument types disagree in application"
                  ^ "  ntyp is "
                  ^ type_to_str ~effannot:true ntyp
                  ^ "  at is "
                  ^ type_to_str ~effannot:true at)
            | No_sol ->
              failwith
                ("tcheck: argument types do not unify in application"
                ^ "  ntyp is "
                ^ type_to_str ~effannot:true ntyp
                ^ "  at is "
                ^ type_to_str ~effannot:true at))
          else
            failwith
              ("tcheck: function types disagree in application"
              ^ ("  sub is "
                ^ Print.list
                    (Print.pair
                       (fun id -> "'a" ^ string_of_int id)
                       (type_to_str ~effannot:true))
                    sub)
              ^ "  mtyp is "
              ^ type_to_str ~effannot:true mtyp
              ^ "  (Fun (at,ceff,rt)) is "
              ^ type_to_str ~effannot:true (Fun (at, ceff, rt)))
        | No_sol ->
          failwith
            ("tcheck: function types do not unify in application"
            ^ "  mtyp is "
            ^ type_to_str ~effannot:true mtyp
            ^ "  (Fun (at,ceff,rt)) is "
            ^ type_to_str ~effannot:true (Fun (at, ceff, rt))))
      else failwith "tcheck: application has subexprs with eff"
    | _ -> failwith "tcheck: application of non-function type")
  | Let (x, t, m, n, ltyp, leff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck (VarMap.add x mtyp env) n in
    if types_compat mtyp t (* annotation may be more concrete then inferred type *)
    then
      (*  annot "int list" instead of the more general "'a list" *)
      if types_compat ntyp ltyp
      then (
        let j_eff = eff_join meff neff in
        if eff_leq j_eff leff
        then (ntyp, leff)
        else
          failwith
            ("tcheck: let-effect disagrees with annotation"
            ^ "  leff is "
            ^ eff_to_str leff
            ^ "  j_eff is "
            ^ eff_to_str j_eff))
      else
        failwith
          ("tcheck: let-body's type disagrees with annotation: "
          ^ "ntyp is "
          ^ type_to_str ~effannot:true ntyp
          ^ "  ltyp is "
          ^ type_to_str ~effannot:true ltyp)
    else failwith "tcheck: let-bound type disagrees with annotation"
  | Lambda (t, x, s, m) ->
    let mtyp, meff = tcheck (VarMap.add x s env) m in
    let ftyp = Fun (s, meff, mtyp) in
    if types_compat ftyp t
    then (ftyp, no_eff)
    else
      failwith
        ("tcheck: Lambda's type disagrees with annotation: "
        ^ "ftyp is "
        ^ type_to_str ~effannot:true ftyp
        ^ "  t is "
        ^ type_to_str ~effannot:true t)
  | If (t, b, m, n, e) ->
    let btyp, beff = tcheck env b in
    if btyp = Bool
    then
      if eff_leq beff e
      then (
        let mtyp, meff = tcheck env m in
        let ntyp, neff = tcheck env n in
        match unify mtyp ntyp with
        | Sol sub ->
          if types_compat (subst sub mtyp) t
             (* we obtain annot by instantiating inferred type *)
          then
            if types_compat (subst sub ntyp) t
               (* we obtain annot by instantiating inferred type *)
            then
              if eff_leq meff e && eff_leq neff e
              then (
                let e' = eff_join beff (eff_join meff neff) in
                (t, e'))
              else failwith "tcheck: If's branch effects disagree with annotation"
            else
              failwith
                ("tcheck: If's else branch type disagrees with annotation: "
                ^ "  term is "
                ^ term_to_ocaml ~typeannot:false term
                ^ "  ntyp is "
                ^ type_to_str ~effannot:true ntyp
                ^ "  (subst sub ntyp) is "
                ^ type_to_str ~effannot:true (subst sub ntyp)
                ^ "  t is "
                ^ type_to_str ~effannot:true t)
          else
            failwith
              ("tcheck: If's then branch type disagrees with annotation: "
              ^ "  term is "
              ^ term_to_ocaml ~typeannot:false term
              ^ "  mtyp is "
              ^ type_to_str ~effannot:true mtyp
              ^ "  (subst sub mtyp) is "
              ^ type_to_str ~effannot:true (subst sub mtyp)
              ^ "  t is "
              ^ type_to_str ~effannot:true t)
        | No_sol ->
          failwith
            ("tcheck: If's branch types do not unify:  "
            ^ "  term is "
            ^ term_to_ocaml ~typeannot:false term
            ^ "  mtyp is "
            ^ type_to_str ~effannot:true mtyp
            ^ "  ntyp is "
            ^ type_to_str ~effannot:true ntyp))
      else failwith "tcheck: If's condition effect disagrees with annotation"
    else failwith "tcheck: If with non-Boolean condition"
;;

let print_wrap t =
  Let
    ( "i",
      Int,
      t,
      App
        ( Unit,
          Variable (Fun (Int, (true, false), Unit), "print_int"),
          Int,
          Variable (Int, "i"),
          (true, false) ),
      Unit,
      (true, false) )
;;

let printer_by_etype typ =
  let fun_name, printer_typ_opt =
    match typ with
    | Int -> ("print_int", lookup_var "print_int" init_tri_env)
    | Float -> ("print_float", lookup_var "print_float" init_tri_env)
    | String -> ("print_string", lookup_var "print_string" init_tri_env)
    | Unit | Typevar _ | Option _ | List _ | Fun _ | Bool ->
      failwith
        "printer_by_etype: such base type should not be generated (not implemented)"
  in
  match printer_typ_opt with
  | Some typ -> Variable (typ, fun_name)
  | None -> failwith "printer_by_etype: printer for this type is unavailable."
;;

let rand_print_wrap typ trm =
  Let
    ( "x",
      typ,
      trm,
      App (Unit, printer_by_etype typ, typ, Variable (typ, "x"), (true, false)),
      Unit,
      (true, false) )
;;

module Arbitrary = struct
  (* TODO: Is it correct to name a function using suffix `_gen`
          if it is of type `'a arbitrary`
  *)
  let term_gen_by_type typ =
    make
      ~print:(Print.option (term_to_ocaml ~typeannot:false))
      ~shrink:Shrinker.shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.term_gen typ (true, false) rs)
  ;;

  let int_term_gen = term_gen_by_type Int

  let arb_type =
    make
      ~print:type_to_str
      Gen.(
        frequency
          [ (1, map (fun i -> Typevar i) (oneofl [ 1; 2; 3; 4; 5 ]));
            (6, sized StaticGenerators.type_gen)
          ])
  ;;

  (* Arbitrary type-dependent term generator - both the term and its type are generated by
  the same random seed *)
  let arb_dep_term_with_cache =
    make
      ~print:
        (let printer (_typ, trm) = term_to_ocaml ~typeannot:false trm in
         Print.option printer)
      ~shrink:Shrinker.wrapped_dep_term_shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.dep_term_gen rs)
  ;;
end

let unify_funtest =
  Test.make
    ~count:1000
    ~name:"unify functional"
    (pair Arbitrary.arb_type Arbitrary.arb_type)
    (fun (ty, ty') ->
      match unify ty ty' with
      | No_sol -> ty <> ty'
      | Sol t ->
        let sty = subst t ty in
        let sty' = subst t ty' in
        types_compat sty sty' || types_compat sty' sty)
;;

(** Tests *)

(* FIXME: update to arb_dep_term *)
let gen_classify =
  Test.make
    ~count:1000
    ~name:"classify gen"
    (make
       ~collect:(fun t -> if t = None then "None" else "Some")
       (gen Arbitrary.int_term_gen))
    (fun _ -> true)
;;

let can_compile_test ~with_logging =
  let logger =
    if not with_logging
    then no_logger
    else make_logger "generated_tests/ocamltestml_log.ml"
  in
  let prgm_filename = "generated_tests/ocamltest.ml" in
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"generated term passes OCaml's typecheck"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None ->
        logger "%s" "failwith(\"dep_t_opt = None\")";
        false
      | Some (_typ, trm) ->
        (try
           let generated_prgm = term_to_ocaml trm in
           logger "%s" generated_prgm;
           write_prog generated_prgm prgm_filename;
           0 = Sys.command ("ocamlc -w -5@20-26 " ^ prgm_filename)
         with _ -> false))
;;

let type_check_test =
  Test.make
    ~count:500
    ~name:"generated term type checks"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None -> false
      | Some (typ, trm) ->
        let env, _, _ = init_tri_env in
        let typ', eff = tcheck env trm in
        types_compat typ typ' && eff_leq eff (true, false))
;;

let int_eq_test =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - int_eq_test"
    Arbitrary.int_term_gen
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (term_to_ocaml (print_wrap t)))
;;

let rand_eq_test typ =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - term gen by given type"
    (Arbitrary.term_gen_by_type typ)
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (term_to_ocaml (rand_print_wrap typ t)))
;;

let dep_eq_test ~with_logging =
  let logger =
    if not with_logging then no_logger else make_logger "generated_tests/testml_log.ml"
  in
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"bytecode/native backends agree - type-dependent term generator"
    Arbitrary.arb_dep_term_with_cache
    (fun dep_t_opt ->
      dep_t_opt
      <> None
      ==>
      match dep_t_opt with
      | None ->
        logger "%s" "failwith(\"dep_t_opt = None\")";
        false
      | Some (typ, trm) ->
        let generated_prgm = rand_print_wrap typ trm |> term_to_ocaml in
        logger "%s" generated_prgm;
        is_native_byte_equiv generated_prgm)
;;

(* The actual call to QCheck_runner.run_tests_main is located in effmain.ml *)
