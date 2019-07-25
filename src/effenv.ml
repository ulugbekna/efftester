open Effast

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
    let rts = Effunif.get_return_types norm_new_type in
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
          (Effunif.get_return_types (normalize_eff s))
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
    (arity t = arity_s && Effunif.types_compat t s)
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
    [ (* ref operators *)
      ("ref", Ref.ref_t);
      ("(!)", Ref.deref_t);
      ("(:=)", Ref.update_t);
      (* These follow the order and specification of the Pervasives module
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
