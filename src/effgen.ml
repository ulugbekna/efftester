module Gen = QCheck.Gen
module Print = QCheck.Print
open Effast
open Effenv
open Effunif
open Effprint

(** Auxiliary functions *)

(* TODO: replace by [QCheck.Gen.float_bound_inclusive] from new QCheck release *)
let float_bound_inclusive bound st = Random.State.float st bound

(* TODO: replace by [QCheck.Gen.shuffle_w_l] from new QCheck release *)
let shuffle_w_l l st =
  let sample (w, v) =
    let fl_w = float_of_int w in
    (float_bound_inclusive 1. st ** (1. /. fl_w), v)
  in
  let samples = List.map sample l in
  List.sort (fun (w1, _) (w2, _) -> compare w2 w1) samples |> List.map snd
;;

let rec first_some f lst =
  match lst with
  | [] -> None
  | x :: xs ->
    (match f x with
    | Some _ as res -> res
    | None -> first_some f xs)
;;

(* The error-reporting code uses either failwith(f) or
   QCheck.Test.fail_report(f).

   - [fail_report] should be used in test *conditions*, as the error
   message is handled by QCheck and printed nicely; on the other hand,
   the more standard [failwith] should be used in test *generators*,
   where no such message support exists.

   - [fail_report] should be used to report a test failure that will
   be logged, lead to shrinking, etc. while [failwith] should be used
   for fatal error that will interrupt the program; in particular,
   they should only be used in the case of programming errors
   (in a generator or in a test), rather than unexpected test inputs.
*)
let failwithf fmt =
  let buf = Buffer.create 20 in
  Format.kfprintf
    (fun ppf ->
      Format.pp_print_flush ppf ();
      Format.pp_print_flush Format.err_formatter ();
      prerr_endline (Buffer.contents buf);
      failwith (Buffer.contents buf))
    (Format.formatter_of_buffer buf)
    ("@[" ^^ fmt ^^ "@]")
;;

module GenOpt : sig
  type 'a t = 'a option Gen.t

  val map : ('a -> 'b) -> 'a t -> 'b t
  val pure : 'a -> 'a t
  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t
  val fail : unit -> 'a t
  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end = struct
  type 'a t = 'a option Gen.t

  let map f a =
    let map_opt f = function
      | None -> None
      | Some v -> Some (f v)
    in
    Gen.map (map_opt f) a
  ;;

  let pure v = Gen.pure (Some v)

  let ( <*> ) f a =
    let apply_opt : ('a -> 'b) option -> 'a option -> 'b option =
     fun f v ->
      match (f, v) with
      | None, _ | _, None -> None
      | Some f, Some v -> Some (f v)
    in
    Gen.( <*> ) (Gen.map apply_opt f) a
  ;;

  let return v = Gen.return (Some v)
  let fail () = Gen.return None

  let ( >>= ) m f =
    Gen.( >>= ) m (function
        | None -> fail ()
        | Some v -> f v)
  ;;
end

module Syntax = struct
  let return = Gen.return
  let return_opt = GenOpt.return
  let fail = GenOpt.fail
  let ( >>= ) = Gen.( >>= )
  let ( >>=? ) = GenOpt.( >>= )
end

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
              (1, Gen.map (fun t -> List t) (recgen (sqrt n)));
              ( 1,
                Gen.map3
                  (fun t e t' -> Fun (t, e, t'))
                  (recgen (n / 2))
                  eff_gen
                  (recgen (n / 2)) )
            ])
  ;;

  let all_type_gen =
    (* Generates all types available in Efftester *)
    Gen.fix (fun recgen n ->
        let base_types = [ Unit; Int; Float; Bool; String ] in
        if n = 0
        then Gen.oneofl base_types
        else
          Gen.frequency
            [ (* Generate no alphas *)
              (4, Gen.oneofl base_types);
              (1, Gen.map (fun t -> Option t) (recgen (sqrt n)));
              (1, Gen.map (fun t -> Ref t) (recgen (sqrt n)));
              ( 1,
                Gen.map
                  (fun tuple_lst -> Tuple tuple_lst)
                  (Gen.small_list (recgen (sqrt n))) );
              (1, Gen.map (fun t -> List t) (recgen (sqrt n)));
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
    let fail s = Printf.sprintf "literal_gen: %s arg. should not happen" s |> failwith in
    match t with
    | Unit -> Gen.return LitUnit
    | Int -> Gen.map (fun i -> LitInt i) int_gen
    | Float -> Gen.map (fun f -> LitFloat f) float_gen
    | Bool -> Gen.map (fun b -> LitBool b) Gen.bool
    | String -> Gen.map (fun s -> LitStr s) string_gen
    | Option _ -> fail "option"
    | Ref _ -> fail "ref"
    | Tuple _ -> fail "tuple"
    | List _ -> fail "list"
    | Typevar _ -> fail "typevar"
    | Fun _ -> fail "funtype"
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
    match s with
    | Unit | Int | Float | Bool | String ->
      [ (6, Gen.map (fun l -> Some (Lit l)) (literal_gen s eff size)) ]
    | Tuple _ | List _ | Option _ | Ref _ | Fun _ | Typevar _ -> []
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
          | Some t -> arity t = arity_s && Effunif.types_compat t s
          | None ->
            failwithf "var_rules: found variable %a without associated type" pp_var x)
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
      let open Syntax in
      var_gen >>= fun x ->
      term_gen_sized (add_var x s env) t eff (size / 2) >>=? fun m ->
      let myeff = imm_eff m in
      return_opt (Lambda (Fun (s, myeff, imm_type m), x, s, m))
    in
    match u with
    | Unit | Int | Float | Bool | String | Option _ | Ref _ | Tuple _ | List _
    | Typevar _ ->
      []
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
    let open Syntax in
    let from_type funeff argeff s =
      term_gen_sized env (Fun (s, eff, t)) funeff (size / 2) >>=? fun f ->
      term_gen_sized env s argeff (size / 2) >>=? fun x ->
      match imm_type f with
      | Fun (_, e, frange) ->
        let funeff = imm_eff f in
        let argeff = imm_eff x in
        let ef, ev = eff_join e (eff_join funeff argeff) in
        let eff' = (ef, ev || (fst funeff && fst argeff)) in
        if eff_leq eff' eff
        then return_opt (App (frange, f, imm_type x, x, eff'))
        else
          (*GenOpt.fail ()*)
          failwith "app_rules generated application with too big effect"
      | _ ->
        failwithf
          ("app_rules generated application with non-function:@;"
          ^^ "@[<v>t is %a,@ f is %a,@ imm_type f is %a@]")
          (pp_type ~effannot:true)
          t
          (pp_term ~typeannot:false)
          f
          (pp_type ~effannot:true)
          (imm_type f)
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
        failwithf
          ("get_arg_types: should not happen:@;" ^^ "@[<v>s is %a,@ t is %a@]")
          (pp_type ~effannot:true)
          s
          (pp_type ~effannot:true)
          t
    in
    (* returns the index of the first effect - or else the number of arguments *)
    let rec first_eff = function
      | s when types_compat s t || types_compat t s -> 0
      | Fun (_, e, t) -> if e = no_eff then 1 + first_eff t else 1
      | s -> failwithf "first_eff: should not happen@ %a" (pp_type ~effannot:true) s
    in
    (* recursively build application term argument by argument *)
    let rec apply term r_type n effacc = function
      | [] -> Syntax.return_opt term
      | arg :: args ->
        (* arg 'n' may have effect 'eff' *)
        let myeff = if n = 0 then eff else no_eff in
        let open Syntax in
        term_gen_sized env arg myeff (size / 2) >>=? fun a ->
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
            failwith "apply: overly effectful program generated. This should not happen."
        | _ ->
          failwith "apply: non-function type expecting argument. This should not happen")
    in
    let application s f =
      (* s is the unnormalized, effect-full type *)
      let f_term = Variable (s, f) in
      match mgu s t with
      | None ->
        failwithf
          "indir_rules, application:@ the return types of chosen variable@ @[%a : %a@]@ \
           do not match goal type %a"
          pp_var
          f
          (pp_type ~effannot:true)
          s
          (pp_type ~effannot:true)
          t
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
        let open Syntax in
        build_subst ftvs >>= fun sub' ->
        let goal_type = subst sub' goal_type in
        let arg_types =
          try get_arg_types goal_type (subst sub t)
          with Failure exc ->
            failwithf
              "%s@ [@<v>s is %a,@ sub is %a, (subst sub s) is %a, t is %a@]"
              exc
              (pp_type ~effannot:true)
              s
              (pp_solution ~effannot:true)
              sub
              (pp_type ~effannot:true)
              (subst sub s)
              (pp_type ~effannot:true)
              t
        in
        let index_gen =
          let first_eff_index = first_eff goal_type in
          if first_eff_index = 0 then return 0 else Gen.int_bound (first_eff_index - 1)
        in
        index_gen >>= fun n -> apply f_term goal_type n no_eff arg_types
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
    let open Syntax in
    let from_type s =
      var_gen >>= fun x ->
      term_gen_sized env s eff (size / 2) >>=? fun m ->
      term_gen_sized (add_var x s env) t eff (size / 2) >>=? fun n ->
      let myeff = eff_join (imm_eff m) (imm_eff n) in
      return_opt (Let (x, s, m, n, imm_type n, myeff))
    in
    [ (6, type_gen (size / 2) >>= from_type) ]

  and if_rules env t eff size =
    let open Syntax in
    let gen =
      (* predicate is generated *)
      term_gen_sized env Bool eff (size / 3) >>=? fun b ->
      (* then branch is generated *)
      term_gen_sized env t eff (size / 3) >>=? fun m ->
      let then_type = imm_type m in
      match unify then_type t with
      | No_sol ->
        failwithf
          "if_rules: generated type %a in then branch does not unify with goal type"
          (pp_type ~effannot:true)
          then_type
          (pp_type ~effannot:true)
          t
      | Sol sub ->
        let subst_t = subst sub t in
        (* else branch is generated *)
        term_gen_sized env subst_t eff (size / 3) >>=? fun n ->
        let else_type = imm_type n in
        (match unify else_type subst_t with
        | No_sol ->
          failwithf
            "if_rules: generated else branch type %a does not unify with subst goal \
             type %a"
            (pp_type ~effannot:true)
            else_type
            (pp_type ~effannot:true)
            subst_t
        | Sol sub' ->
          let mytype = subst sub' subst_t in
          let myeff = eff_join (imm_eff b) (eff_join (imm_eff m) (imm_eff n)) in
          return_opt (If (mytype, b, m, n, myeff)))
    in
    [ (3, gen) ]

  and option_intro_rules env t eff size =
    let gen =
      let open Syntax in
      match t with
      | Option t' ->
        Gen.frequencyl [ (2, "Some"); (1, "None") ] >>= fun name ->
        (match name with
        | "None" -> return (Some (none t))
        | "Some" ->
          term_gen_sized env t' eff (size - 1) >>=? fun trm ->
          return_opt (some t trm eff)
        | _ -> failwith "option_intro_rules: impossible option adt_constr name")
      | _ -> return None
    in
    [ (3, gen) ]

  and option_elim_rules env t eff size =
    let gen =
      let open Syntax in
      StaticGenerators.basetype_gen >>= fun bt ->
      term_gen_sized env (Option bt) eff (size / 3) >>=? fun match_trm ->
      var_gen >>= fun var_name ->
      let extended_env = add_var var_name bt env in
      term_gen_sized extended_env t eff (size / 3) >>=? fun some_branch_trm ->
      term_gen_sized env t eff (size / 3) >>=? fun none_branch_trm ->
      return_opt
        (PatternMatch
           ( t,
             match_trm,
             [ (PattConstr (bt, "Some", [ PattVar var_name ]), some_branch_trm);
               (PattConstr (bt, "None", []), none_branch_trm)
             ],
             eff ))
    in
    [ (3, gen) ]

  and tuple_intro_rules env t eff size : (int * term GenOpt.t) list =
    match t with
    | Tuple t_lst ->
      let gen st : term option =
        let exception Short_circuit in
        match
          List.map
            (fun t ->
              match term_gen_sized env t eff size st with
              | Some trm -> trm
              | None -> raise Short_circuit)
            t_lst
        with
        | exception Short_circuit -> None
        | trm_lst ->
          Some (Constructor (t, TupleArity (List.length trm_lst), trm_lst, eff))
      in
      [ (3, gen) ]
    | _ -> []

  and list_intro_rules env goal_typ eff size =
    let open Syntax in
    match goal_typ with
    | List elt_typ ->
      let gen =
        match elt_typ with
        | Typevar _ -> return_opt (ListTrm (goal_typ, [], no_eff))
        | _ ->
          if size = 0
          then return_opt (ListTrm (goal_typ, [], no_eff))
          else
            Gen.int_bound (sqrt size) >>= fun lst_size ->
            let elems_gen =
              let lst_size = if lst_size = 0 then 1 else lst_size in
              Gen.list_size
                (return lst_size)
                (term_gen_sized env elt_typ eff (size / (lst_size * 10)))
            in
            elems_gen >>= fun opt_lst ->
            let lst =
              List.fold_left
                (fun acc_lst elt ->
                  match elt with
                  | Some x -> x :: acc_lst
                  | None -> acc_lst)
                []
                opt_lst
            in
            return_opt (ListTrm (goal_typ, lst, eff))
      in
      [ (3, gen) ]
    | _ -> []

  (* [term_from_rules rules] returns a constant generator with a term option,
     in which the term was generated using a randomly picked generator from [rules].

     Generators are picked according to their weights.
  *)
  and term_from_rules rules : term option Gen.t =
   fun st ->
    let shuffled_rules = shuffle_w_l rules st in
    first_some (fun rule -> rule st) shuffled_rules

  and term_gen_sized env goal eff size =
    let apply f = f env goal eff size in
    let apply_concat lst = List.map apply lst |> List.concat in
    if size = 0
    then apply_concat [ lit_rules; var_rules ] |> term_from_rules
    else
      apply_concat
        [ lit_rules;
          option_intro_rules;
          option_elim_rules;
          tuple_intro_rules;
          list_intro_rules;
          (* var rule is covered by indir with no args *)
          app_rules;
          lam_rules;
          indir_rules;
          let_rules;
          if_rules
        ]
      |> term_from_rules
  ;;

  let list_permute_term_gen_rec_wrapper env goal eff =
    Gen.sized (term_gen_sized env goal eff)
  ;;

  let term_gen = list_permute_term_gen_rec_wrapper init_tri_env

  let dep_term_gen =
    let open Syntax in
    basetype_gen >>= fun typ ->
    term_gen typ (true, false) >>=? fun trm -> return_opt (typ, trm)
  ;;
end
