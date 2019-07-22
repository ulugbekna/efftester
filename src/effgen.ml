module Gen = QCheck.Gen
module Print = QCheck.Print
open Effast
open Effenv
open Effunif
open Effprint

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
          | Some t -> arity t = arity_s && Effunif.types_compat t s
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
              ^ str_of_pp (pp_type ~effannot:true) t
              ^ " f is "
              ^ str_of_pp (pp_term ~typeannot:false) f
              ^ " imm_type f is "
              ^ str_of_pp (pp_type ~effannot:true) (imm_type f)))
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
          ^ str_of_pp (pp_type ~effannot:true) s
          ^ " t is "
          ^ str_of_pp (pp_type ~effannot:true) t)
    in
    (* returns the index of the first effect - or else the number of arguments *)
    let rec first_eff = function
      | s when types_compat s t || types_compat t s -> 0
      | Fun (_, e, t) -> if e = no_eff then 1 + first_eff t else 1
      | s ->
        failwith ("first_eff: should not happen  " ^ str_of_pp (pp_type ~effannot:true) s)
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
          ^ str_of_pp (pp_type ~effannot:true) s
          ^ " do not match goal type "
          ^ str_of_pp (pp_type ~effannot:true) t)
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
                print_endline ("s is " ^ str_of_pp (pp_type ~effannot:true) s);
                print_endline
                  ("sub is "
                  ^ Print.list
                      (Print.pair
                         (fun id -> "'a" ^ string_of_int id)
                         (str_of_pp (pp_type ~effannot:true)))
                      sub);
                print_endline
                  ("(subst sub s) is " ^ str_of_pp (pp_type ~effannot:true) (subst sub s));
                print_endline ("t is " ^ str_of_pp (pp_type ~effannot:true) t);
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
              ^ str_of_pp (pp_type ~effannot:true) then_type
              ^ " in then branch does not unify with goal type "
              ^ str_of_pp (pp_type ~effannot:true) t)
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
                  ^ str_of_pp (pp_type ~effannot:true) else_type
                  ^ " does not unify with subst goal type "
                  ^ str_of_pp (pp_type ~effannot:true) subst_t)
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
