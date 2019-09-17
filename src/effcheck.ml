module Print = QCheck.Print
module Test = QCheck.Test
open Effast
open Effenv
open Effunif
open Effprint

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
  | LitInt32 _ -> (Int32, no_eff)
  | LitInt64 _ -> (Int64, no_eff)
  | LitNativeInt _ -> (NativeInt, no_eff)
  | LitFloat _ -> (Float, no_eff)
  | LitBool _ -> (Bool, no_eff)
  | LitStr _ -> (String, no_eff)
;;

(** checks that a given pattern is well-typed, and returns the
   scrutinee type and well-typed environment returned by that pattern *)
let rec pcheck = function
  | PattVar (ty, x) -> VarMap.singleton x ty
  | PattConstr (ty, cstr, ps) ->
    let disjoint_union env1 env2 =
      VarMap.merge
        (fun x o1 o2 ->
          match (o1, o2) with
          | None, None -> None
          | Some ty, None | None, Some ty -> Some ty
          | Some _, Some _ ->
            Test.fail_reportf "pcheck: the variable %s occurs more than once" x)
        env1
        env2
    in
    let pcheck_args tys args =
      if List.length tys <> List.length args
      then Test.fail_report "pcheck: arity mismatch";
      List.fold_left2
        (fun env ty p ->
          let p_ty = imm_pat_type p in
          if not (types_compat ty p_ty)
             (* Note: this check is in the opposite direction
              than the check on terms: in a constructedterm
              `K(e)`, the immediate type of `e` may be "less"
              (less effectful, less general) than the type expected by K;
              for patterns it is the converse, if the constructor
              K expects a sub-pattern at a given type, then the actual
              type of the sub-pattern cannot be less general (it would
              miss some possible scrutinees), it should be more general.

              For example if (x, y) claims to match on values of type
              ((a -{pure}-> b) * c), it is fine if the pattern variable x
              accepts the more general type (a -{impure}-> b) -- the typing
              environment will be populated with this less precise type.
              On the other hand, it would be unsound for (x, y) to claim to match
              on ((a -{impure}-> b) * c) and yet populate the environment with
              (x : (a -{pure}-> b)). *)
          then Test.fail_report "pcheck: inner pattern mismatch";
          disjoint_union env (pcheck p))
        VarMap.empty
        tys
        args
    in
    (match (cstr, ty) with
    | TupleArity n, Tuple tys ->
      if not (List.length tys = n) then Test.fail_report "pcheck: tuple arity mismatch";
      pcheck_args tys ps
    | TupleArity _, _ -> Test.fail_report "pcheck: tuple constructor at non-tuple type"
    | Variant "None", Option _t -> pcheck_args [] ps
    | Variant "Some", Option t -> pcheck_args [ t ] ps
    | Variant (("Some" | "None") as cstr), _ ->
      Test.fail_reportf "pcheck: %s must have type option" cstr
    | Variant cstr, _ -> Test.fail_reportf "pcheck: unknown variant constructor %S" cstr)
;;

(** checks that given term has indicated type and holds invariants associated with it *)
let compat_sig (ty1, eff1) (ty2, eff2) = types_compat ty1 ty2 && eff_leq eff1 eff2

let assert_compat explanation sig1 sig2 =
  if compat_sig sig1 sig2
  then ()
  else Test.fail_reportf "effcheck: signature mismatch in %s" explanation
;;

let rec tcheck_compat env term explanation expected_sig =
  let term_sig = tcheck env term in
  assert_compat explanation term_sig expected_sig

and tcheck env term =
  match term with
  | Lit l -> tcheck_lit l
  | Variable (t, v) ->
    (match VarMap.find v env with
    | exception Not_found -> Test.fail_reportf "tcheck: unknown variable %s" v
    | et ->
      if not (types_compat et t) (* annotation may be more concrete then inferred type *)
      then Test.fail_report "tcheck: variable types disagree";
      (et, no_eff))
  | ListTrm (typ, lst, eff) ->
    let elem_typ =
      match typ with
      | List et -> et
      | _ -> Test.fail_report "tcheck: ListTrm must have a list type"
    in
    List.iter (fun e -> tcheck_compat env e "list element" (elem_typ, eff)) lst;
    (typ, eff)
  | Constructor (typ, cstr, args, eff) ->
    let check_args tys args =
      if List.length tys <> List.length args
      then Test.fail_report "tcheck: arity mismatch";
      List.iter2
        (fun ty e -> tcheck_compat env e "constructor argument" (ty, eff))
        tys
        args
    in
    (match typ with
    | Tuple tys ->
      (match cstr with
      | TupleArity i ->
        if List.length tys <> i
        then Test.fail_report "tcheck: tuple constructor of incorrect arity";
        check_args tys args
      | _ -> Test.fail_report "tcheck: incorrect tuple constructor")
    | Option t ->
      (match cstr with
      | Variant "None" -> check_args [] args
      | Variant "Some" -> check_args [ t ] args
      | _ -> Test.fail_report "tcheck: incorrect option constructor")
    | _ -> Test.fail_report "tcheck: constructor at unexpected type");
    (typ, eff)
  | PatternMatch (ret_typ, matched_trm, cases, eff) ->
    tcheck env matched_trm |> ignore;
    let check_case (pat, body) =
      let body_env = VarMap.union (fun _ _ t -> Some t) env (pcheck pat) in
      tcheck_compat body_env body "right-hand-side" (ret_typ, eff)
    in
    List.iter check_case cases;
    (ret_typ, eff)
  | App (rt, m, at, n, ceff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck env n in
    let fun_eff =
      match mtyp with
      | Fun (_, eff, _) -> eff
      | _ -> Test.fail_report "tcheck: application of non-function type"
    in
    if not (List.mem no_eff [ meff; neff ])
    then Test.fail_report "tcheck: application has subexprs with eff";
    let msub, mtyp =
      match unify mtyp (Fun (at, ceff, rt)) with
      | No_sol ->
        Test.fail_reportf
          ("tcheck: function types do not unify in application:@;"
          ^^ "@[<v>mtyp is %a,@ (Fun (at,ceff,rt)) is %a@]")
          (pp_type ~effannot:true)
          mtyp
          (pp_type ~effannot:true)
          (Fun (at, ceff, rt))
      | Sol sub -> (sub, subst sub mtyp)
    in
    let _nsub, ntyp =
      match unify ntyp at with
      | No_sol ->
        Test.fail_reportf
          ("tcheck: argument types do not unify in application:@;"
          ^^ "@[<v>ntyp is %a,@ at is %a@]")
          (pp_type ~effannot:true)
          ntyp
          (pp_type ~effannot:true)
          at
      | Sol sub -> (sub, subst sub ntyp)
    in
    if not (types_compat mtyp (Fun (at, ceff, rt)))
    then
      Test.fail_reportf
        ("tcheck: function types disagree in application:@;"
        ^^ "@[<v>sub is %a,@ mtyp is %a,@ (Fun (at,ceff,rt)) is %a@]")
        (pp_solution ~effannot:true)
        msub
        (pp_type ~effannot:true)
        mtyp
        (pp_type ~effannot:true)
        (Fun (at, ceff, rt));
    if not (types_compat ntyp at)
    then
      Test.fail_reportf
        ("tcheck: argument types disagree in application:@;"
        ^^ "@[<v>ntyp is %a,@ at is %a@]")
        (pp_type ~effannot:true)
        ntyp
        (pp_type ~effannot:true)
        at;
    let j_eff = eff_join fun_eff (eff_join meff neff) in
    if not (eff_leq j_eff ceff)
    then
      Test.fail_reportf
        ("tcheck: effect annotation disagree in application:@;"
        ^^ "@[<v>ceff is %a,@ j_eff is %a@]")
        pp_eff
        ceff
        pp_eff
        j_eff;
    (rt, j_eff)
  | Let (x, t, m, n, ltyp, leff) ->
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck (VarMap.add x mtyp env) n in
    if not (types_compat mtyp t)
    then Test.fail_report "tcheck: let-bound type disagrees with annotation";
    (*  annot "int list" instead of the more general "'a list" *)
    if not (types_compat ntyp ltyp)
    then
      Test.fail_reportf
        ("tcheck: let-body's type disagrees with annotation:@;"
        ^^ "@[<v>ntyp is %a, ltyp is %a@]")
        (pp_type ~effannot:true)
        ntyp
        (pp_type ~effannot:true)
        ltyp;
    let j_eff = eff_join meff neff in
    if not (eff_leq j_eff leff)
    then
      Test.fail_reportf
        ("tcheck: let-effect disagrees with annotation:@;"
        ^^ "@[<v>leff is %a,@ j_eff is %a@]")
        pp_eff
        leff
        pp_eff
        j_eff;
    (ntyp, leff)
  | Lambda (t, x, s, m) ->
    let mtyp, meff = tcheck (VarMap.add x s env) m in
    let ftyp = Fun (s, meff, mtyp) in
    if types_compat ftyp t
    then (ftyp, no_eff)
    else
      Test.fail_reportf
        ("tcheck: Lambda's type disagrees with annotation:@;"
        ^^ "@[<v>ftyp is %a,@ t is %a@]")
        (pp_type ~effannot:true)
        ftyp
        (pp_type ~effannot:true)
        t
  | If (t, b, m, n, e) ->
    let btyp, beff = tcheck env b in
    assert_compat "boolean condition" (btyp, beff) (Bool, e);
    let mtyp, meff = tcheck env m in
    let ntyp, neff = tcheck env n in
    let mtyp, ntyp =
      match unify mtyp ntyp with
      | No_sol ->
        Test.fail_reportf
          ("tcheck: If's branch types do not unify:@;"
          ^^ "@[<v>term is %a,@ mtyp is %a,@ ntyp is %a@]")
          (pp_term ~typeannot:false)
          term
          (pp_type ~effannot:true)
          mtyp
          (pp_type ~effannot:true)
          ntyp
      | Sol sub -> (subst sub mtyp, subst sub ntyp)
    in
    assert_compat "the then branch" (mtyp, meff) (t, e);
    assert_compat "the else branch" (ntyp, neff) (t, e);
    let e' = eff_join beff (eff_join meff neff) in
    (t, e')
;;
