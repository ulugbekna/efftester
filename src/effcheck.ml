module Print = QCheck.Print
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
          if not (types_compat (imm_type e) elem_typ)
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
  | PatternMatch (typ, matched_trm, cases, eff) ->
    let has_pat_type_mismatch pat =
      match pat with
      | PattVar _ -> false
      | PattConstr (typ, _, _) -> types_compat (imm_type matched_trm) typ
    in
    let has_type_mismatch typ1 typ2 = if types_compat typ1 typ2 then false else true in
    let has_type_mismatch_lst =
      List.exists
        (fun (pat, body) ->
          has_type_mismatch (imm_type body) typ || has_pat_type_mismatch pat)
        cases
    in
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
                    ^ str_of_pp pp_eff ceff
                    ^ "  j_eff is "
                    ^ str_of_pp pp_eff j_eff))
              else
                failwith
                  ("tcheck: argument types disagree in application"
                  ^ "  ntyp is "
                  ^ str_of_pp (pp_type ~effannot:true) ntyp
                  ^ "  at is "
                  ^ str_of_pp (pp_type ~effannot:true) at)
            | No_sol ->
              failwith
                ("tcheck: argument types do not unify in application"
                ^ "  ntyp is "
                ^ str_of_pp (pp_type ~effannot:true) ntyp
                ^ "  at is "
                ^ str_of_pp (pp_type ~effannot:true) at))
          else
            failwith
              ("tcheck: function types disagree in application"
              ^ ("  sub is "
                ^ Print.list
                    (Print.pair
                       (fun id -> "'a" ^ string_of_int id)
                       (str_of_pp (pp_type ~effannot:true)))
                    sub)
              ^ "  mtyp is "
              ^ str_of_pp (pp_type ~effannot:true) mtyp
              ^ "  (Fun (at,ceff,rt)) is "
              ^ str_of_pp (pp_type ~effannot:true) (Fun (at, ceff, rt)))
        | No_sol ->
          failwith
            ("tcheck: function types do not unify in application"
            ^ "  mtyp is "
            ^ str_of_pp (pp_type ~effannot:true) mtyp
            ^ "  (Fun (at,ceff,rt)) is "
            ^ str_of_pp (pp_type ~effannot:true) (Fun (at, ceff, rt))))
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
            ^ str_of_pp pp_eff leff
            ^ "  j_eff is "
            ^ str_of_pp pp_eff j_eff))
      else
        failwith
          ("tcheck: let-body's type disagrees with annotation: "
          ^ "ntyp is "
          ^ str_of_pp (pp_type ~effannot:true) ntyp
          ^ "  ltyp is "
          ^ str_of_pp (pp_type ~effannot:true) ltyp)
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
        ^ str_of_pp (pp_type ~effannot:true) ftyp
        ^ "  t is "
        ^ str_of_pp (pp_type ~effannot:true) t)
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
                ^ str_of_pp (pp_term ~typeannot:false) term
                ^ "  ntyp is "
                ^ str_of_pp (pp_type ~effannot:true) ntyp
                ^ "  (subst sub ntyp) is "
                ^ str_of_pp (pp_type ~effannot:true) (subst sub ntyp)
                ^ "  t is "
                ^ str_of_pp (pp_type ~effannot:true) t)
          else
            failwith
              ("tcheck: If's then branch type disagrees with annotation: "
              ^ "  term is "
              ^ str_of_pp (pp_term ~typeannot:false) term
              ^ "  mtyp is "
              ^ str_of_pp (pp_type ~effannot:true) mtyp
              ^ "  (subst sub mtyp) is "
              ^ str_of_pp (pp_type ~effannot:true) (subst sub mtyp)
              ^ "  t is "
              ^ str_of_pp (pp_type ~effannot:true) t)
        | No_sol ->
          failwith
            ("tcheck: If's branch types do not unify:  "
            ^ "  term is "
            ^ str_of_pp (pp_term ~typeannot:false) term
            ^ "  mtyp is "
            ^ str_of_pp (pp_type ~effannot:true) mtyp
            ^ "  ntyp is "
            ^ str_of_pp (pp_type ~effannot:true) ntyp))
      else failwith "tcheck: If's condition effect disagrees with annotation"
    else failwith "tcheck: If with non-Boolean condition"
;;
