module Iter = QCheck.Iter
module Shrink = QCheck.Shrink
open Effast

(* [shrink_list_elems shrink l yield] shrinks a list of elements [l] given a shrinker [shrink]
  TODO: use QCheck version of [shrink_list_elems] when @gasche's PR gets merged *)
let shrink_list_elems shrink l yield =
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

let rec occurs_in_pat var pat =
  match pat with
  | PattVar (_, x) -> x = var
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

let rec term_size = function
  | Variable _ -> 1
  | Lit lit ->
    (match lit with
    | LitUnit -> 1
    | LitInt n -> 1 + abs n (* we want shrinkers that reduce n to reduce size *)
    | LitInt32 n -> 1 + (Int32.abs n |> Int32.to_int)
    | LitInt64 n -> 1 + (Int64.abs n |> Int64.to_int)
    | LitNativeInt n -> 1 + (Nativeint.abs n |> Nativeint.to_int)
    | LitFloat x -> 1 + int_of_float (ceil (abs_float x))
    | LitBool _ -> 1
    | LitStr s -> 1 + String.length s)
  | ListTrm (_, ms, _) | Constructor (_, _, ms, _) ->
    List.fold_left ( + ) 1 (List.map term_size ms)
  | PatternMatch (_, m, cases, _) ->
    (* ignore pattern sizes for now *)
    let case_size (_pat, m) = term_size m in
    List.fold_left ( + ) 1 (term_size m :: List.map case_size cases)
  | Lambda (_, _, _, m) -> 1 + term_size m
  | App (_, m, _, n, _) | Let (_, _, m, n, _, _) -> 1 + term_size m + term_size n
  | If (_, m, m1, m2, _) -> 1 + term_size m + term_size m1 + term_size m2
;;

(* the simplest possible term at a given type *)
let rec minimal_term ty =
  match ty with
  | Typevar _ -> raise Not_found
  | Unit -> Lit LitUnit
  | Int -> Lit (LitInt 0)
  | Int32 -> Lit (LitInt32 0l)
  | Int64 -> Lit (LitInt64 0L)
  | NativeInt -> Lit (LitNativeInt 0n)
  | Float -> Lit (LitFloat 0.)
  | Bool -> Lit (LitBool true)
  | String -> Lit (LitStr "")
  | Option _ -> none ty
  | Ref t -> App (ty, Ref.ref_f, t, minimal_term t, (true, false))
  | Tuple t_lst ->
    let arity = List.length t_lst in
    let elts = List.map minimal_term t_lst in
    Constructor (ty, TupleArity arity, elts, no_eff)
  | List _ -> ListTrm (ty, [], no_eff)
  | Fun (input_t, _, output_t) ->
    let body = minimal_term output_t in
    Lambda (ty, "x", input_t, body)
;;

let rec term_shrinker term =
  let ( <+> ) = Iter.( <+> ) in
  (match minimal_term (imm_type term) with
  | exception Not_found -> Iter.empty
  | mini ->
    (* checking that the minimal term has a strictly-smaller size
           prevents us from shrinking a minimal term into itself,
           which would loop infinitely *)
    if term_size mini < term_size term then Iter.return mini else Iter.empty)
  <+>
  match term with
  | Lit l -> shrink_lit l
  | Variable (_, _) -> Iter.empty
  | ListTrm (t, lst, e) -> Iter.map (fun l -> ListTrm (t, l, e)) (Shrink.list lst)
  | Constructor (typ, name, args, eff) ->
    let open Iter in
    shrink_list_elems term_shrinker args >|= fun args' ->
    Constructor (typ, name, args', eff)
  | PatternMatch (typ, matched_trm, cases, eff) ->
    let open Iter in
    Iter.map (fun m' -> PatternMatch (typ, m', cases, eff)) (term_shrinker matched_trm)
    <+> ( shrink_list_elems
            (fun (pat, body) -> Iter.pair (return pat) (term_shrinker body))
            cases
        >|= fun c' -> PatternMatch (typ, matched_trm, c', eff) )
  | Lambda (t, x, s, m) -> Iter.map (fun m' -> Lambda (t, x, s, m')) (term_shrinker m)
  | App (rt, m, at, n, e) ->
    (if Effunif.types_compat at rt then Iter.return n else Iter.empty)
    <+> (match m with
        | App (_, _, at', n', _) when Effunif.types_compat at' rt -> Iter.return n'
        | Lambda (_, x, s, m') ->
          if fv x m'
          then Iter.return (Let (x, s, n, m', rt, e))
          else Iter.of_list [ m'; Let (x, s, n, m', rt, e) ]
        | Let (x, t, m', n', _, _) ->
          if fv x n
          then (
            (* potential var capt.*)
            let x' = newvar () in
            Iter.return (Let (x', t, m', App (rt, alpharename n' x x', at, n, e), rt, e)))
          else Iter.return (Let (x, t, m', App (rt, n', at, n, e), rt, e))
        | _ -> Iter.empty)
    <+> Iter.map
          (fun (m', n') -> App (rt, m', at, n', e))
          (Shrink.pair term_shrinker term_shrinker (m, n))
  | Let (x, t, m, n, s, e) ->
    (match (fv x n, m) with
    | false, Let (x', t', m', _, _, _) ->
      if fv x' n
      then (
        (* potential var capt.*)
        let y = newvar () in
        Iter.of_list [ n; Let (y, t', m', n, s, e) ])
      else Iter.of_list [ n; Let (x', t', m', n, s, e) ]
    | false, _ -> Iter.return n
    | true, _ -> Iter.empty)
    <+> Iter.map
          (fun (m', n') -> Let (x, t, m', n', s, e))
          (Shrink.pair term_shrinker term_shrinker (m, n))
  | If (t, b, m, n, e) ->
    Iter.of_list [ n; m ]
    <+> (match b with
        | Lit _ -> Iter.empty
        | Variable (_, _) -> Iter.empty
        | _ ->
          let x = newvar () in
          Iter.return (Let (x, Bool, b, If (t, Variable (Bool, x), m, n, e), t, e)))
    <+> Iter.map
          (fun (b', m', n') -> If (t, b', m', n', e))
          (Shrink.triple term_shrinker term_shrinker term_shrinker (b, m, n))
;;

let dep_term_shrinker (typ, term) = Iter.pair (Iter.return typ) (term_shrinker term)

let wrapper shrinker op_term =
  match op_term with
  | None -> Iter.empty
  | Some term -> Iter.map (fun t -> Some t) (shrinker term)
;;

let shrinker term = wrapper term_shrinker term
let wrapped_dep_term_shrinker dep_term = wrapper dep_term_shrinker dep_term
