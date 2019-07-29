open Effast

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
    | Ref a, Ref b -> unify_list [ (a, b) ] @ sub
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
    | Ref _, _
    | List _, _
    | Fun _, _ ->
      raise No_solution)
;;

let unify r t = try Sol (unify_list [ (r, t) ]) with No_solution -> No_sol

(* determines whether the first arg is a generalization of the second *)
(* or framed differently: whether the second is a particular instance of the first *)
let rec types_compat t t' =
  match (t, t') with
  | Unit, Unit | Int, Int | Float, Float | Bool, Bool | String, String -> true
  | Option a, Option b -> types_compat a b
  | Ref a, Ref b -> types_compat a b
  | Fun (at, e, rt), Fun (at', e', rt') ->
    types_compat at' at && types_compat rt rt' && eff_leq e e'
  | List et, List et' -> types_compat et et'
  | Typevar _, _ ->
    (match unify t t' with
    | No_sol -> false
    | Sol _ -> true)
  | Unit, _
  | Int, _
  | Float, _
  | Bool, _
  | String, _
  | Option _, _
  | Ref _, _
  | Fun _, _
  | List _, _ ->
    false
;;

let rec get_return_types = function
  | Fun (s, e, t) -> Fun (s, e, t) :: get_return_types t
  | t -> [ t ]
;;
