open Effast

let str_of_pp printer input =
  let buf = Buffer.create 20 in
  let ppf = Format.formatter_of_buffer buf in
  Format.fprintf ppf "@[<hv2>@;<0 -2>%a@]" printer input;
  Format.pp_print_flush ppf ();
  Buffer.contents buf
;;

let pp_pair pp1 pp2 ppf (v1, v2) = Format.fprintf ppf "@[(%a,@ %a)@]" pp1 v1 pp2 v2

let pp_list pp ppf vs =
  let pp_sep ppf () = Format.fprintf ppf ",@ " in
  Format.fprintf ppf "[@[<hov>%a]@]" (Format.pp_print_list ~pp_sep pp) vs
;;

let pp_option pp ppf = function
  | None -> ()
  | Some v -> pp ppf v
;;

let pp_eff ppf (ef, ev) = Format.fprintf ppf "%B/%B" ef ev
let pp_var ppf x = Format.fprintf ppf "%s" x
let pp_tvar ppf a = Format.fprintf ppf "'a%d" a

let pp_type ?(effannot = false) ppf etype =
  let rec pp_type ppf t =
    let below = pp_param_type in
    let rec self ppf = function
      | Fun (s, e, t) ->
        Format.fprintf
          ppf
          "%a@ -%a> %a"
          below
          s
          (pp_option pp_eff)
          (if effannot then Some e else None)
          self
          t
      | other -> below ppf other
    in
    Format.fprintf ppf "@[<hv>%a@]" self t
  and pp_param_type ppf t =
    let below = pp_simple_type in
    let rec self ppf = function
      | Option e -> Format.fprintf ppf "%a@ option" self e
      | Ref e -> Format.fprintf ppf "%a@ ref" self e
      | List s -> Format.fprintf ppf "%a@ list" self s
      | other -> below ppf other
    in
    Format.fprintf ppf "@[<hov2>%a@]" self t
  and pp_simple_type ppf = function
    | Typevar a -> pp_tvar ppf a
    | Unit -> Format.fprintf ppf "unit"
    | Int -> Format.fprintf ppf "int"
    | Float -> Format.fprintf ppf "float"
    | Bool -> Format.fprintf ppf "bool"
    | String -> Format.fprintf ppf "string"
    | (Fun _ | Option _ | Ref _ | List _) as non_simple ->
      Format.fprintf ppf "@[<2>(%a)@]" pp_type non_simple
  in
  pp_type ppf etype
;;

let pp_solution ?effannot = pp_list (pp_pair pp_tvar (pp_type ?effannot))

let pp_lit ppf = function
  | LitUnit -> Format.fprintf ppf "()"
  | LitInt i -> if i < 0 then Format.fprintf ppf "(%d)" i else Format.fprintf ppf "%d" i
  | LitFloat f ->
    if f <= 0. then Format.fprintf ppf "(%F)" f else Format.fprintf ppf "%F" f
  (* We want parentheses when f equals (-0.);
      Without parentheses -0. is interpreted as an arithmetic operation function. *)
  | LitBool b -> Format.fprintf ppf "%B" b
  | LitStr s -> Format.fprintf ppf "%S" s
;;

let pp_constructor_args ~one:pp_one ~several:pp_several ppf = function
  | [] -> ()
  | [ arg ] -> Format.fprintf ppf "@ %a" pp_one arg
  | arg_list ->
    let pp_sep ppf () = Format.fprintf ppf ",@ " in
    Format.fprintf
      ppf
      "@ (@[<hov>%a@])"
      (Format.pp_print_list ~pp_sep pp_several)
      arg_list
;;

let pp_pattern ppf pat =
  let rec pp_pattern ppf = function
    | PattConstr (_typ, name, patt_lst) ->
      Format.fprintf
        ppf
        "%s%a"
        name
        (pp_constructor_args ~one:pp_simple_pattern ~several:pp_pattern)
        patt_lst
    | PattVar _ as simple -> pp_simple_pattern ppf simple
  and pp_simple_pattern ppf = function
    | PattVar v -> pp_var ppf v
    | non_simple -> Format.fprintf ppf "(%a)" pp_pattern non_simple
  in
  pp_pattern ppf pat
;;

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
let pp_term ?(typeannot = true) ppf term =
  let rec pp_exp ppf t =
    let pp_binder ppf (x, t) =
      if typeannot
      then Format.fprintf ppf "(%s: %a)" x (pp_type ~effannot:false) t
      else Format.fprintf ppf "%s" x
    in
    match t with
    | Constructor (_, name, args, _) ->
      Format.fprintf
        ppf
        "@[<2>%s%a@]"
        name
        (pp_constructor_args ~one:pp_arg ~several:pp_app)
        args
    | PatternMatch (_, match_trm, branches, _) ->
      let pp_case ppf (pattern, body) =
        Format.fprintf ppf "@;| @[<2>%a@ ->@ %a@]" pp_pattern pattern pp_arg body
        (* we use pp_arg to ensure that inner 'match' expressions get parenthesized,
           to avoid incorrect-precedence cases such as
             match x with
             | None ->
               match y with
               | None -> ()
               | Some _ -> ()
             | Some _ -> (* captured by 'match y' above *)
         *)
      in
      Format.fprintf
        ppf
        "@[<hv>@[@[<2>match@ %a@]@ with@]%a@]"
        pp_exp
        match_trm
        (Format.pp_print_list pp_case)
        branches
    | Lambda (_, x, t, m) ->
      Format.fprintf ppf "@[<2>fun %a ->@ %a@]" pp_binder (x, t) pp_exp m
    | Let (x, t, m, n, _, _) ->
      Format.fprintf
        ppf
        "@[<2>@[<hv2>let %a =@ %a@]@;<1 -2>in %a@]"
        pp_binder
        (x, t)
        pp_exp
        m
        pp_exp
        n
    | If (_, b, m, n, _) ->
      Format.fprintf
        ppf
        "@[<2>if %a@;<1 -2>then %a@;<1 -2>else %a@]"
        pp_exp
        b
        pp_exp
        m
        pp_exp
        n
    | Lit _ | Variable _ | ListTrm _ | App _ -> pp_app ppf t
  and pp_app ppf t =
    let below = pp_arg in
    let rec self ppf = function
      | App (_, m, _, n, _) -> Format.fprintf ppf "%a@ %a" self m below n
      | t -> below ppf t
    in
    Format.fprintf ppf "@[<2>%a@]" self t
  and pp_arg ppf t =
    match t with
    | Lit l -> pp_lit ppf l
    | Variable (_, s) -> pp_var ppf s
    | ListTrm (_, ls, _) ->
      let pp_sep ppf () = Format.fprintf ppf ";@ " in
      Format.fprintf ppf "[@[<hv>%a@]]" (Format.pp_print_list ~pp_sep pp_app) ls
    | _ -> Format.fprintf ppf "(%a)" pp_exp t
  in
  pp_exp ppf term
;;
