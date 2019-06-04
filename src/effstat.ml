open QCheck
open Efftester

(** A classifier *)

let lit_size l =
  match l with
  | LitUnit | LitInt _ | LitFloat _ | LitBool _ | LitStr _ -> 1
  | LitList ls -> List.length ls
;;

let rec term_size e =
  match e with
  | Lit l -> lit_size l
  | Variable (_, _) -> 1
  | Lambda (_, _x, _, e) -> 1 + term_size e
  | App (_, e, _, e', _) -> 1 + term_size e + term_size e'
  | Let (_x, _, e, e', _, _) -> 1 + term_size e + term_size e'
  | If (_, e, e', e'', _) -> 1 + term_size e + term_size e' + term_size e''
;;

let coll_gen =
  set_collect
    (fun e ->
      match e with
      | None -> "0"
      | Some e -> string_of_int (term_size e))
    int_term_gen
;;

let coltest =
  Test.make ~count:50 (*1000*) coll_gen (fun _e ->
      print_char '.';
      flush stdout;
      true)
;;

let () =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests_main [ coltest ]
;;
