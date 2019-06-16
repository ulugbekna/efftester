open Efftester

let _ =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests
    ~colors:true
    ~verbose:true
    (* [ unify_funtest; gen_classify; ocaml_test; tcheck_test; rand_eq_test ] *)
    [ can_compile_test ]
;;
