open Efftester

let () =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests_main
    (* [ unify_funtest; gen_classify; ocaml_test; tcheck_test; rand_eq_test ] *)
    [ type_check_test; can_compile_test ~with_logging:true ]
;;
