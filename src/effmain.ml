open Effast
open Efftester

let () =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests_main [ dep_eq_test ~with_logging:true ]
;;
