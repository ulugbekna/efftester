open Efftester

let _ =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests
    ~colors:true
    ~verbose:true
    [ dep_eq_test ]
;;
