(* *************************************************************** *)
(* OCaml compiler backend tester                                   *)
(* Initial version by Patrick Kasting and Mathias Nygaard Justesen *)
(* Type and effect extension by Jan Midtgaard                      *)
(* *************************************************************** *)

open QCheck
open Effast
open Effprint
open Effunif
open Effenv

(** Helpers *)

let make_logger file_path =
  let file_out = open_out file_path in
  let counter = ref 0 in
  fun fmt ->
    incr counter;
    Printf.fprintf file_out ("(* %d *) " ^^ fmt ^^ ";;\n%!") !counter
;;

let no_logger = Printf.ifprintf stdout

(** Compilation *)

(* Write OCaml source to file *)
let write_prog src filename =
  let ostr = open_out filename in
  let () = output_string ostr src in
  close_out ostr
;;

let run srcfile compil_filename compil_comm =
  let exefile = "generated_tests/" ^ compil_filename in
  let exitcode = Sys.command (compil_comm ^ " " ^ srcfile ^ " -o " ^ exefile) in
  (* Check that compilation was successful *)
  if exitcode <> 0
  then
    failwith
      (compil_filename ^ " compilation failed with error code " ^ string_of_int exitcode)
  else (
    (* Run the compiled program *)
    let runcode = Sys.command ("./" ^ exefile ^ " >" ^ exefile ^ ".out 2>&1") in
    (runcode, exefile ^ ".out"))
;;

let is_native_byte_equiv (*printFunction*) src =
  (* Write OCaml source to file *)
  let file = "generated_tests/test.ml" in
  let () = write_prog src file in
  let ncode, nout = run file "native" "ocamlopt -O3 -w -5-26" in
  (* -w -5@20-26 *)
  (* Silence warnings for partial applications and unused variables *)
  let bcode, bout = run file "byte" "ocamlc -w -5-26" in
  let comp = Sys.command ("diff -q " ^ nout ^ " " ^ bout ^ " > /dev/null") in
  ncode = bcode && comp = 0
;;

let print_wrap t =
  Let
    ( "i",
      Int,
      t,
      App
        ( Unit,
          Variable (Fun (Int, (true, false), Unit), "print_int"),
          Int,
          Variable (Int, "i"),
          (true, false) ),
      Unit,
      (true, false) )
;;

let printer_by_etype typ =
  let fun_name, printer_typ_opt =
    match typ with
    | Int -> ("print_int", lookup_var "print_int" init_tri_env)
    | Float -> ("print_float", lookup_var "print_float" init_tri_env)
    | String -> ("print_string", lookup_var "print_string" init_tri_env)
    | Unit | Typevar _ | Option _ | Ref _ | List _ | Fun _ | Bool ->
      failwith
        "printer_by_etype: such base type should not be generated (not implemented)"
  in
  match printer_typ_opt with
  | Some typ -> Variable (typ, fun_name)
  | None -> failwith "printer_by_etype: printer for this type is unavailable."
;;

let rand_print_wrap typ trm =
  Let
    ( "x",
      typ,
      trm,
      App (Unit, printer_by_etype typ, typ, Variable (typ, "x"), (true, false)),
      Unit,
      (true, false) )
;;

module Arbitrary = struct
  open Effgen

  (* TODO: Is it correct to name a function using suffix `_gen`
          if it is of type `'a arbitrary`
  *)
  let term_gen_by_type typ =
    make
      ~print:(Print.option (str_of_pp (pp_term ~typeannot:false)))
      ~shrink:Effshrink.shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.term_gen typ (true, false) rs)
  ;;

  let int_term_gen = term_gen_by_type Int

  let arb_type =
    make
      ~print:(str_of_pp pp_type)
      Gen.(
        frequency
          [ (1, map (fun i -> Typevar i) (oneofl [ 1; 2; 3; 4; 5 ]));
            (6, sized StaticGenerators.type_gen)
          ])
  ;;

  (* Arbitrary type-dependent term generator - both the term and its type are generated by
  the same random seed *)
  let arb_dep_term_with_cache =
    make
      ~print:
        (let printer (_typ, trm) = str_of_pp (pp_term ~typeannot:false) trm in
         Print.option printer)
      ~shrink:Effshrink.wrapped_dep_term_shrinker
      (fun rs ->
        let module Gener = GeneratorsWithContext (FreshContext ()) in
        Gener.dep_term_gen rs)
  ;;
end

let unify_funtest =
  Test.make
    ~count:1000
    ~name:"unify functional"
    (pair Arbitrary.arb_type Arbitrary.arb_type)
    (fun (ty, ty') ->
      match unify ty ty' with
      | No_sol -> ty <> ty'
      | Sol t ->
        let sty = subst t ty in
        let sty' = subst t ty' in
        types_compat sty sty' || types_compat sty' sty)
;;

(** Tests *)

(* FIXME: update to arb_dep_term *)
let gen_classify =
  Test.make
    ~count:1000
    ~name:"classify gen"
    (make
       ~collect:(fun t -> if t = None then "None" else "Some")
       (gen Arbitrary.int_term_gen))
    (fun _ -> true)
;;

let can_compile_test ~with_logging =
  let logger =
    if not with_logging
    then no_logger
    else make_logger "generated_tests/ocamltestml_log.ml"
  in
  let prgm_filename = "generated_tests/ocamltest.ml" in
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"generated term passes OCaml's typecheck"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None ->
        logger "%s" "failwith(\"dep_t_opt = None\")";
        false
      | Some (_typ, trm) ->
        (try
           let generated_prgm = str_of_pp pp_term trm in
           logger "%s" generated_prgm;
           write_prog generated_prgm prgm_filename;
           0 = Sys.command ("ocamlc -w -5@20-26 " ^ prgm_filename)
         with _ -> false))
;;

let type_check_test =
  Test.make
    ~count:500
    ~name:"generated term type checks"
    Arbitrary.arb_dep_term_with_cache
    (fun t_opt ->
      t_opt
      <> None
      ==>
      match t_opt with
      | None -> false
      | Some (typ, trm) ->
        let env, _, _ = init_tri_env in
        let typ', eff = Effcheck.tcheck env trm in
        types_compat typ typ' && eff_leq eff (true, false))
;;

let int_eq_test =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - int_eq_test"
    Arbitrary.int_term_gen
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (str_of_pp pp_term (print_wrap t)))
;;

let rand_eq_test typ =
  Test.make
    ~count:500
    ~name:"bytecode/native backends agree - term gen by given type"
    (Arbitrary.term_gen_by_type typ)
    (fun topt ->
      topt
      <> None
      ==>
      match topt with
      | None -> false
      | Some t -> is_native_byte_equiv (str_of_pp pp_term (rand_print_wrap typ t)))
;;

let dep_eq_test ~with_logging =
  let logger =
    if not with_logging then no_logger else make_logger "generated_tests/testml_log.ml"
  in
  Test.make
    ~count:500
    ~long_factor:10
    ~name:"bytecode/native backends agree - type-dependent term generator"
    Arbitrary.arb_dep_term_with_cache
    (fun dep_t_opt ->
      dep_t_opt
      <> None
      ==>
      match dep_t_opt with
      | None ->
        logger "%s" "failwith(\"dep_t_opt = None\")";
        false
      | Some (typ, trm) ->
        let generated_prgm = rand_print_wrap typ trm |> str_of_pp pp_term in
        logger "%s" generated_prgm;
        is_native_byte_equiv generated_prgm)
;;

(* The actual call to QCheck_runner.run_tests_main is located in effmain.ml *)
