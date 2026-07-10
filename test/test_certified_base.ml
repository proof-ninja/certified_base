(* Where Certified_base's API overlaps with Jane Street's [base], check that
   both agree on the same inputs. Everything else is checked standalone. *)

module CFn = Certified_base.Fn
module CUnit = Certified_base.Unit
module CResult = Certified_base.Result
module CSign = Certified_base.Sign

let test_fn () =
  assert (CFn.id 42 = Base.Fn.id 42);
  assert (CFn.id "hi" = Base.Fn.id "hi");
  assert (CFn.const 1 "ignored" = Base.Fn.const 1 "ignored");
  assert (CFn.compose (( + ) 1) (( * ) 2) 10 = Base.Fn.compose (( + ) 1) (( * ) 2) 10);
  assert (CFn.flip ( - ) 3 10 = Base.Fn.flip ( - ) 3 10);
  assert (CFn.non (fun x -> x > 0) 5 = Base.Fn.non (fun x -> x > 0) 5);
  assert (CFn.non (fun x -> x > 0) (-5) = Base.Fn.non (fun x -> x > 0) (-5));
  assert (
    CFn.apply_n_times 5 (( + ) 1) 0 = Base.Fn.apply_n_times ~n:5 (( + ) 1) 0);
  CFn.ignore 42;
  Base.Fn.ignore 42;
  (* [pipe] has no Base.Fn equivalent (Base uses the [|>] operator instead). *)
  assert (CFn.pipe 41 (( + ) 1) = 42)

let test_unit () =
  assert (CUnit.equal () () = Base.Unit.equal () ());
  assert (CUnit.compare () () = Base.Unit.compare () ());
  assert (List.length CUnit.all = List.length Base.Unit.all)

let test_result () =
  assert (CResult.return_ 1 = Base.Result.return 1);
  assert (
    CResult.bind (Ok 1) (fun x -> Ok (x + 1))
    = Base.Result.bind (Ok 1) ~f:(fun x -> Ok (x + 1)));
  assert (
    CResult.bind (Error "e") (fun x -> Ok (x + 1))
    = Base.Result.bind (Error "e") ~f:(fun x -> Ok (x + 1)));
  assert (CResult.map (( + ) 1) (Ok 1) = Base.Result.map (Ok 1) ~f:(( + ) 1));
  assert (
    CResult.map_error String.uppercase_ascii (Error "e")
    = Base.Result.map_error (Error "e") ~f:String.uppercase_ascii);
  assert (CResult.is_ok (Ok 1) = Base.Result.is_ok (Ok 1));
  assert (CResult.is_error (Error "e") = Base.Result.is_error (Error "e"));
  assert (CResult.ok (Ok 1) = Base.Result.ok (Ok 1));
  assert (CResult.error (Error "e") = Base.Result.error (Error "e"));
  (* [value] has no Base.Result equivalent by that name. *)
  assert (CResult.value (Ok 1) 0 = 1);
  assert (CResult.value (Error "e") 0 = 0)

let test_sign () =
  assert (List.length CSign.all = List.length Base.Sign.all);
  List.iter
    (fun s ->
      let base_of = function
        | CSign.Neg -> Base.Sign.Neg
        | CSign.Zero -> Base.Sign.Zero
        | CSign.Pos -> Base.Sign.Pos
      in
      assert (base_of (CSign.flip s) = Base.Sign.flip (base_of s));
      List.iter
        (fun t ->
          assert (base_of (CSign.mult s t) = Base.Sign.( * ) (base_of s) (base_of t)))
        CSign.all)
    CSign.all;
  assert (CSign.equal CSign.Neg CSign.Neg = true);
  assert (CSign.equal CSign.Neg CSign.Pos = false)

let () =
  test_fn ();
  test_unit ();
  test_result ();
  test_sign ();
  print_endline "all tests passed"
