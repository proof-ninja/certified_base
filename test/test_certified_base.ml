(* Where Certified_base's API overlaps with Jane Street's [base], check that
   both agree on the same inputs. Everything else is checked standalone. *)

module CFn = Certified_base.Fn
module CUnit = Certified_base.Unit
module CResult = Certified_base.Result
module CSign = Certified_base.Sign
module CList = Certified_base.List
module COption = Certified_base.Option

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

let test_list () =
  let l = [ 1; 2; 3 ] in
  assert (CList.is_empty ([] : int list) = true);
  assert (CList.is_empty l = false);
  assert (CList.length l = Base.List.length l);
  assert (CList.append l [ 4; 5 ] = Base.List.append l [ 4; 5 ]);
  assert (CList.rev l = Base.List.rev l);
  assert (CList.concat [ l; [ 4 ] ] = Base.List.concat [ l; [ 4 ] ]);
  assert (CList.map (( + ) 1) l = Base.List.map l ~f:(( + ) 1));
  assert (CList.filter (fun x -> x > 1) l = Base.List.filter l ~f:(fun x -> x > 1));
  assert (CList.exists_ (fun x -> x = 2) l = Base.List.exists l ~f:(fun x -> x = 2));
  assert (CList.for_all (fun x -> x > 0) l = Base.List.for_all l ~f:(fun x -> x > 0));
  assert (CList.fold l 0 ( + ) = Base.List.fold l ~init:0 ~f:( + ));
  assert (CList.mem Int.equal 2 l = Base.List.mem l 2 ~equal:Int.equal);
  assert (CList.find (fun x -> x > 1) l = Base.List.find l ~f:(fun x -> x > 1));
  assert (CList.hd l = Base.List.hd l);
  assert (CList.tl l = Base.List.tl l);
  assert (CList.nth l 1 = Base.List.nth l 1);
  assert (CList.init 3 (fun i -> i * i) = Base.List.init 3 ~f:(fun i -> i * i));
  assert (CList.return_ 1 = Base.List.return 1);
  assert (CList.bind [ 1; 2 ] (fun x -> [ x; x ]) = Base.List.bind [ 1; 2 ] ~f:(fun x -> [ x; x ]));
  assert (CList.count (fun x -> x > 1) l = Base.List.count l ~f:(fun x -> x > 1));
  assert (CList.rev_append l [ 4; 5 ] = Base.List.rev_append l [ 4; 5 ]);
  assert (CList.equal Int.equal l [ 1; 2; 3 ] = Base.List.equal Int.equal l [ 1; 2; 3 ]);
  assert (CList.equal Int.equal l [ 1; 2 ] = Base.List.equal Int.equal l [ 1; 2 ]);
  assert (
    CList.compare Int.compare l [ 1; 3 ] = Base.List.compare Int.compare l [ 1; 3 ]);
  assert (CList.compare Int.compare l l = Base.List.compare Int.compare l l);
  let r1 = ref 0 and r2 = ref 0 in
  CList.iter (fun x -> r1 := !r1 + x) l;
  Base.List.iter l ~f:(fun x -> r2 := !r2 + x);
  assert (!r1 = !r2);
  assert (CList.mapi (fun i x -> i + x) l = Base.List.mapi l ~f:(fun i x -> i + x));
  let r3 = ref 0 and r4 = ref 0 in
  CList.iteri (fun i x -> r3 := !r3 + i + x) l;
  Base.List.iteri l ~f:(fun i x -> r4 := !r4 + i + x);
  assert (!r3 = !r4);
  assert (
    CList.existsi (fun i x -> i = x) l = Base.List.existsi l ~f:(fun i x -> i = x));
  assert (
    CList.for_alli (fun _ x -> x > 0) l = Base.List.for_alli l ~f:(fun _ x -> x > 0));
  assert (
    CList.findi (fun _ x -> x = 2) l = Base.List.findi l ~f:(fun _ x -> x = 2));
  assert (CList.take l 2 = Base.List.take l 2);
  assert (CList.drop l 2 = Base.List.drop l 2);
  assert (
    CList.take_while (fun x -> x < 2) l = Base.List.take_while l ~f:(fun x -> x < 2));
  assert (
    CList.drop_while (fun x -> x < 2) l = Base.List.drop_while l ~f:(fun x -> x < 2));
  assert (CList.last l = Base.List.last l);
  assert (CList.cons 1 [ 2; 3 ] = Base.List.cons 1 [ 2; 3 ]);
  assert (CList.sub [ 1; 2; 3; 4 ] 1 2 = Base.List.sub [ 1; 2; 3; 4 ] ~pos:1 ~len:2);
  assert (CList.unzip [ (1, "a"); (2, "b") ] = Base.List.unzip [ (1, "a"); (2, "b") ]);
  assert (
    CList.zip [ 1; 2 ] [ 3; 4 ]
    = (match Base.List.zip [ 1; 2 ] [ 3; 4 ] with Ok l -> Some l | Unequal_lengths -> None));
  assert (CList.zip [ 1; 2 ] [ 3 ] = None);
  assert (
    CList.partition_tf (fun x -> x > 1) l
    = Base.List.partition_tf l ~f:(fun x -> x > 1))

let test_option () =
  assert (COption.is_none None = Base.Option.is_none None);
  assert (COption.is_some (Some 1) = Base.Option.is_some (Some 1));
  assert (COption.value (Some 1) 0 = Base.Option.value (Some 1) ~default:0);
  assert (COption.value None 0 = Base.Option.value None ~default:0);
  assert (COption.map (( + ) 1) (Some 1) = Base.Option.map (Some 1) ~f:(( + ) 1));
  assert (COption.return_ 1 = Base.Option.return 1);
  assert (
    COption.bind (Some 1) (fun x -> Some (x + 1))
    = Base.Option.bind (Some 1) ~f:(fun x -> Some (x + 1)));
  let r1 = ref 0 and r2 = ref 0 in
  COption.iter (Some 5) (fun x -> r1 := x);
  Base.Option.iter (Some 5) ~f:(fun x -> r2 := x);
  assert (!r1 = !r2);
  assert (COption.exists_ (fun x -> x > 1) (Some 2) = Base.Option.exists (Some 2) ~f:(fun x -> x > 1));
  assert (COption.for_all (fun x -> x > 1) None = Base.Option.for_all None ~f:(fun x -> x > 1));
  assert (COption.find (fun x -> x > 1) (Some 2) = Base.Option.find (Some 2) ~f:(fun x -> x > 1));
  assert (COption.filter (fun x -> x > 1) (Some 2) = Base.Option.filter (Some 2) ~f:(fun x -> x > 1));
  assert (COption.first_some None (Some 3) = Base.Option.first_some None (Some 3));
  assert (
    COption.merge (Some 1) (Some 2) ( + ) = Base.Option.merge (Some 1) (Some 2) ~f:( + ));
  assert (COption.equal Int.equal (Some 1) (Some 1) = Base.Option.equal Int.equal (Some 1) (Some 1));
  assert (
    COption.compare Int.compare (Some 1) (Some 2)
    = Base.Option.compare Int.compare (Some 1) (Some 2));
  assert (COption.compare Int.compare None (Some 2) = Base.Option.compare Int.compare None (Some 2));
  assert (COption.compare Int.compare (Some 1) None = Base.Option.compare Int.compare (Some 1) None);
  assert (COption.compare Int.compare None None = Base.Option.compare Int.compare None None);
  assert (
    COption.value_map (Some 1) 0 (( + ) 1) = Base.Option.value_map (Some 1) ~default:0 ~f:(( + ) 1));
  assert (COption.value_map None 0 (( + ) 1) = Base.Option.value_map None ~default:0 ~f:(( + ) 1));
  assert (
    COption.value_or_thunk None (fun () -> 5)
    = Base.Option.value_or_thunk None ~default:(fun () -> 5));
  assert (COption.fold (Some 1) 0 ( + ) = Base.Option.fold (Some 1) ~init:0 ~f:( + ));
  assert (COption.mem Int.equal 1 (Some 1) = Base.Option.mem (Some 1) 1 ~equal:Int.equal);
  assert (COption.length (Some 1) = Base.Option.length (Some 1));
  assert (COption.length None = Base.Option.length None);
  assert (
    COption.find_map (fun x -> if x > 0 then Some (x + 1) else None) (Some 1)
    = Base.Option.find_map (Some 1) ~f:(fun x -> if x > 0 then Some (x + 1) else None));
  assert (COption.to_list (Some 1) = Base.Option.to_list (Some 1));
  assert (COption.to_list (None : int COption.t) = Base.Option.to_list None);
  let r3 = ref 0 and r4 = ref 0 in
  COption.call 5 (Some (fun x -> r3 := x));
  Base.Option.call 5 ~f:(Some (fun x -> r4 := x));
  assert (!r3 = !r4);
  assert (COption.some 1 = Base.Option.some 1);
  assert (COption.some_if true 1 = Base.Option.some_if true 1);
  assert (COption.some_if false 1 = Base.Option.some_if false 1);
  assert (COption.map2 ( + ) (Some 1) (Some 2) = Base.Option.map2 (Some 1) (Some 2) ~f:( + ));
  assert (COption.both (Some 1) (Some 2) = Base.Option.both (Some 1) (Some 2));
  assert (
    COption.apply (Some (( + ) 1)) (Some 1) = Base.Option.apply (Some (( + ) 1)) (Some 1))

let () =
  test_fn ();
  test_unit ();
  test_result ();
  test_sign ();
  test_list ();
  test_option ();
  print_endline "all tests passed"
