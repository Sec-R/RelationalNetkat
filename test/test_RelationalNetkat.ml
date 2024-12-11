open OUnit2
open RelationalNetkat

(*let print_sat l =
  let open MLBDD in
  let first = ref true in
  List.iter (fun (b,v) ->
      if !first then first := false
      else print_string ", ";
      if not b then print_string "~";
      print_int v;
    ) l;
  print_endline ""*)

let tests = "MLBDD tests" >::: [
      "var_test" >:: (fun _ctx ->
      let man = RN.init_man 10 10 in
      let var_a  = RN.bddvar man 1 0 in  
      let var_b  = RN.bddvar man 1 1 in  
      assert_equal ~cmp:(fun a b -> a = b) var_a 1;
      assert_equal ~cmp:(fun a b -> a = b) var_b 6;
      );
      "compile_pred_test" >:: (fun _ctx ->
        let man = RN.init_man 10 10 in
        let pk1 = 0 in
        let bdd1 = RN.compile_pred_bdd man pk1 RN.True in
        let bdd2 = RN.compile_pred_bdd man pk1 (RN.Neg (RN.False)) in
        assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
        let bdd3 = RN.compile_pred_bdd man pk1 (RN.Test (1, true)) in
        let bdd4 = RN.compile_pred_bdd man pk1 (RN.Neg (RN.Test (1, false))) in
        assert_equal ~cmp:MLBDD.equal bdd3 bdd4;
        let pred_and = RN.And (RN.Test (1, true), RN.Test (2, false)) in
        let bdd5 = RN.compile_pred_bdd man pk1 pred_and in
        let expected_and =
          MLBDD.dand
            (RN.compile_pred_bdd man pk1 (RN.Test (1, true)))
            (RN.compile_pred_bdd man pk1 (RN.Test (2, false)))
        in
        assert_equal ~cmp:MLBDD.equal bdd5 expected_and;
        let pred_or = RN.OrP (RN.Test (1, true), RN.Test (2, false)) in
        let bdd6 = RN.compile_pred_bdd man pk1 pred_or in
        let expected_or =
          MLBDD.dor
            (RN.compile_pred_bdd man pk1 (RN.Test (1, true)))
            (RN.compile_pred_bdd man pk1 (RN.Test (2, false)))
        in
        assert_equal ~cmp:MLBDD.equal bdd6 expected_or;
        let complex_pred =
          RN.And (
            RN.OrP (RN.Test (1, true), RN.Test (2, false)),
            RN.Neg (RN.Test (3, true))
          )
        in
        let bdd7 = RN.compile_pred_bdd man pk1 complex_pred in
        let expected_complex =
          MLBDD.dand
            (MLBDD.dor
               (RN.compile_pred_bdd man pk1 (RN.Test (1, true)))
               (RN.compile_pred_bdd man pk1 (RN.Test (2, false))))
            (MLBDD.dnot (RN.compile_pred_bdd man pk1 (RN.Test (3, true))))
        in
        assert_equal ~cmp:MLBDD.equal bdd7 expected_complex;
      );
      "compile_pkr_test" >:: (fun _ctx ->
        let man = RN.init_man 10 10 in
        let pk1 = 0 in
        let pk2 = 1 in
        let pk3 = RN.generate_unused_pk pk1 pk2 in
        let bdd1 = RN.compile_pkr_bdd man pk1 pk2 RN.Id in
        let bdd2 = (MLBDD.exists (RN.generate_support man pk3) (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk3 RN.Id)
        (RN.compile_pkr_bdd man pk3 pk2 RN.Id))) in
        assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
        let bdd3 = RN.compile_pkr_bdd man pk1 pk1 RN.Id in
        assert_equal ~cmp:MLBDD.equal bdd3 (RN.bdd_true man);
        let bdd4 = RN.compile_pkr_bdd man pk1 pk2 RN.Empty in
        assert_equal ~cmp:MLBDD.equal bdd4 (RN.bdd_false man);
        let bdd5 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftTest (1, true)) in
        let bdd6 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Id,RN.LeftTest (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd5 bdd6;
        let bdd7 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftTest (1, true),RN.LeftTest (2, true))) in
        let bdd8 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftTest (2, true),RN.LeftTest (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd7 bdd8;
        let bdd9 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftTest (1, true),RN.LeftTest (1, false))) in
        assert_equal ~cmp:MLBDD.equal bdd9 (RN.bdd_false man);
        let bdd10 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftTest (1, true),RN.LeftAsgn (1, true))) in
        let bdd11 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
        let bdd12 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.LeftTest (1, true))) in
        let bdd13 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftTest (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd12 bdd13;
        let bdd14 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightTest (1, true),RN.RightAsgn (1, true))) in
        let bdd15 = RN.compile_pkr_bdd man pk1 pk2 (RN.RightTest (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd14 bdd15;
        let bdd16 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.RightTest (1, true))) in
        let bdd17 = RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd16 bdd17;
        let bdd18 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (1, true))) in
        let bdd19 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftTest (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd18 bdd19;
        let bdd20 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.Or (RN.LeftAsgn (1, true),RN.LeftTest (2, true))),RN.RightAsgn (3, true))) in
        let bdd21 = RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (3, true)),RN.Comp(RN.LeftTest (2, true),RN.RightAsgn (3, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd20 bdd21;
        let bdd22 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.RightAsgn (3, true)),(RN.Or (RN.LeftAsgn (1, true),RN.LeftTest (2, true))))) in
        let bdd23 = RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.Comp (RN.RightAsgn (3, true),RN.LeftAsgn (1, true)),RN.Comp(RN.RightAsgn (3, true),RN.LeftTest (2, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd22 bdd23;
      );
      "compile_delta_k_test" >:: (fun _ctx ->
        let man = RN.init_man 10 10 in
        let pk1 = 0 in
        let pk2 = 1 in
        let compare = RN.NKOMap.equal MLBDD.equal in
        let nkomap1 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star (RN.NK.Pred (RN.True)))) in
        let nkomap2 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 RN.Id) in
        assert_equal ~cmp:compare nkomap1 nkomap2;
        let nkomap3 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star RN.NK.Dup)) in
        let nkomap4 = RN.add_nko_mapping (Some (RN.NK.Seq (Pred True, RN.NK.Star RN.NK.Dup)))
          (RN.produce_id man pk1 pk2) nkomap2 in
        assert_equal ~cmp:compare nkomap3 nkomap4;
        let nkomap5 = RN.delta_k man pk1 pk2 (Some (RN.NK.Seq (Asgn (1,true), RN.NK.Dup))) in
        let nkomap6 = RN.NKOMap.singleton (Some (Pred True)) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) in
        assert_equal ~cmp:compare nkomap5 nkomap6;
        let nkomap7 = RN.delta_k man pk1 pk2 (Some (RN.NK.Seq (Asgn (1,true), Asgn (2,true)))) in
        let nkomap8 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap7 nkomap8;
        let nkomap9 = RN.delta_k man pk1 pk2 (Some (RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add (Asgn (2,true)) RN.SNK.empty)))) in
        let nkomap10 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap9 nkomap10;
        let nkomap11 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add (Asgn (2,true)) RN.SNK.empty))))) in
        let nkomap12 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Or (RN.RightAsgn (1, true),RN.Id),(RN.Or (RN.RightAsgn (2, true),RN.Id))))) in
        assert_equal ~cmp:compare nkomap11 nkomap12;
        let nkomap13 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty))))) in
        let nkomap14 = RN.add_nko_mapping 
          (Some (RN.NK.Seq (Pred True, RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty)))))) 
          (RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.RightAsgn (1, true),RN.Id))) 
          (RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.RightAsgn (1, true),RN.Id)))) in
        assert_equal ~cmp:compare nkomap13 nkomap14;
        let nkomap15 = RN.delta_k man pk1 pk2 (Some (RN.NK.Seq (Asgn (1,true), RN.NK.Seq (Asgn (2,true),RN.NK.Dup)))) in
        let nkomap16 = RN.NKOMap.singleton (Some (Pred True)) (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap15 nkomap16;
      );
      "epsilon_kr_test" >:: (fun _ctx ->
        let man = RN.init_man 10 10 in
        let pk1 = 0 in
        let pk2 = 1 in
        let compare = RN.NKROMap.equal MLBDD.equal in
        let nkromap1 = RN.epsilon_kr man pk1 pk2 (None, None) in
        let nkromap2 = RN.NKROMap.singleton (None,None) (RN.produce_id man pk1 pk2) in
        assert_equal ~cmp:compare nkromap1 nkromap2;
        let nkromap3 = RN.epsilon_kr man pk1 pk2 ((Some (Pred True)), Some (RN.Rel.Left RN.Id)) in
        let nkromap4 = RN.add_nkro_mapping (None,None) (RN.produce_id man pk1 pk2)
        (RN.NKROMap.singleton ((Some (Pred True)), Some (RN.Rel.Left RN.Id)) (RN.produce_id man pk1 pk2)) in
        assert_equal ~cmp:compare nkromap3 nkromap4;
        let nkromap5 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.Left RN.Id)) in
        let nkromap6 = RN.add_nkro_mapping ((Some (Pred True)),None) (RN.produce_id man pk1 pk2)
        (RN.NKROMap.singleton ((Some RN.NK.Dup), Some (RN.Rel.Left RN.Id)) (RN.produce_id man pk1 pk2)) in
        assert_equal ~cmp:compare nkromap5 nkromap6;
        let nkromap7 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left RN.Id, RN.Rel.Left RN.Id))) in
        let nkromap8 = RN.add_nkro_mapping (None,None) (RN.produce_id man pk1 pk2)
          (RN.add_nkro_mapping ((Some (Pred True)),Some (RN.Rel.Left RN.Id)) (RN.produce_id man pk1 pk2)
        (RN.NKROMap.singleton ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left RN.Id, RN.Rel.Left RN.Id))) (RN.produce_id man pk1 pk2))) in
        assert_equal ~cmp:compare nkromap7 nkromap8;
        let nkromap9 = RN.epsilon_kr man pk1 pk2 (Some (RN.NK.Asgn (1,true)), Some (RN.Rel.Left (RN.RightAsgn (2,true)))) in
        let nkromap10 = RN.add_nkro_mapping (None,None) 
        (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftTest(1,true),RN.LeftTest(2,true))))
        (RN.NKROMap.singleton (Some (RN.NK.Asgn (1,true)), Some (RN.Rel.Left (RN.RightAsgn (2,true)))) (RN.produce_id man pk1 pk2)) in
        assert_equal ~cmp:compare nkromap9 nkromap10;
        let nkromap11 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.RightAsgn (1,true)), RN.Rel.Left (RN.RightAsgn (2,true))))) in
        let nkromap12 = RN.add_nkro_mapping (None,None)  (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightTest(1,true),RN.RightTest(2,true))))
          (RN.add_nkro_mapping ((Some (Pred True)),Some (RN.Rel.Left (RN.RightAsgn (2,true)))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightTest(1,true)))
        (RN.NKROMap.singleton ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.RightAsgn (1,true)), RN.Rel.Left (RN.RightAsgn (2,true))))) (RN.produce_id man pk1 pk2))) in
        assert_equal ~cmp:compare nkromap11 nkromap12;
        let nkromap13 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Left RN.Id))) in
        print_endline (RN.nkro_map_to_string nkromap13);
      );

      ]

let _ =
  run_test_tt_main begin "all" >::: [
      tests;
    ] end