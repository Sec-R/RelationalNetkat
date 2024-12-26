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
        let bdd5 = RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)) in
        let bdd6 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Id,RN.Test (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd5 bdd6;
        let bdd7 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (1, true),RN.Test (2, true))) in
        let bdd8 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (2, true),RN.Test (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd7 bdd8;
        let bdd9 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (1, true),RN.Test (1, false))) in
        assert_equal ~cmp:MLBDD.equal bdd9 (RN.bdd_false man);
        let bdd10 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (1, true),RN.LeftAsgn (1, true))) in
        let bdd11 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
        let bdd12 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.Test (1, true))) in
        let bdd13 = RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd12 bdd13;
        let bdd14 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (1, true),RN.RightAsgn (1, true))) in
        let bdd15 = RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd14 bdd15;
        let bdd16 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.Test (1, true))) in
        let bdd17 = RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd16 bdd17;
        let bdd18 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (1, true))) in
        let bdd19 = RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd18 bdd19;
        let bdd20 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.Or (RN.LeftAsgn (1, true),RN.Test (2, true))),RN.RightAsgn (3, true))) in
        let bdd21 = RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (3, true)),RN.Comp(RN.Test (2, true),RN.RightAsgn (3, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd20 bdd21;
        let bdd22 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.RightAsgn (3, true)),(RN.Or (RN.LeftAsgn (1, true),RN.Test (2, true))))) in
        let bdd23 = RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.Comp (RN.RightAsgn (3, true),RN.LeftAsgn (1, true)),RN.Comp(RN.RightAsgn (3, true),RN.Test (2, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd22 bdd23;
        let bdd24 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test (1, true),RN.Test (2, true))) in
        let bdd25 = (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd24 bdd25;
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
        let nkromap4 = RN.NKROMap.singleton (None,None) (RN.produce_id man pk1 pk2) in
        assert_equal ~cmp:compare nkromap3 nkromap4;
        let nkromap5 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.Left RN.Id)) in
        let nkromap6 = RN.NKROMap.singleton ((Some (Pred True)),None) (RN.produce_id man pk1 pk2) in
        assert_equal ~cmp:compare nkromap5 nkromap6;
        let nkromap7 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left RN.Id, RN.Rel.Left RN.Id))) in
        let nkromap8 = RN.NKROMap.singleton (None,None) (RN.produce_id man pk1 pk2) in
        assert_equal ~cmp:compare nkromap7 nkromap8;
        let nkromap9 = RN.epsilon_kr man pk1 pk2 (Some (RN.NK.Asgn (1,true)), Some (RN.Rel.Left (RN.RightAsgn (2,true)))) in
        let nkromap10 = RN.NKROMap.singleton (None,None) 
        (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test(1,true),RN.Test(2,true)))) in
        assert_equal ~cmp:compare nkromap9 nkromap10;
        let nkromap11 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.RightAsgn (1,true)), RN.Rel.Left (RN.RightAsgn (2,true))))) in
        let nkromap12 = RN.NKROMap.singleton (None,None)  (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Test(1,true),RN.Test(2,true)))) in
        assert_equal ~cmp:compare nkromap11 nkromap12;
        let nkromap13 = RN.epsilon_kr man pk1 pk2 ((Some RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Left RN.Id))) in
        let bdd1 = RN.NKROMap.find (None, None) nkromap13 in
        let bdd2 = RN.NKROMap.find ((Some RN.NK.Dup), None) nkromap13 in
        let bdd3 = RN.NKROMap.find ((Some (Pred True)), None) nkromap13 in
        assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
        assert_equal ~cmp:MLBDD.equal bdd2 bdd3;
        assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk2);
        assert_equal (RN.NKROMap.cardinal nkromap13) 3;
        let nkromap14 = RN.epsilon_kr man pk1 pk2 ((Some (RN.NK.Star RN.NK.Dup)), Some (RN.Rel.StarR (RN.Rel.Left RN.Id))) in
        let bdd4 = RN.NKROMap.find (None, None) nkromap14 in
        let bdd5 = RN.NKROMap.find ((Some (RN.NK.Star RN.NK.Dup)), None) nkromap14 in
        assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
        assert_equal ~cmp:MLBDD.equal bdd5 (RN.produce_id man pk1 pk2);
        assert_equal (RN.NKROMap.cardinal nkromap14) 3; (* Substitute for (RN.NK.Star RN.NK.Dup)*)
        let nkromap15 = RN.epsilon_kr man pk1 pk2 ((Some (RN.NK.Star RN.NK.Dup)), Some (RN.Rel.SeqR ((RN.Rel.StarR (RN.Rel.Left RN.Id)),(RN.Rel.StarR (RN.Rel.Left RN.Id))))) in
        assert_equal (RN.NKROMap.cardinal nkromap15) 3; 
        (* 
          The Pairs now are 
          None, None
          Seq (Pred True, Star (Dup)), None
          Star (Dup), None    
        *)
        let nkromap16 = RN.epsilon_kr man pk1 pk2 (Some (RN.NK.Star RN.NK.Dup), 
          Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) RN.SR.empty))))) in
        let bdd6 = RN.NKROMap.find (None,None) nkromap16 in  
        let bdd7 = RN.compile_pkr_bdd man pk1 pk2 (RN.Or (RN.Test (1, true),RN.Test (2, true))) in
        let bdd8 = RN.NKROMap.find ((Some (RN.NK.Star RN.NK.Dup)),None) nkromap16 in
        let bdd9 = RN.NKROMap.find ((Some (RN.NK.Seq (Pred True, RN.NK.Star RN.NK.Dup))),None) nkromap16 in
        assert_equal ~cmp:MLBDD.equal bdd6 bdd7;
        assert_equal ~cmp:MLBDD.equal bdd8 (RN.produce_id man pk1 pk2);     
        assert_equal ~cmp:MLBDD.equal bdd6 bdd9;
        let nkromap17 = RN.epsilon_kr man pk1 pk2 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Right RN.Id))) in
        let bdd10 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap17 in
        assert_equal ~cmp:MLBDD.equal bdd10 (RN.produce_id man pk1 pk2);
        let nkromap17 = RN.epsilon_kr man pk1 pk2 (Some (RN.NK.Star RN.NK.Dup), 
        Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))) in
        let bdd11 = RN.NKROMap.find (None,None) nkromap17 in
        let bdd12 =  RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd11 bdd12;
        );
        "delta_kr_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let compare = RN.NKROMap.equal MLBDD.equal in
          let nkromap1 = RN.delta_kr man pk1 pk2 pk3 pk4 (None,None) in
          let nkromap2 = RN.NKROMap.empty in
          assert_equal ~cmp:compare nkromap1 nkromap2;
          let nkromap3 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup),None) in
          assert_equal ~cmp:compare nkromap2 nkromap3;
          let nkromap4 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Left RN.Id))) in
          assert_equal ~cmp:compare nkromap3 nkromap4; 
          let nkromap5 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Right RN.Id))) in
          let bdd1 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap5 in
          let bdd2 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.SeqR (RN.Rel.Right RN.Id,(RN.Rel.StarR (RN.Rel.Right RN.Id))))) nkromap5 in
          let bdd3 = (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          assert_equal ~cmp:MLBDD.equal bdd2 bdd3;
          let nkromap6 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
          Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))) in
          let bdd4 = RN.NKROMap.find (None,None) nkromap6 in
          let bdd5 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.Test (1, true)))) in
          let bdd6 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap6 in
          let bdd7 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.produce_id man pk1 pk2)) in
          assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
          assert_equal ~cmp:MLBDD.equal bdd6 bdd7;
          let nkromap7 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) RN.SR.empty))))) in
          assert_equal ~cmp:compare nkromap1 nkromap7;
          let nkromap8 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))) in
          let bdd8 = RN.NKROMap.find (None,None) nkromap8 in
          let bdd9 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)))) in
          assert_equal ~cmp:MLBDD.equal bdd8 bdd9;
        );
        "var_order_test" >:: (fun _ctx ->
          let man = RN.init_man 10 1 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let btree = MLBDD.inspectb (RN.produce_id man pk1 pk3) in
          match btree with
            | MLBDD.BTrue -> failwith "Wrong Inspection!"
            | MLBDD.BFalse -> failwith "Wrong Inspection!"
            | MLBDD.BIf (l,v,r) -> 
              let bdd1 = RN.var_if man v l r in
              assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk3);
          let bdd2 =  MLBDD.dand (RN.produce_id man pk1 pk3) (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (3, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.Test (2, true)))) in
          let bdd3 = RN.back_ordering man pk1 pk2 pk3 pk4 (RN.re_ordering man pk1 pk2 pk3 pk4 bdd2) in
          assert_equal ~cmp:MLBDD.equal bdd2 bdd3;
          );
        "calculate_reachable_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let nkromap1 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (RN.NK.Star RN.NK.Dup,RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty)))) in
          let bdd1 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))) nkromap1 in
          let bdd2 = RN.produce_id man pk1 pk3 in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          let nkromap2 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))) in
          let bdd3 = (MLBDD.dand bdd2 (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))))) in
          let support13 = RN.generate_double_support man pk1 pk3 in
          let bdd4 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd3))) in
          let bdd5 = RN.NKROMap.find (None,None) nkromap2 in
          assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
          let bdd6 = RN.NKROMap.find (None,Some (RN.Rel.SeqR (RN.Rel.Right (RightAsgn (2,true)), (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (1,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (2,true))) RN.SR.empty))))))) nkromap2 in
          let bdd7 =  (MLBDD.dand bdd2  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))))) in
          let bdd8 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd7))) in
          assert_equal ~cmp:MLBDD.equal bdd6 bdd8;
          let nkromap3 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let bdd9 = MLBDD.dand bdd2 (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (3, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.Test (2, true)))) in
          let bdd10 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd9))) in
          let bdd11 = RN.NKROMap.find (None,None) nkromap3 in
          assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
          let nkromap4 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 ((RN.NK.Seq (RN.NK.Asgn (1,true),(RN.NK.Star (RN.NK.Asgn (1,true))))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (Test (1,false))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          assert_equal (Option.is_none (RN.NKROMap.find_opt (None,None) nkromap4)) true;
        );
        "splitting_bdd_test" >:: (fun _ctx ->
          let man = RN.init_man 5 5 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let bdd1 = RN.produce_id man pk1 pk3 in
          let bdd2 = RN.BSet.choose (RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd1) in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          assert_equal (RN.BSet.cardinal (RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd1)) 1;
          let bdd3 = (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)))) in
          (*10 10 requires more than 30s to split it*)
          let bddset = RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd3 in
          let bdd4 = RN.BSet.fold (fun acc x -> MLBDD.dor acc x) bddset (RN.bdd_false man) in
          assert_equal ~cmp:MLBDD.equal bdd3 bdd4;
          assert_equal (RN.BSet.cardinal bddset) 16;
        );
        "transition_test" >:: (fun _ctx ->
          let man = RN.init_man 5 5 in
          (* 10 requires a lot of more time*)
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let nkrosmap1 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          assert_equal true (RN.NKROMap.mem (None,None) nkrosmap1); 
          (* Print to see*)
         (* print_endline (RN.transition_set_map_to_string nkrosmap1); *)   
          let nkrosmap2 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let nkromap1 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          RN.NKROMap.iter (fun nkro (bset,_) -> if RN.is_final nkro then assert_equal ~cmp:MLBDD.equal (RN.bdd_true man) (RN.BSet.choose bset)
                                                else assert_equal ~cmp:MLBDD.equal (RN.NKROMap.find nkro nkromap1) (MLBDD.dor (RN.NKROMap.find nkro nkromap1) (RN.BSet.fold (fun bdd acc -> MLBDD.dor bdd acc) bset (RN.bdd_false man)))
                                                ) nkrosmap2;
          (* Print to see*)
          (* Print_endline (RN.transition_set_map_to_string nkrosmap2); *)
          let nkrobmap1 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap1 in
          assert_equal false (RN.NKROBMap.mem ((None,None),RN.bdd_true man) nkrobmap1); 
          RN.NKROBMap.iter (fun (nkro,bdd) _ -> assert_equal true (RN.BSet.mem bdd (fst (RN.NKROMap.find nkro nkrosmap1)))) nkrobmap1;
          let nkrobmap2 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap2 in
          RN.NKROBMap.iter (fun (nkro,bdd) _ -> assert_equal true (RN.BSet.mem bdd (fst (RN.NKROMap.find nkro nkrosmap2)))) nkrobmap2;
          (* Print to see*)
           (* print_endline (RN.transition_map_to_string nkrobmap1);*)
          (* print_endline (RN.transition_map_to_string nkrobmap2); *)
        );
        "determinization_transition_test" >:: (fun _ctx ->
          let man = RN.init_man 5 5 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let map1 = RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk1 pk2) in
          let dmap1 = RN.determinize_transition map1 in
          let ((key1,flag1),bdd1) = RN.NKROBSMap.choose dmap1 in
          assert_equal ~cmp:RN.NKROBSet.equal key1 (RN.NKROBSet.singleton ((None,None),RN.bdd_false man));
          assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk2);
          assert_equal flag1 true;
          let map2 = RN.NKROBMap.add ((None,None),RN.bdd_true man) (RN.produce_id man pk1 pk2) map1 in
          let dmap2 = RN.determinize_transition map2 in
          let ((key2,flag2),bdd2) = RN.NKROBSMap.choose dmap2 in
          assert_equal ~cmp:RN.NKROBSet.equal key2 (RN.NKROBSet.add ((None,None),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man)));
          assert_equal ~cmp:MLBDD.equal bdd2 (RN.produce_id man pk1 pk2);
          assert_equal flag2 true;
          assert_equal (RN.NKROBSMap.cardinal dmap2) 1;
          let map3 = RN.NKROBMap.add ((None,None),RN.bdd_true man) (RN.produce_id man pk3 pk4) map1 in
          let dmap3 = RN.determinize_transition map3 in
          let bdd3 = RN.NKROBSMap.find (key2,true) dmap3 in
          let bdd4 = RN.NKROBSMap.find (key1,true) dmap3 in
          let bdd5 = RN.NKROBSMap.find  ((RN.NKROBSet.singleton ((None,None),RN.bdd_true man)),true) dmap3 in      
          assert_equal ~cmp:MLBDD.equal bdd3 (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4));
          assert_equal ~cmp:MLBDD.equal bdd4 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk3 pk4)));
          assert_equal ~cmp:MLBDD.equal bdd5 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk1 pk2)) (RN.produce_id man pk3 pk4));
          let map4 = RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man) (RN.produce_id man pk2 pk3) map3 in
          let dmap4 = RN.determinize_transition map4 in
          let bdd6 = RN.NKROBSMap.find (key2,true) dmap4 in
          let bdd7 = RN.NKROBSMap.find (RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man),false) dmap4 in
          assert_equal ~cmp:MLBDD.equal bdd6 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk2 pk3)) bdd3);
          assert_equal ~cmp:MLBDD.equal bdd7 (MLBDD.dand (RN.produce_id man pk2 pk3) (MLBDD.dnot (MLBDD.dor (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4))));
        );
        "determinization_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let map1 = RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk1 pk2)) in
          let start1 = (RN.NKROBSet.singleton ((None,None),RN.bdd_false man),true) in
          let dmap1 = RN.determinization man pk1 pk2 start1 map1 in
          let bdd1 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find start1 dmap1)) in
          assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk2);
          assert_equal (RN.NKROBSMap.cardinal dmap1) 1;
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find start1 dmap1)) 1;
          let start2 = (RN.NKROBSet.singleton ((None,None),RN.bdd_false man),false) in
          let dmap2 = RN.determinization man pk1 pk2 start2 map1 in
          let bdd2 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find start1 dmap2)) in
          let bdd3 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find start2 dmap2)) in
          assert_equal ~cmp:MLBDD.equal bdd2 (RN.produce_id man pk1 pk2);
          assert_equal ~cmp:MLBDD.equal bdd3 (RN.produce_id man pk1 pk2);
          assert_equal (RN.NKROBSMap.cardinal dmap2) 2;
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find start1 dmap2)) 1;
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find start2 dmap2)) 1;
          let map2 = RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man) (RN.produce_id man pk2 pk3) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk1 pk2))) in
          let dmap3 = RN.determinization man pk1 pk2 start1 map2 in
          let bdd4 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find start1 dmap3)) in
          assert_equal ~cmp:MLBDD.equal bdd4 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk2 pk3)));
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find start1 dmap3)) 3;
          let map3 = RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk3 pk4)) map2 in
          let dmap4 = RN.determinization man pk1 pk2 start1 map3 in
          let bdd5 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find start1 dmap4)) in
          assert_equal ~cmp:MLBDD.equal bdd5 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk2 pk3)));
          let bdd6 = (RN.NKROBSMap.find (RN.NKROBSet.add ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man)),true) (RN.NKROBSMap.find start1 dmap4)) in
          let bdd7 = (RN.NKROBSMap.find start1 (RN.NKROBSMap.find (RN.NKROBSet.add ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man)),true) dmap4)) in
          assert_equal ~cmp:MLBDD.equal bdd6 (MLBDD.dand (RN.produce_id man pk2 pk3) (RN.produce_id man pk1 pk2));
          assert_equal ~cmp:MLBDD.equal bdd7 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk2 pk3)) (MLBDD.dor (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)));
        );
        "bisim_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let dmap1 = RN.NKROBSMap.empty in
          let start1 = (RN.NKROBSet.singleton ((None,None),RN.bdd_false man),true) in
          let start2 = (RN.NKROBSet.singleton ((None,None),RN.bdd_false man),false) in
          assert_equal true (RN.bisim man pk1 pk2 start1 start1 dmap1 dmap1);
          assert_equal false (RN.bisim man pk1 pk2 start1 start2 dmap1 dmap1);
          let start3 = (RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_false man),false) in
          let start4 = (RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left RN.Id))),RN.bdd_false man),true) in
          let dmap2 = RN.NKROBSMap.add start3 (RN.NKROBSMap.singleton start1 (RN.produce_id man pk1 pk2)) dmap1 in
          assert_equal false (RN.bisim man pk1 pk2 start1 start3 dmap1 dmap2);
          let dmap3 = RN.NKROBSMap.add start3 (RN.NKROBSMap.singleton start2 (RN.produce_id man pk1 pk2)) dmap1 in
          assert_equal true (RN.bisim man pk1 pk2 start2 start3 dmap1 dmap3);
          let dmap4 = RN.NKROBSMap.add start4 (RN.NKROBSMap.singleton start4 (RN.produce_id man pk1 pk2)) dmap1 in
          let dmap5 = RN.NKROBSMap.add start1 (RN.NKROBSMap.singleton start1 (RN.produce_id man pk1 pk2)) dmap1 in
          assert_equal true (RN.bisim man pk1 pk2 start4 start1 dmap4 dmap5);
          let dmap5 = RN.NKROBSMap.add start1 (RN.NKROBSMap.add start2 (MLBDD.dnot (RN.produce_id man pk1 pk2)) (RN.NKROBSMap.singleton start1 (RN.produce_id man pk1 pk2))) dmap1 in
          let dmap6 = RN.NKROBSMap.add start4 (RN.NKROBSMap.add start3 (MLBDD.dnot (RN.produce_id man pk1 pk2)) (RN.NKROBSMap.singleton start4 (RN.produce_id man pk1 pk2))) dmap1 in
          assert_equal true (RN.bisim man pk1 pk2 start4 start1 dmap6 dmap5);
          let dmap7 = RN.NKROBSMap.add start2 (RN.NKROBSMap.singleton start2 (MLBDD.dnot (RN.produce_id man pk1 pk2))) dmap5 in
          assert_equal true (RN.bisim man pk1 pk2 start4 start1 dmap6 dmap7);
          let nkrosmap1 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let nkrobmap1 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap1 in
          let start5 = RN.generate_start man pk1 pk2 pk3  ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let nkrobsmap1 = RN.determinization man pk3 pk4 start5 nkrobmap1 in
          assert_equal true (RN.bisim man pk3 pk4 start5 start5 nkrobsmap1 nkrobsmap1); 
          let nkrosmap2 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (4,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let nkrobmap2 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap2 in
          let start6 = RN.generate_start man pk1 pk2 pk3 ( (RN.NK.Star (RN.NK.Asgn (4,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (3,true))) RN.SR.empty))))) in
          let nkrobsmap2 = RN.determinization man pk3 pk4 start6 nkrobmap2 in
          assert_equal true (RN.bisim man pk3 pk4 start5 start6 nkrobsmap1 nkrobsmap2);
          let nkrosmap3 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.Binary Id)))  in
          let nkrobmap3 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap3 in
          let start7 = RN.generate_start man pk1 pk2 pk3  ( (RN.NK.Star (RN.NK.Asgn (1,true))),  (RN.Rel.StarR (RN.Rel.Binary Id))) in
          let nkrobsmap3 = RN.determinization man pk3 pk4 start7 nkrobmap3 in
          let nkrosmap4 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star (RN.NK.Asgn (4,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (1,true))) RN.SR.empty))))) in
          let nkrobmap4 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap4 in
          let start8 = RN.generate_start man pk1 pk2 pk3 ( (RN.NK.Star (RN.NK.Asgn (4,true))),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RightAsgn (2,true))) (RN.SR.add (RN.Rel.Right (RightAsgn (1,true))) RN.SR.empty))))) in
          let nkrobsmap4 = RN.determinization man pk3 pk4 start8 nkrobmap4 in
          assert_equal false (RN.bisim man pk3 pk4 start7 start8 nkrobsmap3 nkrobsmap4);
          let start9 = (fst start7,true) in
          let nkrobsmap5 = RN.determinization man pk3 pk4 start9 nkrobmap3 in
          assert_equal false (RN.bisim man pk3 pk4 start7 start9 nkrobsmap3 nkrobsmap5);
          assert_equal false (RN.bisim man pk3 pk4 start8 start9 nkrobsmap4 nkrobsmap5);
          let nkrosmap6 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.Binary Id)))  in
          let nkrobmap6 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap6 in
          let start10 = RN.generate_start man pk1 pk2 pk3  ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.Binary Id))) in
          let start11 = (fst start10,true) in
          let nkrobsmap6 = RN.determinization man pk3 pk4 start11 nkrobmap6 in
          let nkrosmap7 = RN.generate_all_transition man pk1 pk2 pk3 pk4 ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left Id) (RN.SR.add (RN.Rel.Right Id) RN.SR.empty)))))  in
          let nkrobmap7 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap7 in
          let start12 = RN.generate_start man pk1 pk2 pk3  ( (RN.NK.Star RN.NK.Dup),  (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left Id) (RN.SR.add (RN.Rel.Right Id) RN.SR.empty))))) in
          let nkrobsmap7 = RN.determinization man pk3 pk4 start12 nkrobmap7 in
          assert_equal true (RN.bisim man pk3 pk4 start11 start12 nkrobsmap6 nkrobsmap7);          
          );
          
      ]

let _ =
  run_test_tt_main begin "all" >::: [
      tests;
    ] end