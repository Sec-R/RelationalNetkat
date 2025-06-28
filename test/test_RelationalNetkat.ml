open OUnit2
open RelationalNetkat

let tests = "MLBDD tests" >::: [
      "var_test" >:: (fun _ctx ->
      let var_a  = RN.bddvar 1 0 in  
      let var_b  = RN.bddvar 1 1 in  
      assert_equal var_a 1;
      assert_equal var_b 7;
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
        let pred_or = RN.Or (RN.Test (1, true), RN.Test (2, false)) in
        let bdd6 = RN.compile_pred_bdd man pk1 pred_or in
        let expected_or =
          MLBDD.dor
            (RN.compile_pred_bdd man pk1 (RN.Test (1, true)))
            (RN.compile_pred_bdd man pk1 (RN.Test (2, false)))
        in
        assert_equal ~cmp:MLBDD.equal bdd6 expected_or;
        let complex_pred =
          RN.And (
            RN.Or (RN.Test (1, true), RN.Test (2, false)),
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
        let bdd5 = RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true)) in
        let bdd6 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.Id,RN.TestP (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd5 bdd6;
        let bdd7 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (1, true),RN.TestP (2, true))) in
        let bdd8 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (2, true),RN.TestP (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd7 bdd8;
        let bdd9 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (1, true),RN.TestP (1, false))) in
        assert_equal ~cmp:MLBDD.equal bdd9 (RN.bdd_false man);
        let bdd10 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (1, true),RN.LeftAsgn (1, true))) in
        let bdd11 = RN.compile_pkr_bdd man pk1 pk2 (RN.LeftAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
        let bdd12 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.TestP (1, true))) in
        let bdd13 = RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd12 bdd13;
        let bdd14 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (1, true),RN.RightAsgn (1, true))) in
        let bdd15 = RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd14 bdd15;
        let bdd16 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.TestP (1, true))) in
        let bdd17 = RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd16 bdd17;
        let bdd18 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (1, true))) in
        let bdd19 = RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true)) in
        assert_equal ~cmp:MLBDD.equal bdd18 bdd19;
        let bdd20 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.OrP (RN.LeftAsgn (1, true),RN.TestP (2, true))),RN.RightAsgn (3, true))) in
        let bdd21 = RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.Comp (RN.LeftAsgn (1, true),RN.RightAsgn (3, true)),RN.Comp(RN.TestP (2, true),RN.RightAsgn (3, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd20 bdd21;
        let bdd22 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp ((RN.RightAsgn (3, true)),(RN.OrP (RN.LeftAsgn (1, true),RN.TestP (2, true))))) in
        let bdd23 = RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.Comp (RN.RightAsgn (3, true),RN.LeftAsgn (1, true)),RN.Comp(RN.RightAsgn (3, true),RN.TestP (2, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd22 bdd23;
        let bdd24 = RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP (1, true),RN.TestP (2, true))) in
        let bdd25 = (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd24 bdd25;
        let bdd26 = RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.TestP (1, true),RN.OrP (RN.TestP (2, true),RN.TestP (3, true)))) in
        let bdd27 = RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.AndP (RN.TestP (1, true),RN.TestP (2, true)),RN.AndP (RN.TestP (1, true),RN.TestP (3, true)))) in
        assert_equal ~cmp:MLBDD.equal bdd26 bdd27;
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
        let nkomap10 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap9 nkomap10;
        let nkomap11 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add (Asgn (2,true)) RN.SNK.empty))))) in
        let nkomap12 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.OrP (RN.RightAsgn (1, true),RN.Id),(RN.OrP (RN.RightAsgn (2, true),RN.Id))))) in
        assert_equal ~cmp:compare nkomap11 nkomap12;
        let nkomap13 = RN.delta_k man pk1 pk2 (Some (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty))))) in
        let nkomap14 = RN.add_nko_mapping 
          (Some (RN.NK.Seq (Pred True, RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty)))))) 
          (RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.RightAsgn (1, true),RN.Id))) 
          (RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.RightAsgn (1, true),RN.Id)))) in
        assert_equal ~cmp:compare nkomap13 nkomap14;
        let nkomap15 = RN.delta_k man pk1 pk2 (Some (RN.NK.Seq (Asgn (1,true), RN.NK.Seq (Asgn (2,true),RN.NK.Dup)))) in
        let nkomap16 = RN.NKOMap.singleton (Some (Pred True)) (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap15 nkomap16;
        let nkomap17 = RN.delta_k man pk1 pk2 (Some (RN.NK.Inter (Asgn (1,true), Asgn (2,true)))) in
        let nkomap18 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.RightAsgn (1, true),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap17 nkomap18;
        let nkomap19 = RN.delta_k man pk1 pk2 (Some (RN.NK.Inter (RN.NK.Seq (Asgn (1,true),RN.NK.Dup), Asgn (2,true)))) in
        assert_equal ~cmp:compare nkomap19 RN.NKOMap.empty;
        let nkomap20 = RN.delta_k man pk1 pk2 (Some (RN.NK.Diff (Asgn (1,true), Asgn (2,true)))) in
        let nkomap21 = RN.NKOMap.singleton None (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (MLBDD.dnot (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (2, true))))) in
        assert_equal ~cmp:compare nkomap20 nkomap21;
        let nkomap22 = RN.delta_k man pk1 pk2 (Some (RN.NK.Diff (RN.NK.Seq (Asgn (1,true),RN.NK.Dup), Asgn (2,true)))) in
        let nkomap23 = RN.NKOMap.singleton (Some (Pred True)) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) in
        assert_equal ~cmp:compare nkomap22 nkomap23;
        let nkomap24 = RN.delta_k man pk1 pk2 (Some (RN.NK.Inter (RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add (Asgn (3,true)) RN.SNK.empty)), Asgn (2,true)))) in
        let nkomap25 = RN.NKOMap.singleton None (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.OrP (RN.RightAsgn (1, true),RN.RightAsgn (3, true)),RN.RightAsgn (2, true)))) in
        assert_equal ~cmp:compare nkomap24 nkomap25;
        let nkomap26 = RN.delta_k man pk1 pk2 (Some (RN.NK.Inter (RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty)), Asgn (2,true)))) in
        assert_equal ~cmp:compare nkomap26 nkomap18;
        let nkomap27 = RN.delta_k man pk1 pk2 (Some (RN.NK.Inter (RN.NK.Union (RN.SNK.add (RN.NK.Seq (Asgn (3,true),(RN.NK.Seq (RN.NK.Dup,RN.NK.Dup)))) (RN.SNK.add (RN.NK.Seq (Asgn (1,true),RN.NK.Dup)) RN.SNK.empty)), (RN.NK.Seq (Asgn (2,true),RN.NK.Dup))))) in
        let nkomap28 = RN.add_nko_mapping (Some (RN.NK.Inter (Pred True,Pred True))) (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.RightAsgn (1, true),RN.RightAsgn (2, true))))
          (RN.NKOMap.singleton (Some (RN.NK.Inter (RN.NK.Seq (Pred True,RN.NK.Dup),Pred True))) (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.RightAsgn (3, true),RN.RightAsgn (2, true))))) in
        assert_equal ~cmp:compare nkomap27 nkomap28;
        let nkomap29 = RN.delta_k man pk1 pk2 (Some (RN.NK.Diff (RN.NK.Union (RN.SNK.add (RN.NK.Seq (Asgn (3,true),(RN.NK.Seq (RN.NK.Dup,RN.NK.Dup)))) (RN.SNK.add (RN.NK.Seq (Asgn (1,true),RN.NK.Dup)) RN.SNK.empty)), (RN.NK.Seq (Asgn (2,true),RN.NK.Dup))))) in
        let nkomap30 = RN.add_nko_mapping (Some (RN.NK.Diff (Pred True,Pred True))) (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.RightAsgn (1, true),RN.RightAsgn (2, true))))
          (RN.add_nko_mapping (Some (RN.NK.Diff (RN.NK.Seq (Pred True,RN.NK.Dup),Pred True))) (RN.compile_pkr_bdd man pk1 pk2 (RN.AndP (RN.RightAsgn (3, true),RN.RightAsgn (2, true))))
          (RN.add_nko_mapping (Some (RN.NK.Seq (Pred True,RN.NK.Dup))) (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (3, true))) (MLBDD.dnot (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (2, true)))))
          (RN.NKOMap.singleton (Some (Pred True)) (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (MLBDD.dnot (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (2, true)))))))) in
        assert_equal ~cmp:compare nkomap29 nkomap30;
        );
        "compile_delta_r_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let compare = RN.ROMap.equal MLBDD.equal in
          let romap1 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.Left (RN.NK.Star (RN.NK.Pred (RN.True))))) X in
          let romap2 = RN.ROMap.singleton None (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 RN.Id) (RN.compile_pkr_bdd man pk3 pk4 RN.Id)) in
          assert_equal ~cmp:compare romap1 romap2;
          let romap3 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.StarR (RN.Rel.Left RN.NK.Dup))) X in
          let romap4 = RN.add_ro_mapping (Some (RN.Rel.SeqR (Left (Pred True), RN.Rel.StarR (RN.Rel.Left RN.NK.Dup))))
            (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) RN.ROMap.empty in
          assert_equal ~cmp:compare romap3 romap4;
          let romap5 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.Left (RN.NK.Seq (Asgn (1,true), RN.NK.Dup)))) X in
          let romap6 = RN.ROMap.singleton (Some (RN.Rel.Left (Pred True))) (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (RN.produce_id man pk3 pk4)) in
          assert_equal ~cmp:compare romap5 romap6;
          let romap7 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (SeqR (Left (Asgn (1,true)), Left (Asgn (2,true))))) X in
          let romap8 = RN.ROMap.singleton (Some (Left (Asgn (2,true)))) (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (RN.produce_id man pk3 pk4)) in
          assert_equal ~cmp:compare romap7 romap8;
          let romap9 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.Id (RN.NK.Star (RN.NK.Pred (RN.True))))) XY in
          let romap10 = RN.ROMap.singleton None (MLBDD.dand (RN.produce_id man pk1 pk3) (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4))) in
          assert_equal ~cmp:compare romap9 romap10;
          let romap11 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (Right (Seq (RN.NK.Pred (RN.True), RN.NK.Dup)))) X in
          assert_equal ~cmp:compare romap11 RN.ROMap.empty;
          let romap12 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (App (Id,Id))) X in
          assert_equal ~cmp:compare romap12 RN.ROMap.empty;
          let romap13 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (Binary (Asgn (1,true), Seq (Dup, Asgn (2,true))))) X in
          let romap14 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (SeqR (Left (Asgn (1,true)), Right (Seq (Dup,Asgn (2,true)))))) X in
          assert_equal ~cmp:compare romap13 romap14;
          let romap15 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty)))) X in
          let romap16 = RN.ROMap.singleton None (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))) (RN.produce_id man pk3 pk4)) in
          assert_equal ~cmp:compare romap15 romap16;
          let romap17 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (Nil Id)) E in
          let romap18 = RN.ROMap.singleton None (MLBDD.dand (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) (RN.produce_id man pk3 pk1)) in
          assert_equal ~cmp:compare romap17 romap18;
          let romap19 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty)))) Y in
          let romap20 = RN.ROMap.singleton None (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.produce_id man pk1 pk2)) in
          assert_equal ~cmp:compare romap19 romap20;
          let romap21 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.SeqR (Left (Pred True), RN.Rel.StarR (RN.Rel.Left RN.NK.Dup)))) E in
          assert_equal ~cmp:compare romap21 (RN.ROMap.singleton (Some (RN.Rel.SeqR (Left (Pred True), RN.Rel.StarR (RN.Rel.Left RN.NK.Dup)))) (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)));
          let romap22 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.SeqR (Nil Id, RN.Rel.StarR (RN.Rel.Left RN.NK.Dup)))) E in
          assert_equal ~cmp:compare romap22 (RN.ROMap.add (Some (RN.Rel.SeqR ((RN.Rel.Left RN.NK.Dup), RN.Rel.StarR (RN.Rel.Left RN.NK.Dup)))) (MLBDD.dand (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) (RN.produce_id man pk3 pk1)) romap18);
          let romap23 = RN.delta_r man pk1 pk2 pk3 pk4 (Some (RN.Rel.Left (RN.NK.Pkr Id))) X in
          assert_equal ~cmp:compare romap1 romap23;
          );
      "delta_krx_test" >:: (fun _ctx ->
        let man = RN.init_man 10 10 in
        let pk1 = 0 in
        let pk2 = 1 in
        let pk3 = 2 in
        let pk4 = 3 in
        let id2bdd = (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) in
        let compare = RN.NKROMap.equal MLBDD.equal in
        let nkromap1 = RN.delta_krx man pk1 pk2 pk3 pk4 (None, None) in
        let nkromap2 = RN.NKROMap.singleton (None,None) id2bdd in
        assert_equal ~cmp:compare nkromap1 nkromap2;
        let nkromap3 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some (Pred True)), Some (RN.Rel.Left (RN.NK.Pkr Id))) in
        let nkromap4 = RN.NKROMap.add ((Some (Pred True)), Some (RN.Rel.Left (RN.NK.Pkr Id))) id2bdd (RN.NKROMap.singleton (None,None) id2bdd) in
        assert_equal ~cmp:compare nkromap3 nkromap4;
        let nkromap5 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some RN.NK.Dup), Some (RN.Rel.Left (RN.NK.Pkr Id))) in
        let nkromap6 = RN.NKROMap.add ((Some RN.NK.Dup), Some (RN.Rel.Left (RN.NK.Pkr Id))) id2bdd (RN.NKROMap.singleton ((Some (Pred True)),None) id2bdd) in
        assert_equal ~cmp:compare nkromap5 nkromap6;
        let nkromap7 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.NK.Pkr Id), RN.Rel.Left (RN.NK.Pkr Id)))) in
        let nkromap8 = RN.NKROMap.add ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.NK.Pkr Id), RN.Rel.Left (RN.NK.Pkr Id)))) id2bdd (RN.NKROMap.add ((Some (Pred True)),Some (RN.Rel.Left (RN.NK.Pkr Id))) id2bdd
        (RN.NKROMap.singleton (None,None) id2bdd)) in
        assert_equal ~cmp:compare nkromap7 nkromap8;
        let nkromap9 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Asgn (1,true)), Some (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true))))) in
        let nkromap10 = RN.NKROMap.add (Some (RN.NK.Asgn (1,true)), Some (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true))))) id2bdd
        (RN.NKROMap.singleton (None,None) 
        (MLBDD.dand (RN.produce_id man pk3 pk4) (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP(1,true),RN.TestP(2,true)))))) in
        assert_equal ~cmp:compare nkromap9 nkromap10;
        let nkromap11 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.NK.Pkr (RN.RightAsgn (1,true))), RN.Rel.Left (RN.NK.Pkr (RN.RightAsgn (2,true)))))) in
        let nkromap12 = RN.NKROMap.add ((Some RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Left (RN.NK.Pkr (RN.RightAsgn (1,true))), RN.Rel.Left (RN.NK.Pkr (RN.RightAsgn (2,true)))))) id2bdd
          (RN.NKROMap.add (None,None) (MLBDD.dand (RN.produce_id man pk3 pk4)  (RN.compile_pkr_bdd man pk1 pk2 (RN.Comp (RN.TestP(1,true),RN.TestP(2,true)))))
          (RN.NKROMap.singleton (Some (Pred True),Some (RN.Rel.Left (RN.NK.Pkr (RN.RightAsgn (2,true))))) (MLBDD.dand (RN.produce_id man pk3 pk4)  (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP(1,true))))))
         in
        assert_equal ~cmp:compare nkromap11 nkromap12;
        let nkromap13 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id)))) in
        let bdd1 = RN.NKROMap.find (None, None) nkromap13 in
        let bdd2 = RN.NKROMap.find ((Some RN.NK.Dup), Some (SeqR ((RN.Rel.Left (RN.NK.Pkr Id)),RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id))))) nkromap13 in
        let bdd3 = RN.NKROMap.find ((Some (Pred True)), None) nkromap13 in
        assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
        assert_equal ~cmp:MLBDD.equal bdd2 bdd3;
        assert_equal ~cmp:MLBDD.equal bdd3 id2bdd;
      (* Print to See!*)   
      (* print_endline (RN.nkro_map_to_string nkromap13);*)
        assert_equal (RN.NKROMap.cardinal nkromap13) 6;
        let nkromap14 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some (RN.NK.Star RN.NK.Dup)), Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id)))) in
        let bdd4 = RN.NKROMap.find (None, None) nkromap14 in
        let bdd5 = RN.NKROMap.find ((Some (RN.NK.Star RN.NK.Dup)), Some (SeqR ((RN.Rel.Left (RN.NK.Pkr Id)),RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id))))) nkromap14 in
        assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
        assert_equal ~cmp:MLBDD.equal bdd5 id2bdd;
      (* Print to See!*)   
      (* print_endline (RN.nkro_map_to_string nkromap14);*)
        assert_equal (RN.NKROMap.cardinal nkromap14) 6; (* Substitute for (RN.NK.Star RN.NK.Dup)*)
        let nkromap15 = RN.delta_krx man pk1 pk2 pk3 pk4 ((Some (RN.NK.Star RN.NK.Dup)), Some (RN.Rel.SeqR ((RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id))),(RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr Id)))))) in
        assert_equal (RN.NKROMap.cardinal nkromap15) 9; 
        (* 
          There are 9 pairs in the nkromap15.
          the nko pairs are 
          None, Seq (Pred True, Star (Dup)),  Star (Dup)
          The ro pairs are
          None, SeqR Left Pkr Id StarR Left Pkr Id,  SeqR SeqR Left Pkr Id StarR Left Pkr Id StarR Left Pkr Id
        *)
        let nkromap16 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
          Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) in
        let bdd6 = RN.NKROMap.find (None,None) nkromap16 in  
        let bdd7 = MLBDD.dand (RN.produce_id man pk3 pk4 ) (RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.TestP (1, true),RN.TestP (2, true)))) in
        let bdd8 = RN.NKROMap.find ((Some (RN.NK.Star RN.NK.Dup)),Some (SeqR ((RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))),(RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))))) nkromap16 in
        let bdd9 = RN.NKROMap.find (None,Some (SeqR ((RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))),(RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))))) nkromap16 in
        assert_equal ~cmp:MLBDD.equal bdd6 bdd7;
        assert_equal ~cmp:MLBDD.equal bdd8 id2bdd;
        assert_equal ~cmp:MLBDD.equal bdd7 bdd9;
        let nkromap17 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Right (RN.NK.Pkr RN.Id)))) in
        let bdd10 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap17 in
        assert_equal ~cmp:MLBDD.equal bdd10 id2bdd;
        let nkromap18 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
        Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) in
        let bdd11 = RN.NKROMap.find (Some (Seq (Pred True, Star RN.NK.Dup)),None) nkromap18 in
        let bdd12 = MLBDD.dand (RN.produce_id man pk3 pk4) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true))) in
        assert_equal ~cmp:MLBDD.equal bdd11 bdd12;
        let nkromap19 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.Left (RN.NK.Star RN.NK.Dup))) in
        let bdd13 = RN.NKROMap.find (None,None) nkromap19 in
        assert_equal ~cmp:MLBDD.equal bdd13 id2bdd;
        let nkromap20 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty)))),
        Some (RN.Rel.Left (RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty)))))) in
        let bdd14 = RN.NKROMap.find (None,None) nkromap20 in
        assert_equal ~cmp:MLBDD.equal bdd14 (MLBDD.dand (RN.compile_pkr_bdd man pk1 pk2 (RN.OrP (RN.RightAsgn (1, true),RN.Id))) (RN.produce_id man pk3 pk4));
        let nkromap21 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
        Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (Seq (RN.NK.Pkr (RightAsgn (1,true)),Dup))) (RN.SR.add (RN.Rel.Right (Seq (RN.NK.Pkr (RightAsgn (2,true)), Dup))) RN.SR.empty))))) in
        let bdd15 = MLBDD.dand (RN.produce_id man pk3 pk4) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true))) in
        let bdd16 = RN.NKROMap.find (None,None) nkromap21 in
        assert_equal ~cmp:MLBDD.equal bdd15 bdd16;
        let nkromap21 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
        Some (RN.Rel.StarR (RN.Rel.SeqR (Nil Id,(RN.Rel.OrR (RN.SR.add (RN.Rel.Left (Seq (RN.NK.Pkr (RightAsgn (1,true)),Dup))) (RN.SR.add (RN.Rel.Right (Seq (RN.NK.Pkr (RightAsgn (2,true)), Dup))) RN.SR.empty))))))) in
        let bdd17 = RN.NKROMap.find (None,None) nkromap21 in
        assert_equal ~cmp:MLBDD.equal (MLBDD.dand bdd15 (RN.produce_id man pk1 pk3)) bdd17;
        let nkromap22 = RN.delta_krx man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
        Some (RN.Rel.StarR (RN.Rel.SeqR (Nil Id,(RN.Rel.OrR (RN.SR.add (RN.Rel.SeqR ((RN.Rel.Left (Seq (RN.NK.Pkr (RightAsgn (1,true)),Dup))),Nil (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (Seq (RN.NK.Pkr (RightAsgn (2,true)), Dup))) RN.SR.empty))))))) in
        let bdd18 = RN.NKROMap.find (None,None) nkromap22 in
        assert_equal ~cmp:MLBDD.equal (MLBDD.dand bdd18 (MLBDD.dand (RN.produce_id man pk1 pk3) (RN.compile_pkr_bdd man pk2 pk4 (RightAsgn (1, true))))) bdd18;
      );
        "delta_kr_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let id2bdd = (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)) in
          let compare = RN.NKROMap.equal MLBDD.equal in
          let nkromap1 = RN.delta_kr man pk1 pk2 pk3 pk4 (None,None) true in
          let nkromap2 = RN.NKROMap.empty in
          assert_equal ~cmp:compare nkromap1 nkromap2;
          let nkromap3 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup),None) true in
          assert_equal ~cmp:compare nkromap2 nkromap3;
          let nkromap4 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))) true in
      (*  Should not be found! *)
      (* let bdd1 = RN.NKROMap.find (None,None) nkromap4 in *)
          assert_equal ~cmp:compare nkromap4 nkromap3;
          let nkromap5 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.Right (Seq (Dup, RN.NK.Pkr RN.Id))))) true in
        (*  Should not be found! *)
        (* let bdd2 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap5 in *)
          let bdd3 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.SeqR (RN.Rel.Right (Seq (Pred True, RN.NK.Pkr RN.Id)),(RN.Rel.StarR (RN.Rel.Right (Seq (Dup, RN.NK.Pkr RN.Id))))))) nkromap5 in
          assert_equal ~cmp:MLBDD.equal id2bdd bdd3;
          let nkromap6 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), 
          Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) true in
          let bdd4 = RN.NKROMap.find (None,None) nkromap6 in
          let bdd5 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (1, true)))) in
          assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
          let bdd6 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap6 in
          let bdd7 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.produce_id man pk1 pk2)) in
          assert_equal ~cmp:MLBDD.equal bdd6 bdd7;
          let nkromap7 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Dup), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) true in
          assert_equal ~cmp:compare nkromap1 nkromap7;
          let nkromap8 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) true in
          let bdd8 = RN.NKROMap.find (None,None) nkromap8 in
          let bdd9 =  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)))) in
          assert_equal ~cmp:MLBDD.equal bdd8 bdd9;
          (* Compare to nkromap5 *)
          let nkromap9 = RN.delta_kr man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.Right (RN.NK.Star (RN.NK.Pkr RN.Id)))) true in
          let bdd10 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),None) nkromap9 in
          assert_equal ~cmp:MLBDD.equal bdd10 (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4));
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
          let bdd2 =  MLBDD.dand (RN.produce_id man pk1 pk3) (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (3, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (2, true)))) in
          let bdd3 = RN.back_ordering pk1 pk2 pk3 pk4 (RN.re_ordering pk1 pk2 pk3 pk4 bdd2) in
          let bdd4 = RN.re_ordering pk1 pk2 pk3 pk4 (RN.back_ordering pk1 pk2 pk3 pk4 bdd2) in
          assert_equal ~cmp:MLBDD.equal bdd2 bdd3;
          assert_equal ~cmp:MLBDD.equal bdd3 bdd4;
          );
        "calculate_reachable_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let nkromap1 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) true in
          let bdd1 = RN.NKROMap.find (Some (RN.NK.Star RN.NK.Dup),Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) nkromap1 in
          let bdd2 = RN.bdd_true man in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          let nkromap2 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))) true in
          let bdd3 = (MLBDD.dand bdd2 (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))))) in
          let support13 = RN.generate_double_support man pk1 pk3 in
          let bdd4 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd3))) in
          let bdd5 = RN.NKROMap.find (None,None) nkromap2 in
          assert_equal ~cmp:MLBDD.equal bdd4 bdd5;
          let bdd6 = RN.NKROMap.find (None,Some (RN.Rel.SeqR (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true))), (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (1,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (2,true)))) RN.SR.empty))))))) nkromap2 in
          let bdd7 =  (MLBDD.dand bdd2  (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true))))) in
          let bdd8 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd7))) in
          assert_equal ~cmp:MLBDD.equal bdd6 bdd8;
          let nkromap3 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty))))) true in
          let bdd9 = MLBDD.dand bdd2 (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (3, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (2, true)))) in
          let bdd10 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd9))) in
          let bdd11 = RN.NKROMap.find (None,None) nkromap3 in
          assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
          let nkromap4 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (Some (RN.NK.Seq (RN.NK.Asgn (1,true),(RN.NK.Star (RN.NK.Asgn (1,true))))), Some (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (TestP (1,false)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty))))) true in
          assert_equal (Option.is_none (RN.NKROMap.find_opt (None,None) nkromap4)) true;
          let nkromap5 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (SeqR (Nil Id,(RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty))))))) true in
          let bdd12 = MLBDD.dand (RN.produce_id man pk1 pk3) (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (3, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.TestP (2, true)))) in
          let bdd13 = (RN.rename_bdd pk2 pk1 (RN.rename_bdd pk4 pk3 (MLBDD.exists support13 bdd12))) in
          let bdd14 = RN.NKROMap.find (None,None) nkromap5 in
          assert_equal ~cmp:MLBDD.equal bdd13 bdd14;          
        );
        "splitting_bdd_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let bdd1 = RN.produce_id man pk1 pk3 in
          let bdd2 = RN.BSet.choose (RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd1) in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          assert_equal (RN.BSet.cardinal (RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd1)) 1;
          let bdd3 = (MLBDD.dand (RN.compile_pkr_bdd man pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man pk1 pk2 (RN.RightAsgn (1, true)))) in
          let bddset = RN.splitting_bdd man pk1 pk2 pk3 pk4 bdd3 in
          let bdd4 = RN.BSet.fold (fun acc x -> MLBDD.dor acc x) bddset (RN.bdd_false man) in
          assert_equal ~cmp:MLBDD.equal bdd3 bdd4;
          assert_equal (RN.BSet.cardinal bddset) 512;
          let man2 = RN.init_man 128 128 in
          let bdd5 = RN.produce_id man2 pk1 pk3 in
          let bdd6 = RN.BSet.choose (RN.splitting_bdd man2 pk1 pk2 pk3 pk4 bdd5) in
          assert_equal ~cmp:MLBDD.equal bdd5 bdd6;
          assert_equal (RN.BSet.cardinal (RN.splitting_bdd man2 pk1 pk2 pk3 pk4 bdd5)) 1;
          let bdd7 = (MLBDD.dand (RN.produce_id man2 pk1 pk3) (MLBDD.dand (RN.compile_pkr_bdd man2 pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man2 pk1 pk2 (RN.RightAsgn (1, true))))) in
          let bddset2 = RN.splitting_bdd man2 pk1 pk2 pk3 pk4 bdd7 in
          let bdd8 = RN.BSet.fold (fun acc x -> MLBDD.dor acc x) bddset2 (RN.bdd_false man2) in
          assert_equal ~cmp:MLBDD.equal bdd7 bdd8;
          assert_equal (RN.BSet.cardinal bddset2) 1;
          let bdd9 = (MLBDD.dand (RN.compile_pkr_bdd man2 pk1 pk3 (RN.RightAsgn (3, true))) (MLBDD.dand (RN.compile_pkr_bdd man2 pk3 pk4 (RN.RightAsgn (2, true))) (RN.compile_pkr_bdd man2 pk1 pk2 (RN.RightAsgn (1, true))))) in
          let bddset3 = RN.splitting_bdd man2 pk1 pk2 pk3 pk4 bdd9 in
          let bdd10 = RN.BSet.fold (fun acc x -> MLBDD.dor acc x) bddset3 (RN.bdd_false man2) in
          assert_equal ~cmp:MLBDD.equal bdd9 bdd10;
          assert_equal (RN.BSet.cardinal bddset3) 2;
        );
        "transition_test" >:: (fun _ctx ->
          let man = RN.init_man 32 32 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let nkro1 =  (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.SeqR (Nil Id,(RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty))))))) in
          let nkrosmap1 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro1 true in
          assert_equal true (RN.NKROMap.mem (None,None) nkrosmap1); 
          (* Print to see *)
          (* print_endline (RN.transition_set_map_to_string nkrosmap1); *)
          let nkro2 =    (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.SeqR (Nil Id, (RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty))))))) in
          let nkrosmap2 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro2 true in
          let nkromap1 = RN.calculate_reachable_set man pk1 pk2 pk3 pk4 nkro2 true in
          RN.NKROMap.iter (fun nkro (bset,_) -> if RN.is_final_nkro nkro then assert_equal ~cmp:MLBDD.equal (RN.bdd_true man) (RN.BSet.choose bset)
                                                else assert_equal ~cmp:MLBDD.equal (RN.NKROMap.find nkro nkromap1) (MLBDD.dor (RN.NKROMap.find nkro nkromap1) (RN.BSet.fold (fun bdd acc -> MLBDD.dor bdd acc) bset (RN.bdd_false man)))
                                                ) nkrosmap2;
          (* Print to see *)
          (* print_endline (RN.transition_set_map_to_string nkrosmap2); *)
          let nkrobmap1 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap1 in
          assert_equal false (RN.NKROBMap.mem ((None,None),RN.bdd_true man) nkrobmap1); 
          RN.NKROBMap.iter (fun (nkro,bdd) _ -> assert_equal true (RN.BSet.mem bdd (fst (RN.NKROMap.find nkro nkrosmap1)))) nkrobmap1;
          let nkrobmap2 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap2 in
          RN.NKROBMap.iter (fun (nkro,bdd) _ -> assert_equal true (RN.BSet.mem bdd (fst (RN.NKROMap.find nkro nkrosmap2)))) nkrobmap2;
          (* Print to see *)
          (* print_endline (RN.transition_map_to_string nkrobmap1); *)
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
          let (key1,bdd1) = RN.NKROBSMap.choose dmap1 in
          assert_equal ~cmp:RN.NKROBSet.equal key1 (RN.NKROBSet.singleton ((None,None),RN.bdd_false man));
          assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk2);
          let map2 = RN.NKROBMap.add ((None,None),RN.bdd_true man) (RN.produce_id man pk1 pk2) map1 in
          let dmap2 = RN.determinize_transition map2 in
          let (key2,bdd2) = RN.NKROBSMap.choose dmap2 in
          assert_equal ~cmp:RN.NKROBSet.equal key2 (RN.NKROBSet.add ((None,None),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man)));
          assert_equal ~cmp:MLBDD.equal bdd2 (RN.produce_id man pk1 pk2);
          assert_equal (RN.NKROBSMap.cardinal dmap2) 1;
          let map3 = RN.NKROBMap.add ((None,None),RN.bdd_true man) (RN.produce_id man pk3 pk4) map1 in
          let dmap3 = RN.determinize_transition map3 in
          let bdd3 = RN.NKROBSMap.find key2 dmap3 in
          let bdd4 = RN.NKROBSMap.find key1 dmap3 in
          let bdd5 = RN.NKROBSMap.find  (RN.NKROBSet.singleton ((None,None),RN.bdd_true man)) dmap3 in      
          assert_equal ~cmp:MLBDD.equal bdd3 (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4));
          assert_equal ~cmp:MLBDD.equal bdd4 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk3 pk4)));
          assert_equal ~cmp:MLBDD.equal bdd5 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk1 pk2)) (RN.produce_id man pk3 pk4));
          let map4 = RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) (RN.produce_id man pk2 pk3) map3 in
          let dmap4 = RN.determinize_transition map4 in
          let bdd6 = RN.NKROBSMap.find key2 dmap4 in
          let bdd7 = RN.NKROBSMap.find (RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man)) dmap4 in
          assert_equal ~cmp:MLBDD.equal bdd6 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk2 pk3)) bdd3);
          assert_equal ~cmp:MLBDD.equal bdd7 (MLBDD.dand (RN.produce_id man pk2 pk3) (MLBDD.dnot (MLBDD.dor (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4))));
          let map5 = RN.NKOMap.singleton (Some (Pred True)) (RN.produce_id man pk1 pk2) in
          let dmap5 = RN.determinize_nko_transition map5 in
          let (nk5,bdd5) = RN.NKOMap.choose dmap5 in
          assert_equal nk5 (Some (Pred True));
          assert_equal ~cmp:MLBDD.equal bdd5 (RN.produce_id man pk1 pk2);
          let map6 = RN.NKOMap.add (Some (RN.NK.Asgn (1,true))) (RN.produce_id man pk1 pk2) map5 in
          let dmap6 = RN.determinize_nko_transition map6 in
          let (nk6,bdd6) = RN.NKOMap.choose dmap6 in
          assert_equal 0 (Option.compare RN.NK.compare nk6 (Some (RN.NK.Union (RN.SNK.add (RN.NK.Asgn (1,true)) (RN.SNK.singleton (Pred True))))));
          assert_equal ~cmp:MLBDD.equal bdd6 (RN.produce_id man pk1 pk2);
          let map7 = RN.NKOMap.add (Some (RN.NK.Asgn (2,true))) (RN.produce_id man pk3 pk4) map5 in
          let dmap7 = RN.determinize_nko_transition map7 in
          let bdd8 = RN.NKOMap.find (Some (Pred True)) dmap7 in
          let bdd9 = RN.NKOMap.find (Some (RN.NK.Asgn (2,true))) dmap7 in 
          assert_equal ~cmp:MLBDD.equal bdd8 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk3 pk4)));
          assert_equal ~cmp:MLBDD.equal bdd9 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk1 pk2)) (RN.produce_id man pk3 pk4));
          let bdd10 = RN.NKOMap.find (RN.unionize_nko (Some (Pred True)) (Some (RN.NK.Asgn (2,true)))) dmap7 in
          let bdd11 = RN.NKOMap.find (Some (RN.NK.Union (RN.SNK.add (RN.NK.Asgn (2,true)) (RN.SNK.singleton (Pred True))))) dmap7 in
          assert_equal ~cmp:MLBDD.equal bdd10 (MLBDD.dand (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4));
          assert_equal ~cmp:MLBDD.equal bdd10 bdd11;
        );
        "determinization_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let map1 = RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk1 pk2)) in
          let start1 = (None,None) in
          let (dmap1,dstart1) = RN.determinization (RN.start_to_set start1) map1 in
          let bdd1 = (RN.NKROBSMap.find dstart1 (RN.NKROBSMap.find dstart1 dmap1)) in
          assert_equal ~cmp:MLBDD.equal bdd1 (RN.produce_id man pk1 pk2);
          assert_equal (RN.NKROBSMap.cardinal dmap1) 1;
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find dstart1 dmap1)) 1;
          let map2 = RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) (RN.produce_id man pk2 pk3) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk1 pk2))) in
          let (dmap2,dstart2) = RN.determinization (RN.start_to_set start1) map2 in
          let bdd2 = (RN.NKROBSMap.find dstart2 (RN.NKROBSMap.find dstart2 dmap2)) in
          assert_equal ~cmp:MLBDD.equal bdd2 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk2 pk3)));
          assert_equal (RN.NKROBSMap.cardinal (RN.NKROBSMap.find dstart1 dmap2)) 3;
          let map3 = RN.NKROBMap.add ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk3 pk4)) map2 in
          let (dmap3,dstart3) = RN.determinization (RN.start_to_set start1) map3 in
          let bdd3 = (RN.NKROBSMap.find dstart3 (RN.NKROBSMap.find dstart3 dmap3)) in
          assert_equal ~cmp:MLBDD.equal bdd3 (MLBDD.dand (RN.produce_id man pk1 pk2) (MLBDD.dnot (RN.produce_id man pk2 pk3)));
          let bdd4 = (RN.NKROBSMap.find (RN.NKROBSet.add ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man))) (RN.NKROBSMap.find dstart3 dmap3)) in
          let bdd5 = (RN.NKROBSMap.find dstart3 (RN.NKROBSMap.find (RN.NKROBSet.add ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) (RN.NKROBSet.singleton ((None,None),RN.bdd_false man))) dmap3)) in
          assert_equal ~cmp:MLBDD.equal bdd4 (MLBDD.dand (RN.produce_id man pk2 pk3) (RN.produce_id man pk1 pk2));
          assert_equal ~cmp:MLBDD.equal bdd5 (MLBDD.dand (MLBDD.dnot (RN.produce_id man pk2 pk3)) (MLBDD.dor (RN.produce_id man pk1 pk2) (RN.produce_id man pk3 pk4)));
          let map4 = RN.NKROBMap.add ((None,None),RN.bdd_true man) (RN.NKROBMap.singleton ((None,None),RN.bdd_false man) (RN.produce_id man pk3 pk4)) map1 in
          let (dmap4,dstart4) = RN.determinization (RN.start_to_set start1) map4 in
          let bdd6 = (RN.NKROBSMap.find (RN.NKROBSet.singleton ((None,None),RN.bdd_false man)) (RN.NKROBSMap.find dstart4 dmap4)) in
          assert_equal ~cmp:MLBDD.equal bdd6 (MLBDD.dor (RN.produce_id man pk3 pk4) (RN.produce_id man pk1 pk2));
        );
        "bisim_test" >:: (fun _ctx ->
          let man = RN.init_man 10 10 in
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let dmap1 = RN.NKROBSMap.empty in
          let start1 = RN.NKROBSet.singleton ((None,None),RN.bdd_false man) in
          let start2 = RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_false man) in
          assert_equal true (RN.bisim man pk1 pk2 start1 start1 dmap1 dmap1);
          assert_equal false (RN.bisim man pk1 pk2 start1 start2 dmap1 dmap1);
          let start3 = RN.NKROBSet.singleton ((None,Some (RN.Rel.StarR (RN.Rel.Left (RN.NK.Pkr RN.Id)))),RN.bdd_true man) in
          let start4 = RN.NKROBSet.singleton ((None,None),RN.bdd_true man) in
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
          let nkro1 = (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some (RN.Rel.SeqR (RN.Rel.Nil RN.Id,RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty)))))) in
          let nkrosmap1 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro1 true in
          let nkrobmap1 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap1 in
          let (nkrobsmap1,start5) = RN.determinization (RN.start_to_set nkro1) nkrobmap1 in
          assert_equal true (RN.bisim man pk3 pk4 start5 start5 nkrobsmap1 nkrobsmap1);
          let nkro2 =(Some (RN.NK.Star (RN.NK.Asgn (4,true))), Some (RN.Rel.SeqR (RN.Rel.Nil RN.Id, RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (3,true)))) RN.SR.empty)))))) in
          let nkrosmap2 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro2 true in
          let nkrobmap2 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap2 in
          let (nkrobsmap2,start6) = RN.determinization (RN.start_to_set nkro2) nkrobmap2 in
          assert_equal true (RN.bisim man pk3 pk4 start5 start6 nkrobsmap1 nkrobsmap2);
          let nkro3 = (Some (RN.NK.Star (RN.NK.Asgn (1,true))), Some  (RN.Rel.SeqR (RN.Rel.Nil RN.Id, RN.Rel.StarR (RN.Rel.App (Id,Id))))) in
          let nkrosmap3 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro3 true in
          let nkrobmap3 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap3 in
          let (nkrobsmap3,start7) = RN.determinization (RN.start_to_set nkro3) nkrobmap3 in
          let nkro4 = (Some (RN.NK.Star (RN.NK.Asgn (4,true))), Some (RN.Rel.SeqR (RN.Rel.Nil RN.Id, RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr (RightAsgn (2,true)))) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr (RightAsgn (1,true)))) RN.SR.empty)))))) in
          let nkrosmap4 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro4 true in
          let nkrobmap4 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap4 in
          let (nkrobsmap4,start8) = RN.determinization (RN.start_to_set nkro4) nkrobmap4 in
          assert_equal false (RN.bisim man pk3 pk4 start7 start8 nkrobsmap3 nkrobsmap4);
          let nkro5 = (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Nil RN.Id,RN.Rel.StarR (RN.Rel.App (Id,Id))))) in
          let nkrosmap5 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro5 true in
          let nkrobmap5 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap5 in
          let (nkrobsmap5,start9) = RN.determinization (RN.start_to_set nkro5) nkrobmap5 in
          let nkro6 = (Some (RN.NK.Star RN.NK.Dup), Some (RN.Rel.SeqR (RN.Rel.Nil RN.Id,RN.Rel.StarR (RN.Rel.OrR (RN.SR.add (RN.Rel.Left (RN.NK.Pkr Id)) (RN.SR.add (RN.Rel.Right (RN.NK.Pkr Id)) RN.SR.empty)))))) in
          let nkrosmap6 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro6 true in
          let nkrobmap6 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap6 in
          let (nkrobsmap6,start10) = RN.determinization (RN.start_to_set nkro6) nkrobmap6 in
          assert_equal true (RN.bisim man pk3 pk4 start9 start10 nkrobsmap5 nkrobsmap6);
          let nk1 = (RN.NK.Seq (Pred True, RN.NK.Star(RN.NK.Union (RN.SNK.add (Asgn (1,true)) (RN.SNK.add RN.NK.Dup RN.SNK.empty))))) in
          let nk2 = (RN.NK.Seq (Asgn (2,true), RN.NK.Seq (RN.NK.Dup,(RN.NK.Union (RN.SNK.add (RN.NK.Seq (Asgn (3,true),RN.NK.Dup)) (RN.SNK.add (Asgn (4,true)) RN.SNK.empty)))))) in
          (* Inter (nk1,nk2) |> Id *)
          (* nil (Id) = (pk,pk) *)
          (* App (Id,Id) = (pk1pk2,pk1pk2) *)
          (* nil(Id) App (Id,Id) = {(pk,pk)|pk\in PK} . {(pk1pk2,pk1pk2)|pk1,pk2 \in PK} = {(pk.pk1pk2,pk.pk1pk2)|pk,pk1,pk2 \in PK} *)
          (* = {(pk.pk1pk2,pk.pk1pk2)|pk,pk1,pk2 \in PK /\ pk = pk1} = {(pk1pk2,pk1pk2)|pk1,pk2 \in PK} = App (Id,Id)*)
          let nkro7 = (Some (RN.NK.Inter (nk1,nk2)), Some (RN.Rel.StarR (RN.Rel.App (Id,Id)))) in
          let nkrosmap7 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro7 true in
          let nkrobmap7 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap7 in
          let (nkrobsmap7,start11) = RN.determinization (RN.start_to_set nkro7) nkrobmap7 in
          (* nk1 |> Id (nk2) *)
          let nkro8 = (Some nk1, Some (RN.Rel.Id nk2)) in
          let nkrosmap8 = RN.generate_all_transition man pk1 pk2 pk3 pk4 nkro8 true in
          let nkrobmap8 = RN.simplify_all_transition man pk1 pk2 pk3 pk4 nkrosmap8 in
          let (nkrobsmap8,start12) = RN.determinization (RN.start_to_set nkro8) nkrobmap8 in
          assert_equal true (RN.bisim man pk3 pk4 start11 start12 nkrobsmap7 nkrobsmap8);
          (* nk2 |> Id *)
          let nkro9 = (Some nk2, Some (RN.Rel.StarR (RN.Rel.App (Id,Id)))) in
          let (nkrobsmap9,start13) = RN.projection_compiler man pk1 pk2 pk3 pk4 nkro9 true in
          (* nk1 |> nk1 X nk2 *)
          let nkro10 = (Some nk1, Some (RN.Rel.SeqR (RN.Rel.Nil Id, Binary (nk1,nk2)))) in
          let (nkrobsmap10,start14) = RN.projection_compiler man pk1 pk2 pk3 pk4 nkro10 true in
          assert_equal true (RN.bisim man pk3 pk4 start13 start14 nkrobsmap9 nkrobsmap10);
          let nkro11 = (Some nk1, (Some (RN.Rel.IdComp ((Some nk2),(RN.Rel.StarR (RN.Rel.App (Id,Id))))))) in
          let (nkrobsmap11,start15) = RN.projection_compiler man pk1 pk2 pk3 pk4 nkro11 true in
          assert_equal true (RN.bisim man pk3 pk4 start12 start15 nkrobsmap8 nkrobsmap11);
          let pred1 = RN.Test (1, true) in
          let pkr1 = RN.AndP (RN.Binary (RN.Neg pred1, True), RN.Id) in
          let relation1 = RN.Rel.StarR (RN.Rel.App (pkr1,pkr1)) in
          let (nkrobsmap12,start16) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some (RN.NK.Inter (nk1,nk2)), Some relation1) true in
          let pkr2 = RN.Binary (Neg pred1, Neg pred1) in
          let relation2 = RN.Rel.StarR (RN.Rel.SeqR (RN.Rel.Nil Id, RN.Rel.SeqR( RN.Rel.Binary (RN.NK.Pkr pkr2,RN.NK.Pkr Havoc),RN.Rel.Nil Id))) in
          let (nkrobsmap13,start17) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some (RN.NK.Inter (nk1,nk2)), Some relation2) true in
          assert_equal true (RN.bisim man pk3 pk4 start16 start17 nkrobsmap12 nkrobsmap13);

          );
          (*
         "rela_id_test" >:: (fun _ctx ->
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let rela_json = Yojson.Basic.from_file "../../../dataset/rela_test.json" in
          let rela_man = Eval.init_rela_man rela_json in
          let man = RN.init_man (Eval.get_field_length rela_man) (Eval.get_field_length rela_man) in
          for i = 1 to 20 do
            let t = Sys.time() in
            let (before_network, after_network) = Eval.sized_rela_to_network rela_json i rela_man in
            let (nkrobsmap1, start1) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some before_network, Some (RN.Rel.StarR (RN.Rel.App (Id,Id)))) true in
            let (nkrobsmap2, start2) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some after_network, Some (RN.Rel.StarR (RN.Rel.App (Id,Id)))) true in
            assert_equal true (RN.bisim man pk3 pk4 start1 start2 nkrobsmap1 nkrobsmap2);            
            print_endline ("Rela Test " ^ string_of_int i ^ " time: ");
            let formatted_float = Printf.sprintf "%.3f" (Sys.time() -. t) in
            print_endline (formatted_float ^ "s");
          done;
         );
         "rela_delete_test" >:: (fun _ctx ->
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let rela_json = Yojson.Basic.from_file "../../../dataset/rela_test.json" in
          let rela_man = Eval.init_rela_man rela_json in
          let man = RN.init_man (Eval.get_field_length rela_man) (Eval.get_field_length rela_man) in
          for i = 1 to 20 do
            let t = Sys.time() in
            let loc_pred = RN.Neg (Eval.parse_location_to_pred "Device262" false rela_man) in
            let pkr = RN.AndP (RN.Binary (loc_pred, RN.True),Id) in
            let (before_network, after_network) = Eval.sized_rela_to_network rela_json i rela_man in
            let (nkrobsmap1, start1) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some before_network, Some (RN.Rel.StarR (RN.Rel.App (pkr,pkr)))) true in
            let (nkrobsmap2, start2) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some after_network, Some (RN.Rel.StarR (RN.Rel.App (pkr,pkr)))) true in
            assert_equal true (RN.bisim man pk3 pk4 start1 start2 nkrobsmap1 nkrobsmap2);            
            print_endline ("Rela Test " ^ string_of_int i ^ " time: ");
            let formatted_float = Printf.sprintf "%.3f" (Sys.time() -. t) in
            print_endline (formatted_float ^ "s");
          done;
         );
         
          "rela_change_test" >:: (fun _ctx ->
          let pk1 = 0 in
          let pk2 = 1 in
          let pk3 = 2 in
          let pk4 = 3 in
          let rela_json = Yojson.Basic.from_file "../../../dataset/rela_test.json" in
          let rela_man = Eval.init_rela_man rela_json in
          let man = RN.init_man (Eval.get_field_length rela_man) (Eval.get_field_length rela_man) in
          for i = 1 to 20 do
            let t = Sys.time() in
            let loc_pred = Eval.parse_location_to_pred "Device262" false rela_man in
            let loc_pkr = Eval.parse_location_to_pkr "Device2063" false rela_man in
            let pkr = RN.OrP (RN.AndP (RN.Binary (loc_pred, RN.True),loc_pkr),RN.AndP (RN.Binary (RN.Neg loc_pred, RN.True),Id)) in
            let (before_network, after_network) = Eval.sized_rela_to_network rela_json i rela_man in
            let (nkrobsmap1, start1) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some before_network, Some (RN.Rel.StarR (RN.Rel.App (pkr,pkr)))) true in
            let (nkrobsmap2, start2) = RN.projection_compiler man pk1 pk2 pk3 pk4 (Some after_network, Some (RN.Rel.StarR (RN.Rel.App (pkr,pkr)))) true in
            assert_equal true (RN.bisim man pk3 pk4 start1 start2 nkrobsmap1 nkrobsmap2);            
            print_endline ("Rela Test " ^ string_of_int i ^ " time: ");
            let formatted_float = Printf.sprintf "%.3f" (Sys.time() -. t) in
            print_endline (formatted_float ^ "s");
          done;
         );
         *)
        "json_test" >:: (fun _ctx ->
          assert_equal (RN.And (RN.Test (0,true),RN.And (RN.Test (1,true),RN.Test (2,false)))) (Eval.binary_to_pred 0 3 2 6);
          let json_node_base = Yojson.Basic.from_file "../../../dataset/base-node.json" in
          let json_edge_base = Yojson.Basic.from_file "../../../dataset/base-edge.json" in
          let json_protocol = Yojson.Basic.from_file "../../../dataset/base-named-structure.json" in
          let json_interface = Yojson.Basic.from_file "../../../dataset/base-interface.json" in
          let man0 = Eval.init_man json_node_base json_edge_base json_protocol json_interface None in
          assert_equal (Eval.StringMap.cardinal man0.protocols) 3;
          assert_equal ((Eval.binary_to_pred 0 4 3 12)) (Eval.parse_location_to_pred "leaf1" false man0);
          let (ip,netmask) = Eval.parse_ip_entry_string "1.2.3.4/24" in
          assert_equal netmask 24;
          assert_equal ip (1 lsl 24 + 2 lsl 16 + 3 lsl 8 + 4);
          let ip = Eval.parse_ip_string "4.5.6.7" in
          assert_equal ip (4 lsl 24 + 5 lsl 16 + 6 lsl 8 + 7);
          let pred0 = Eval.binary_to_pred 0 2 31 ip in
          assert_equal (RN.And (RN.Test (0,false),RN.Test (1,false))) pred0;
          assert_equal true (Eval.match_ip_string (1 lsl 24 + 2 lsl 16 + 3 lsl 8 + 4) (1 lsl 24 + 1 lsl 23 +7 lsl 16 + 6 lsl 8 + 5) 8);
          let man = RN.init_man (Eval.get_field_length man0) (Eval.get_field_length man0) in
          let core1_loc = Eval.parse_location_to_pred "core1" false man0 in
          let core1_filter = RN.Binary (core1_loc, True) in
          let havocnk = RN.NK.Seq (RN.NK.Pkr Havoc, RN.NK.Star (RN.NK.Seq (RN.NK.Dup, RN.NK.Pkr Havoc))) in
          let id = RN.Rel.Id havocnk in
          let relation = RN.Rel.SeqR (id, RN.Rel.SeqR (RN.Rel.Nil core1_filter, id)) in
          let network0 = Eval.json_to_network json_node_base man0 false ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let t = Sys.time() in
          let boolean = RN.emptiness_check man 0 1 2 3 (Some network0, Some relation) in
          assert_equal false boolean;
          Printf.printf "Base Test Constuction time: %fs\n" (Sys.time() -. t);
          let pred1 = Eval.parse_location_to_pred "core1" true man0 in
          let pkr1 = Eval.parse_location_to_pkr "core1" true man0 in
          let pkr2 = (RN.AndP (RN.Binary (pred1,RN.True),RN.Id)) in
          let bdd1 = RN.compile_pkr_bdd man 0 1 pkr2 in
          let bdd2 = RN.compile_pkr_bdd man 0 1 (Comp (pkr2,pkr1)) in
          assert_equal ~cmp:MLBDD.equal bdd1 bdd2;
          let pkr3 = (RN.Binary (pred1,RN.True)) in
          let bdd3 = RN.compile_pkr_bdd man 0 1 (AndP (pkr3,pkr2)) in
          assert_equal ~cmp:MLBDD.equal bdd3 bdd2;
          let bdd4 = RN.compile_pred_bdd man 0 (Eval.get_ge_pred 0 15 0) in
          assert_equal ~cmp:MLBDD.equal (RN.bdd_true man) bdd4;
          let bdd5 = RN.compile_pred_bdd man 0 (And (Eval.get_ge_pred 0 15 80, Eval.get_le_pred 0 15 80)) in
          let bdd6 = RN.compile_pred_bdd man 0 (Eval.binary_to_pred 0 16 15 80) in
          assert_equal ~cmp:MLBDD.equal bdd5 bdd6;
          let json_node_base_1 = Yojson.Basic.from_file "../../../dataset/change1-node.json" in
          let json_edge_base_2 = Yojson.Basic.from_file "../../../dataset/change1-edge.json" in
          let man1 = Eval.init_man json_node_base_1 json_edge_base_2 json_protocol json_interface None in
          let network1 = Eval.json_to_network json_node_base_1 man1 false ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let core1_loc = Eval.parse_location_to_pred "core1" false man1 in
          let core1_filter = (RN.AndP (Id,RN.Binary (core1_loc, True))) in
          let relation = RN.Rel.SeqR (id, RN.Rel.SeqR (RN.Rel.Nil core1_filter, id)) in
          let t = Sys.time() in
          let boolean = RN.emptiness_check man 0 1 2 3 (Some network1, Some relation) in
          assert_equal true boolean;
          Printf.printf "Change 1 Test time: %fs\n" (Sys.time() -. t);
          let epsilon = RN.Rel.Left (RN.NK.Seq (RN.NK.Pkr Havoc ,RN.NK.Star (RN.NK.Seq (RN.NK.Dup,(RN.NK.Pkr Havoc))))) in
          let relation2 = RN.Rel.SeqR (epsilon, RN.Rel.SeqR (RN.Rel.App (core1_filter,Id), epsilon)) in
          let t = Sys.time() in
          let boolean2 = RN.emptiness_check man 0 1 2 3 (Some network1, Some relation2) in
          assert_equal true boolean2;
          Printf.printf "Test time (optmized): %fs\n" (Sys.time() -. t);
          let dup_free_network0 = Eval.json_to_network json_node_base man0 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let dup_free_network1 = Eval.json_to_network json_node_base_1 man1 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let t = Sys.time() in
          let (nkrobsmap3, start3) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network0, Some id) true in
          Printf.printf "Compiled time (Test 1): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let (nkrobsmap4, start4) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network1, Some id) true in
          Printf.printf "Compiled time (Test 2): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean3 = (RN.bisim man 2 3 start3 start4 nkrobsmap3 nkrobsmap4) in
          Printf.printf "Bisimulation time (Test 2): %fs\n" (Sys.time() -. t);
          assert_equal false boolean3;
          let json_node_base_2 = Yojson.Basic.from_file "../../../dataset/change2-node.json" in
          let json_edge_base_2 = Yojson.Basic.from_file "../../../dataset/change2-edge.json" in
          let man2 = Eval.init_man json_node_base_2 json_edge_base_2 json_protocol json_interface None in
          let network2 = Eval.json_to_network json_node_base_2 man2 false ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let core1_loc = Eval.parse_location_to_pred "core1" false man2 in
          let core1_filter = RN.Binary (core1_loc, True) in
          let relation = RN.Rel.SeqR (id, RN.Rel.SeqR (RN.Rel.Nil core1_filter, id)) in
          let t = Sys.time() in
          let boolean4 = RN.emptiness_check man 0 1 2 3 (Some network2, Some relation) in
          assert_equal true boolean4;
          Printf.printf "Test time (Test 3): %fs\n" (Sys.time() -. t);
          let dup_free_network2 = Eval.json_to_network json_node_base_2 man2 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db";"host-www"] in
          let t = Sys.time() in
          let (nkrobsmap6, start6) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network2, Some id) true in
          Printf.printf "Compiled time (Test 4): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean5 = (RN.bisim man 2 3 start3 start6 nkrobsmap3 nkrobsmap6) in
          Printf.printf "Bisimulation time (Test 4): %fs\n" (Sys.time() -. t);
          assert_equal true boolean5;
          let json_node_base_3 = Yojson.Basic.from_file "../../../dataset/change3-node.json" in
          let json_edge_base_3 = Yojson.Basic.from_file "../../../dataset/change3-edge.json" in
          let json_protocol_3 = Yojson.Basic.from_file "../../../dataset/change3-named-structure.json" in
          let json_interface_3 = Yojson.Basic.from_file "../../../dataset/change3-interface.json" in
          let man3 = Eval.init_man json_node_base_3 json_edge_base_3 json_protocol_3 json_interface_3 None in
          let network3 = Eval.json_to_network json_node_base_3 man3 false ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-www"] in
          let pred2 = Eval.parse_tcp_filter "www" man3 in
          let filter = RN.Binary (pred2, True) in
          let relation = RN.Rel.SeqR (RN.Rel.Nil filter, id) in
          let t = Sys.time() in
          let boolean6 = RN.emptiness_check man 0 1 2 3 (Some network3, Some relation) in
          assert_equal false boolean6;
          Printf.printf "Test time (Test 5): %fs\n" (Sys.time() -. t);
          let dup_free_network3 = Eval.json_to_network json_node_base_3 man3 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db"] in
          let dup_free_network4 = Eval.json_to_network json_node_base man0 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db"] in
          let t = Sys.time() in
          let (nkrobsmap8, start8) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network3, Some relation) true in
          let (nkrobsmap9, start9) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network4, Some relation) true in
          Printf.printf "Compiled time (Test 5): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean7 = (RN.bisim man 2 3 start8 start9 nkrobsmap8 nkrobsmap9) in
          Printf.printf "Bisimulation time (Test 5): %fs\n" (Sys.time() -. t);
          assert_equal false boolean7;
          let json_node_base_4 = Yojson.Basic.from_file "../../../dataset/change4-node.json" in
          let json_edge_base_4 = Yojson.Basic.from_file "../../../dataset/change4-edge.json" in
          let json_protocol_4 = Yojson.Basic.from_file "../../../dataset/change4-named-structure.json" in
          let json_interface_4 = Yojson.Basic.from_file "../../../dataset/change4-interface.json" in
          let man4 = Eval.init_man json_node_base_4 json_edge_base_4 json_protocol_4 json_interface_4 None in
          let network5 = Eval.json_to_network json_node_base_4 man4 false ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-www"] in
          let pred3 = Eval.parse_tcp_filter "www" man4 in
          let filter = RN.Binary (pred3, True) in
          let relation = RN.Rel.SeqR (RN.Rel.Nil filter, id) in
          let t = Sys.time() in
          let boolean8 = RN.emptiness_check man 0 1 2 3 (Some network5, Some relation) in
          assert_equal false boolean8;
          Printf.printf "Test time (Test 5): %fs\n" (Sys.time() -. t);
          let dup_free_network5 = Eval.json_to_network json_node_base_4 man4 true ["border1[GigabitEthernet0/0]";"border2[GigabitEthernet0/0]"] ["host-db"] in
          let t = Sys.time() in
          let (nkrobsmap11, start11) = RN.projection_compiler man 0 1 2 3 (Some dup_free_network5, Some relation) true in
          Printf.printf "Compiled time (Test 6): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean9 = (RN.bisim man 2 3 start9 start11 nkrobsmap9 nkrobsmap11) in
          Printf.printf "Bisimulation time (Test 6): %fs\n" (Sys.time() -. t);
          assert_equal true boolean9;
          let relation3 = RN.Rel.Binary ((RN.NK.Seq (RN.NK.Pkr Havoc ,RN.NK.Star (RN.NK.Seq (RN.NK.Dup,(RN.NK.Pkr Havoc))))),RN.NK.Pkr Havoc) in
          let relation4 = RN.Rel.SeqR (RN.Rel.Nil Id, RN.Rel.SeqR (relation3, RN.Rel.Nil Id)) in
          let relation5 = RN.Rel.OrR (RN.SR.add relation4 (RN.SR.add relation RN.SR.empty)) in
          let t = Sys.time() in
          let (nkrobsmap12, start12) = RN.projection_compiler man 0 1 2 3 (Some network2, Some relation5) true in
          Printf.printf "Compiled time (Test 7): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean10 = (RN.bisim man 2 3 start3 start12 nkrobsmap3 nkrobsmap12) in
          Printf.printf "Bisimulation time (Test 7): %fs\n" (Sys.time() -. t);
          assert_equal true boolean10;
          let t = Sys.time() in
          let (nkrobsmap13, start13) = RN.projection_compiler man 0 1 2 3 (Some network1, Some relation5) true in
          Printf.printf "Compiled time (Test 8): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean11 = (RN.bisim man 2 3 start13 start12 nkrobsmap13 nkrobsmap12) in
          Printf.printf "Bisimulation time (Test 8): %fs\n" (Sys.time() -. t);
          assert_equal false boolean11;
          let json_node_base_5 = Yojson.Basic.from_file "../../../dataset/acl-node.json" in
          let json_edge_base_5 = Yojson.Basic.from_file "../../../dataset/acl-edge.json" in
          let json_protocol_5 = Yojson.Basic.from_file "../../../dataset/acl-named-structure.json" in
          let json_interface_5 = Yojson.Basic.from_file "../../../dataset/acl-interface.json" in
          let man5 = Eval.init_man json_node_base_5 json_edge_base_5 json_protocol_5 json_interface_5 None in
          let network6 = Eval.json_to_network json_node_base_5 man5 false ["firewall[GigabitEthernet0/0/2]"] ["firewall[GigabitEthernet0/0/3]"] in
          let pred4 = Eval.parse_tcp_filter "http" man5 in
          let srcip_filter = Eval.parse_src_ip_filter "10.114.64.1" man5 in
          let dstip_filter = Eval.parse_dst_ip_filter "10.114.60.10" man5 in
          let filter = RN.Binary (RN.And (pred4, RN.And (srcip_filter, dstip_filter)), True) in
          let relation6 = RN.Rel.SeqR (RN.Rel.Nil filter, RN.Rel.StarR (RN.Rel.App (Id,Id))) in
          let t = Sys.time() in
          let boolean12 = RN.emptiness_check man 0 1 2 3 (Some network6, Some relation6) in
          assert_equal false boolean12;
          Printf.printf "Test time (Test 9): %fs\n" (Sys.time() -. t);
          let pred5 = Eval.parse_protocols_to_pred ["TCP"] man5 in
          let srcip_filter = Eval.parse_src_ip_filter "101.164.101.231" man5 in
          let dstip_filter = Eval.parse_dst_ip_filter "101.164.9.0/24" man5 in
          let ports_filter = Eval.parse_dstports_filter 2049 false man5 in
          let filter2 = RN.Binary (RN.And (pred5, RN.And (srcip_filter, RN.And (dstip_filter, ports_filter))), True) in
          let relation7 = RN.Rel.SeqR (RN.Rel.Nil filter2, RN.Rel.StarR (RN.Rel.App (Id,Id))) in
          let t = Sys.time() in
          let boolean13 = RN.emptiness_check man 0 1 2 3 (Some network6, Some relation7) in
          assert_equal false boolean13;
          Printf.printf "Test time (Test 10): %fs\n" (Sys.time() -. t);
          let json_node_base_6 = Yojson.Basic.from_file "../../../dataset/hybrid-node.json" in
          let json_edge_base_6 = Yojson.Basic.from_file "../../../dataset/hybrid-edge.json" in
          let json_protocol_6 = Yojson.Basic.from_file "../../../dataset/hybrid-named-structure.json" in
          let json_interface_6 = Yojson.Basic.from_file "../../../dataset/hybrid-interface.json" in
          let json_ipsec = Yojson.Basic.from_file "../../../dataset/hybrid-ipsec.json" in
          let man6 = Eval.init_man json_node_base_6 json_edge_base_6 json_protocol_6 json_interface_6 (Some json_ipsec) in
          let east2_private = "i-04cd3db5124a05ee6" in
          let east2_public = "i-01602d9efaed4409a" in
          let west2_private = "i-0a5d64b8b58c6dd09" in
          let west2_public = "i-02cae6eaa9edeed70" in
          let man' = RN.init_man (Eval.get_field_length man6) (Eval.get_field_length man6) in
          let network7 = Eval.json_to_network json_node_base_6 man6 false [east2_private] [east2_public] in
          let pred6 = Eval.parse_tcp_filter "ssh" man6 in
          let pred6' = Eval.parse_dst_ip_filter "10.20.1.207" man6 in
          let relation8 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (RN.And (pred6,pred6'), True)), id) in
          let t = Sys.time() in
          let boolean14 = RN.emptiness_check man' 0 1 2 3 (Some network7, Some relation8) in
          assert_equal false boolean14;
          Printf.printf "Test time (Test 11): %fs\n" (Sys.time() -. t);
          let network8 = Eval.json_to_network json_node_base_6 man6 false [east2_public] [west2_public] in
          let pred7 = Eval.parse_dst_ip_filter "10.40.2.80" man6  in
          let relation9 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (pred7, True)), id) in
          let t = Sys.time() in
          let boolean15 = RN.emptiness_check man' 0 1 2 3 (Some network8, Some relation9) in
          assert_equal true boolean15;
          Printf.printf "Test time (Test 12): %fs\n" (Sys.time() -. t);
          let pred8 = Eval.parse_dst_ip_filter "54.191.42.182" man6  in
          let relation10 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (pred8, True)), id) in
          let t = Sys.time() in
          let boolean16 = RN.emptiness_check man' 0 1 2 3 (Some network8, Some relation10) in
          assert_equal true boolean16;
          Printf.printf "Test time (Test 13): %fs\n" (Sys.time() -. t);
          let gateway_json_1 = Yojson.Basic.from_file "../../../dataset/us-west-2/InternetGateways.json" in
          let internet_gateway_1 = Eval.parse_internet_gateways gateway_json_1 in
          let switches_json_1 = Yojson.Basic.from_file "../../../dataset/us-west-2/NetworkInterfaces.json" in
          let gateway_json_2 = Yojson.Basic.from_file "../../../dataset/us-east-2/InternetGateways.json" in
          let internet_gateway_2 = Eval.parse_internet_gateways gateway_json_2 in
          let switches_json_2 = Yojson.Basic.from_file "../../../dataset/us-east-2/NetworkInterfaces.json" in
          let updated_man_2 = Eval.add_ip_switches switches_json_1 internet_gateway_1 man6 in
          let updated_man = Eval.add_ip_switches switches_json_2 internet_gateway_2 updated_man_2 in
          let network9 = Eval.json_to_network json_node_base_6 updated_man false [east2_public] [west2_public] in
          let pred9 = Eval.parse_dst_ip_filter "54.191.42.182" updated_man in
          let pred9' = Eval.parse_dst_ip_filter "10.40.2.80" updated_man in
          let relation11 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (pred9, True)), RN.Rel.SeqR (id,RN.Rel.Nil (RN.Binary (pred9', True)))) in
          let t = Sys.time() in
          let boolean17 = RN.emptiness_check man' 0 1 2 3 (Some network9, Some relation11) in
          assert_equal false boolean17;
          Printf.printf "Test time (Test 14): %fs\n" (Sys.time() -. t);
          let network10 = Eval.json_to_network json_node_base_6 updated_man false ["srv-101"] [east2_public] in
          let pred10 = Eval.parse_dst_ip_filter "13.59.144.125" updated_man in
          let relation12 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (pred10, True)), id) in
          let t = Sys.time() in
          let boolean18 = RN.emptiness_check man' 0 1 2 3 (Some network10, Some relation12) in
          assert_equal false boolean18;
          Printf.printf "Test time (Test 15): %fs\n" (Sys.time() -. t);
          let pred11 = Eval.parse_dst_ip_filter "10.20.1.207" updated_man in
          let relation13 = RN.Rel.SeqR (RN.Rel.Nil (RN.Binary (pred11, True)), id) in
          let t = Sys.time() in
          let boolean19 = RN.emptiness_check man' 0 1 2 3 (Some network10, Some relation13) in
          assert_equal false boolean19;
          Printf.printf "Test time (Test 16): %fs\n" (Sys.time() -. t);
          let pred12 = RN.Neg (Or (Eval.parse_dst_ip_filter_list ["54.191.42.182";"10.40.2.80";"13.59.144.125";"10.20.1.207"] updated_man,
          Eval.parse_src_ip_filter_list ["54.191.42.182";"10.40.2.80";"13.59.144.125";"10.20.1.207"] updated_man )) in
          let pkr12 = RN.AndP (Binary (pred12, True), Id) in
          let relation14 = RN.Rel.Apply (pkr12,havocnk) in
          let t = Sys.time() in
          let network11 = Eval.json_to_network json_node_base_6 man6 false [] [] in
          let (nkrobsmap22, start22) = RN.projection_compiler man' 0 1 2 3 (Some network11, Some relation14) true in
          let network12 = Eval.json_to_network json_node_base_6 updated_man false [] [] in
          let (nkrobsmap23, start23) = RN.projection_compiler man' 0 1 2 3 (Some network12, Some relation14) true in
          Printf.printf "Compiled time (Test 17): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean20 = (RN.bisim man' 2 3 start22 start23 nkrobsmap22 nkrobsmap23) in
          Printf.printf "Bisimulation time (Test 17): %fs\n" (Sys.time() -. t);
          assert_equal true boolean20;
          let network13 = Eval.json_to_network json_node_base_6 updated_man_2 false [] [] in
          let gateway_pred = Eval.parse_location_to_pred "igw-02fd68f94367a67c7" false updated_man_2 in
          let backbone_pred = Eval.parse_location_to_pred "isp_16509" false updated_man_2 in
          let gateway_pkr = Eval.parse_location_to_pkr "igw-02fd68f94367a67c7" false updated_man_2 in
          let backbone_pkr = Eval.parse_location_to_pkr "isp_16509" false updated_man_2 in
          let dst_ip_pred = Eval.parse_dst_ip_filter "13.59.144.125" updated_man_2 in
          let src_ip_pred = Eval.parse_src_ip_filter "10.20.1.207" updated_man_2 in
          let dst_ip_pkr = Eval.parse_dst_ip_pkr "10.20.1.207" updated_man_2 in
          let src_ip_pkr = Eval.parse_src_ip_pkr "13.59.144.125" updated_man_2 in
          let pkr13 = RN.Binary (And (gateway_pred,src_ip_pred), backbone_pred) in
          let pkr14 = RN.Binary (And (backbone_pred,dst_ip_pred), gateway_pred) in
          let pkr15 = RN.NegP (RN.OrP (pkr13,pkr14)) in
          let pkr16 = RN.AndP (pkr13, RN.Comp (src_ip_pkr,backbone_pkr)) in
          let pkr17 = RN.AndP (pkr14, RN.Comp (dst_ip_pkr,gateway_pkr)) in
          let pkr18 = RN.NegP (RN.OrP (pkr16, pkr17)) in
          let filternk = RN.NK.Star (RN.NK.Seq (RN.NK.Pkr pkr15, RN.NK.Dup)) in
          let relation15 = RN.Rel.Id filternk in
          let relation16 = RN.Rel.Id (RN.NK.Star (RN.NK.Seq (RN.NK.Pkr pkr18, RN.NK.Dup))) in
          let t = Sys.time() in 
          let (nkrobsmap24, start24) = RN.projection_compiler man' 0 1 2 3 (Some network12, Some relation15) true in
          let (nkrobsmap25, start25) = RN.projection_compiler man' 0 1 2 3 (Some network13, Some relation15) true in
          Printf.printf "Compiled time (Test 18): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean21 = (RN.bisim man' 2 3 start24 start25 nkrobsmap24 nkrobsmap25) in
          Printf.printf "Bisimulation time (Test 18): %fs\n" (Sys.time() -. t);
          assert_equal true boolean21;
          let (nkrobsmap26, start26) = RN.projection_compiler man' 0 1 2 3 (Some network12, Some (RN.Rel.Id network13)) true in
          Printf.printf "Compiled time (Test 19): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean22 = (RN.bisim man' 2 3 start24 start26 nkrobsmap24 nkrobsmap26) in
          Printf.printf "Bisimulation time (Test 19): %fs\n" (Sys.time() -. t);
          assert_equal true boolean22;
          let boolean23 = RN.emptiness_check man' 0 1 2 3 (Some (RN.NK.Diff (network12,network13)), Some relation16) in
          assert_equal true boolean23;
          let man_2 = Eval.init_man_disable_tunnel json_node_base_6 json_edge_base_6 json_protocol_6 json_interface_6 (Some json_ipsec) in
          let network14 = Eval.json_to_network json_node_base_6 man_2 false [] [] in
          let network11 = Eval.json_to_network json_node_base_6 man6 false [] [] in
          let t = Sys.time() in
          let (nkrobsmap27, start27) = RN.projection_compiler man' 0 1 2 3 (Some network14, Some id) true in
          let (nkrobsmap28, start28) = RN.projection_compiler man' 0 1 2 3 (Some network11, Some id) true in
          Printf.printf "Compiled time (Test 20): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean24 = (RN.bisim man' 2 3 start27 start28 nkrobsmap27 nkrobsmap28) in
          Printf.printf "Bisimulation time (Test 20): %fs\n" (Sys.time() -. t);
          assert_equal true boolean24;
          let network16 = Eval.encrypted_json_to_network json_node_base_6 man_2 false [west2_private] [] [] in
          let pkr17 = Eval.encrypt_packet_relation man_2 [west2_private] in
          let t = Sys.time() in
          let (nkrobsmap29, start29) = RN.projection_compiler man' 0 1 2 3 (Some network16, Some id) true in
          let (nkrobsmap30, start30) = RN.projection_compiler man' 0 1 2 3 (Some network14, Some (RN.Rel.Apply (pkr17,havocnk))) true in
          Printf.printf "Compiled time (Test 21): %fs\n" (Sys.time() -. t);
          let t = Sys.time() in
          let boolean25 = (RN.bisim man' 2 3 start29 start30 nkrobsmap29 nkrobsmap30) in
          Printf.printf "Bisimulation time (Test 21): %fs\n" (Sys.time() -. t);
          assert_equal true boolean25;
          );

      ]

let _ =
  run_test_tt_main begin "all" >::: [
      tests;
    ] end;
