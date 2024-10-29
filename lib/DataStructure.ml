[@@@ocaml.warning "-37"] 
[@@@ocaml.warning "-32"] 
[@@@ocaml.warning "-27"] 


(* The first r denote the state, as we use residual string to represent states *)
(* The second pred denote the additional predicate we need to label the state, such as x =1 *)
(* The last BDD records the transition from current state to next state *)

type field = int
type pk = int

type pred =
  | True
  | False
  | Test of field * bool
  | And of pred * pred
  | Or of pred * pred
  | Neg of pred
  
type pkr =
  | Id
  | Empty
  | LeftTest of field * bool 
  | RightTest of field * bool
  | LeftAsgn of field * bool
  | RightAsgn of field * bool
  | Eqf of field
  | Comp of pkr * pkr
  | Or of pkr * pkr
  | And of pkr * pkr
  | Neg of pkr

type netkat =
  | Pred of pred
  | Asgn of field * bool
  | Union of netkat * netkat
  | Seq of netkat * netkat
  | Star of netkat
  | Dup

type rel =
  | Left of pred
  | Right of pred
  | Binary of pkr
  | OrR of rel * rel
  | SeqR of rel * rel
  | StarR of rel
  
let pk_max = 0
(* The variable is in order of x x' y y' --> 4k, 4k+1, 4k+2, 4k+3*)
let bddvar pk field = 10*field+pk

let generate_single_var (man:MLBDD.man) (pk:pk) (field:field):MLBDD.t =
    MLBDD.ithvar man (bddvar pk field)

let compile_pred_bdd (man:MLBDD.man)(pk:pk) (predicate:pred):MLBDD.t = 
     let rec compile_pred_bdd_aux (predicate:pred):MLBDD.t =
	match predicate with
    		| True -> MLBDD.dtrue man
    		| False -> MLBDD.dfalse man
  		| Test (field,false) -> MLBDD.dnot (generate_single_var man pk field)
  		| Test (field,true) -> generate_single_var man pk field
  		| And (pred1,pred2) -> MLBDD.dand (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| Or (pred1,pred2) -> MLBDD.dor (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| Neg predicate -> MLBDD.dnot (compile_pred_bdd_aux predicate)
  	in compile_pred_bdd_aux predicate

let produce_id (man:MLBDD.man) (pk1:pk) (pk2:pk):MLBDD.t =
     let rec produce_id_aux (cur:field):MLBDD.t =
         if cur > pk_max then 
          MLBDD.dtrue man
         else  
          MLBDD.dand (MLBDD.nxor (generate_single_var man pk1 cur) ((generate_single_var man pk2 cur))) (produce_id_aux (cur+1))
     in produce_id_aux 0

let produce_assign (man:MLBDD.man) (pk1:pk) (pk2:pk) (bvar:int)(asgn:bool) (left:bool):MLBDD.t =
     let rec produce_assign_aux (cur:field):MLBDD.t =
         if cur > pk_max then 
            MLBDD.dtrue man
         else if left && (bvar = (bddvar pk1 cur)) then 
                   MLBDD.dand (if asgn then 
                                  (generate_single_var man pk1 cur)
                               else 
                                  MLBDD.dnot (generate_single_var man pk1 cur))
                              (produce_assign_aux (cur+1))         
         else if (not left) && (bvar = (bddvar pk2 cur)) then
                   MLBDD.dand (if asgn then 
                   		          (generate_single_var man pk2 cur) 
                   	          else 
                                MLBDD.dnot (generate_single_var man pk2 cur)) 
                   	       (produce_assign_aux (cur+1))         
         else 
            MLBDD.dand (MLBDD.nxor (generate_single_var man pk1 cur) (generate_single_var man pk2 cur)) (produce_assign_aux (cur+1))
     in produce_assign_aux 0
     
let generate_unused_pk (pk1:pk) (pk2:pk):pk =
  match (pk1,pk2) with
  |(0,1) ->2   
  |(1,0) ->2   
  |(0,_) ->1   
  |(_,0) ->1
  | _ -> 0

let generate_support (pk:pk):MLBDD.support =
  let rec generate_list (cur:field):int list =
     if cur > pk_max then []
     else (bddvar pk cur)::(generate_list (cur+1))
  in MLBDD.support_of_list (generate_list 0)

  
let comp_bdd (man:MLBDD.man) (pk1:pk) (pk2:pk) (compiler:MLBDD.man -> pk -> pk -> 'a -> MLBDD.t) (con1: 'a) (con2: 'a):MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    MLBDD.exists (generate_support pk3) (MLBDD.dand (compiler man pk1 pk3 con1) (compiler man pk3 pk2 con2))
      
let rec compile_pkr_bdd (man:MLBDD.man)(pk1:pk) (pk2:pk) (pkr:pkr):MLBDD.t = 
     let rec compile_pkr_bdd_aux (pkr:pkr):MLBDD.t =
	match pkr with
	  | Id -> produce_id man pk1 pk2
	  | Empty -> MLBDD.dfalse man
	  | LeftTest (field, false) -> MLBDD.dnot (generate_single_var man pk1 field)
	  | LeftTest (field, true) -> generate_single_var man pk1 field
	  | RightTest (field, false) -> MLBDD.dnot (generate_single_var man pk2 field)
	  | RightTest (field, true) -> generate_single_var man pk2 field
	  | LeftAsgn (field, b) -> produce_assign man pk1 pk2 (bddvar pk1 field) b true  
	  | RightAsgn (field, b) -> produce_assign man pk1 pk2 (bddvar pk2 field) b false  
	  | Eqf field -> MLBDD.nxor (generate_single_var man pk1 field) (generate_single_var man pk2 field)
	  | Comp (pkr1, pkr2) -> comp_bdd man pk1 pk2 compile_pkr_bdd pkr1 pkr2
    | Or (pkr1,pkr2)-> MLBDD.dor (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
  	| And (pkr1,pkr2)-> MLBDD.dand (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
  	| Neg pkr -> MLBDD.dnot (compile_pkr_bdd_aux pkr)
  	in compile_pkr_bdd_aux pkr

(* A naive implementation, to be optimized*)    
let closure_bdd (man:MLBDD.man) (pk1:pk) (pk2:pk) (compiler:MLBDD.man -> pk -> pk -> 'a -> MLBDD.t) (con:'a) :MLBDD.t =
  (* input cur is of pk1 and pk2 *)
  let rec closure_bdd_aux (pk1:pk) (pk2:pk) (cur:MLBDD.t):MLBDD.t =
    let pk3 = generate_unused_pk pk1 pk2 in
      let support = generate_support pk2 in
        let id23 = (produce_id man pk2 pk3) in
         let next = MLBDD.exists support (MLBDD.dand cur (compiler man pk2 pk3 con)) in
          if MLBDD.equal (MLBDD.exists support (MLBDD.dand cur id23)) next then
	                cur
  	            else 
                  (MLBDD.exists support (MLBDD.dand(closure_bdd_aux pk1 pk3 next) id23))
  in closure_bdd_aux pk1 pk2 (produce_id man pk1 pk2)  	 

let rec nk_included (nk1:netkat) (nk2:netkat) :bool=
   match (nk1,nk2) with
   | (Union (nk11,nk12),_) -> (nk_included nk11 nk2)&&(nk_included nk12 nk2)
   | (_,Union (nk21,nk22))-> (nk_included nk1 nk21)||(nk_included nk1 nk22)
   | _ -> nk1 = nk2


let canoicalize_nk (nk:netkat):netkat=
   let rec canoicalize_nk_aux (nk1:netkat) (nk2:netkat):netkat=
      match nk1 with
     | Union (nk11,nk12) -> canoicalize_nk_aux nk11 (canoicalize_nk_aux nk12 nk2)
     | _ -> if nk_included nk1 nk2 then
            nk2
            else Union (nk1,nk2)
    in canoicalize_nk_aux nk (Pred False)       

let nk_equivalent (nk1:netkat) (nk2:netkat):bool=
   (nk_included nk1 nk2)&&(nk_included nk2 nk1)

let rec r_included (r1:rel) (r2:rel) :bool=
   match (r1,r2) with
   | (OrR (r11,r12),_) -> (r_included r11 r2)&&(r_included r12 r2)
   | (_,OrR (r21,r22))-> (r_included r1 r21)||(r_included r1 r22)
   | _ -> r1 = r2

let canoicalize_r (r:rel):rel=
   let rec canoicalize_r_aux (r1:rel) (r2:rel):rel=
      match r1 with
     | OrR (r11,r12) -> canoicalize_r_aux r11 (canoicalize_r_aux r12 r2)
     | _ -> if r_included r1 r2 then
            r2
            else OrR (r1,r2)
    in canoicalize_r_aux r (Binary Empty)       
   
let r_equivalent (r1:rel) (r2:rel):bool=
   (r_included r1 r2)&&(r_included r2 r1)

let nkr_equivalent (nkr1:netkat*rel) (nkr2:netkat*rel):bool =
  (nk_equivalent (fst nkr1) (fst nkr2))&&(r_equivalent (snd nkr1) (snd nkr2))

let canoicalize_nkr (nkr:netkat*rel):netkat*rel=
  ((canoicalize_nk (fst nkr)),(canoicalize_r (snd nkr)))

(* We assume the invariant here is the mapping is canoicalized *)      
let add_mapping (con:'a) (bdd:MLBDD.t) (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
      let rec update_mapping (con:'a) (bdd:MLBDD.t) (mapping:('a*MLBDD.t)list) =
            match mapping with
              | [] ->[(con,bdd)]
              | (conh,bddh)::tl -> if equiv con conh then
                                    (conh,MLBDD.dor bdd bddh)::tl
                                  else (conh,bddh)::(update_mapping con bdd tl)
      in
         if MLBDD.is_false bdd then
	        mapping
	      else
          update_mapping (norm con) bdd mapping  

let add_nk_mapping (nk:netkat) (bdd:MLBDD.t) (mapping:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
  add_mapping nk bdd nk_equivalent canoicalize_nk mapping

let add_nko_mapping (nko:netkat option) (bdd:MLBDD.t) (mapping:(netkat option*MLBDD.t)list):(netkat option*MLBDD.t)list=
  add_mapping nko bdd (Option.equal nk_equivalent) (Option.map canoicalize_nk) mapping

let add_r_mapping (rel:rel) (bdd:MLBDD.t) (mapping:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
  add_mapping rel bdd r_equivalent canoicalize_r mapping

let add_ro_mapping (relo:rel option) (bdd:MLBDD.t) (mapping:(rel option*MLBDD.t)list):(rel option*MLBDD.t)list=
  add_mapping relo bdd (Option.equal r_equivalent) (Option.map canoicalize_r) mapping

let add_nkro_mapping (con:(netkat*rel) option) (bdd:MLBDD.t) (mapping:((netkat*rel) option*MLBDD.t)list):((netkat*rel) option*MLBDD.t)list=
  add_mapping con bdd (Option.equal nkr_equivalent) (Option.map canoicalize_nkr) mapping

  (* We assume the invariant here is the arguments are canoicalized *)      
let rec union_mapping (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(mapping1:('a*MLBDD.t)list) (mapping2:('a*MLBDD.t)list):('a*MLBDD.t)list=
   match mapping1 with
   | [] -> mapping2
   | (con,bdd)::tl -> add_mapping con bdd equiv norm (union_mapping equiv norm tl mapping2)

let union_nk_mapping (mapping1:(netkat*MLBDD.t)list) (mapping2:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
  union_mapping nk_equivalent canoicalize_nk mapping1 mapping2

let union_nko_mapping (mapping1:(netkat option*MLBDD.t)list) (mapping2:(netkat option*MLBDD.t)list):(netkat option*MLBDD.t)list=
  union_mapping (Option.equal nk_equivalent) (Option.map canoicalize_nk) mapping1 mapping2

let union_r_mapping (mapping1:(rel*MLBDD.t)list) (mapping2:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
  union_mapping r_equivalent canoicalize_r mapping1 mapping2

let union_ro_mapping (mapping1:(rel option*MLBDD.t)list) (mapping2:(rel option*MLBDD.t)list):(rel option*MLBDD.t)list=
  union_mapping (Option.equal r_equivalent) (Option.map canoicalize_r) mapping1 mapping2

let union_nkro_mapping (mapping1:((netkat*rel) option*MLBDD.t)list) (mapping2:((netkat*rel) option*MLBDD.t)list):((netkat*rel) option*MLBDD.t)list=
  union_mapping (Option.equal nkr_equivalent) (Option.map canoicalize_nkr) mapping1 mapping2
  
let canonicalize (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
   union_mapping equiv norm mapping []

let canonicalize_nk_mapping (mapping:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
   canonicalize nk_equivalent canoicalize_nk mapping

let canonicalize_nko_mapping (mapping:(netkat option*MLBDD.t)list):(netkat option*MLBDD.t)list=
   canonicalize (Option.equal nk_equivalent) (Option.map canoicalize_nk) mapping

let canonicalize_r_mapping (mapping:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
   canonicalize r_equivalent canoicalize_r mapping

let canonicalize_ro_mapping (mapping:(rel option*MLBDD.t)list):(rel option*MLBDD.t)list=
   canonicalize (Option.equal r_equivalent) (Option.map canoicalize_r) mapping

let canonicalize_nkro_mapping (mapping:((netkat*rel) option*MLBDD.t)list):((netkat*rel) option*MLBDD.t)list=
   canonicalize (Option.equal nkr_equivalent) (Option.map canoicalize_nkr) mapping
   
let apply_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
  (List.filter_map (fun (a,bdd)-> let nbdd = tobdd bdd in 
                                    if (MLBDD.is_false nbdd) then
                                       None
                                    else Some (a,nbdd)) mapping)

let concatenate_mapping (mapping:('a*MLBDD.t)list) (seq:'a*'a->'a)(con:'a):('a*MLBDD.t)list=
   (List.map (fun (a,b)-> (seq (a,con),b)) mapping)

let concatenate_nk_mapping (mapping:(netkat*MLBDD.t)list) (nk:netkat):(netkat*MLBDD.t)list=
  concatenate_mapping mapping (fun (a,b)->Seq (a,b)) nk

let concatenate_nko_mapping (mapping:(netkat option*MLBDD.t)list) (nko:netkat option):(netkat option*MLBDD.t)list=
  concatenate_mapping mapping (fun (nko1,nko2)->match (nko1,nko2) with
                                          | (None,_) -> nko2
                                          | (_, None) -> nko1
                                          | (Some nk1,Some nk2) -> Some (Seq (nk1,nk2))
                                                      ) nko

let concatenate_r_mapping (mapping:(rel*MLBDD.t)list) (rel:rel):(rel*MLBDD.t)list=
  concatenate_mapping mapping (fun (a,b)->SeqR (a,b)) rel

let concatenate_ro_mapping (mapping:(rel option*MLBDD.t)list) (relo:rel option):(rel option*MLBDD.t)list=
  concatenate_mapping mapping (fun (ro1,ro2)->match (ro1,ro2) with
                                                  | (None,_) -> ro2
                                                  | (_, None) -> ro1
                                                  | (Some r1,Some r2) -> Some (SeqR (r1,r2))
                                                        ) relo

let concatenate_nkro_mapping (mapping:((netkat*rel) option*MLBDD.t)list) (con:(netkat*rel) option):((netkat*rel) option*MLBDD.t)list=
  concatenate_mapping mapping (fun (nkro1,nkro2)->match (nkro1,nkro2) with
                                                      | (None,_) -> nkro2
                                                      | (_,None) -> nkro1
                                                      | (Some (nk1,r1),Some (nk2,r2)) ->Some (Seq (nk1,nk2),SeqR(r1,r2))
  ) con

let folding_epsilon (man:MLBDD.man) (nkol:(netkat option*MLBDD.t)list):MLBDD.t =
  List.fold_left 
  (fun acc (nko,bdd)-> match nko with 
                            | None -> MLBDD.dor acc bdd
                            | _ -> acc) 
                            (MLBDD.dfalse man) nkol                                                        
(* We assume the invariant here is the return value is canoicalized *)
let rec delta_k (man:MLBDD.man)(pk1:pk)(pk2:pk)(nko:netkat option): (netkat option*MLBDD.t)list=
    match nko with
      | None -> []
    	| Some (Pred pred) -> [(None,MLBDD.dand (compile_pred_bdd man pk1 pred) (produce_id man pk1 pk2))]  
    	| Some (Asgn (field, b)) -> [(None,produce_assign man pk1 pk2 (bddvar pk1 field) b true)]
  	  | Some (Union(nk1,nk2)) -> union_nko_mapping  (delta_k man pk1 pk2 (Some nk1)) (delta_k man pk1 pk2 (Some nk2))
  	  | Some (Seq(nk1,nk2)) -> let pk3 =  generate_unused_pk pk1 pk2 in
                                  let support = generate_support pk3 in
                                    union_nko_mapping (concatenate_nko_mapping (delta_k man pk1 pk2 (Some nk1)) (Some nk2))
  	                                (let epsilon = folding_epsilon man (delta_k man pk1 pk3 (Some nk1)) in
                                      (apply_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) (delta_k man pk3 pk2 (Some nk2))))
  	  | Some (Star nk) -> concatenate_nko_mapping (let pk3 = generate_unused_pk pk1 pk2 in
                      	                      let support = generate_support pk3 in
                                                let epsilon = closure_bdd man pk1 pk3 (fun man pk1 pk2 nk 
                                                                                            -> folding_epsilon man (delta_k man pk1 pk2 (Some nk))) nk in                         
                                                 (apply_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) (delta_k man pk3 pk2 (Some nk)))) (Some (Star nk)) 
      | Some Dup -> [(Some (Pred True),produce_id man pk1 pk2)]
(* For epsilon kr, there is no transition on the y or the input tape, thus we only need two tape denoting the before
and after hidden state *)

(* A naive implementation, to be optimized*)
let rec delta_kr (man:MLBDD.man) (pk1:pk) (pk2:pk) (pk3:pk) (nkro:netkat*rel option): ((netkat*rel option)*MLBDD.t)list= 
  match nkro with
    | None -> []
    | Some (Left pred) ->                                            
    | Left pred -> []
    | Right pred -> [((nk,None), compile_pred_bdd man pk3 pred)]
    | Binary pkr ->  let bdd = compile_pkr_bdd man pk2 pk3 pkr in 
            (List.filter  (fun (a,b)-> not (MLBDD.is_false b)) (List.map (fun (nk,bdd') -> ((nk,None),MLBDD.dand bdd bdd')) (delta_k man pk1 pk2 nk)))                
    | OrR (r1,r2) -> union_nkro_mapping (delta_kr man pk1 pk2 pk3 nk r1) (delta_kr man pk1 pk2 pk3 nk r2)
    | SeqR (r1,r2) -> let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
                          let support = generate_support pk4 in
                            union_nkro_mapping (concatenate_nkro_mapping (delta_kr man pk1 pk2 pk4 nk r1) (nk,Some r2))
                              (let eps = epsilon_0_kr man pk1 pk4 nk r1 in 
                                List.fold_left (fun acc -> fun (nko,ebdd) -> union_nkro_mapping acc 
                                 (match nko with
                                 | Some nk -> List.map (fun (con,dbdd)-> (con, MLBDD.exists support (MLBDD.dand ebdd dbdd))) 
                                                (delta_kr man pk4 pk2 pk3 nk r2)
                                 | None -> [] )) [] eps)
    | StarR r -> let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
                    let support = generate_support pk4 in
     (concatenate_nkro_mapping  
        (let eps = epsilon_0_kr man pk1 pk4 nk (StarR r) in 
              List.fold_left (fun acc -> fun (nko,ebdd) -> union_nkro_mapping acc 
              (match nko with
                | Some nk -> List.map (fun (con,dbdd)-> (con, MLBDD.exists support (MLBDD.dand ebdd dbdd))) 
                       (delta_kr man pk4 pk2 pk3 nk r)
                | None -> [] )) [] eps) (nk,Some (StarR r)))
    
    
    
    
    
    

