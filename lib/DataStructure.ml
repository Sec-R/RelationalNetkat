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
let bddvar pk field = 4*field+pk

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

let closure_bdd (man:MLBDD.man) (pk1:pk) (pk2:pk) (compiler:MLBDD.man -> pk -> pk -> 'a -> MLBDD.t) (con:'a) :MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    let next_bdd = (compiler man pk3 pk2 con) in
      let rec closure_bdd_aux (cur:MLBDD.t):MLBDD.t =
        let next = MLBDD.exists (generate_support pk3) (MLBDD.dand cur next_bdd) in
          if MLBDD.equal cur next then
  	        cur
  	      else 
            closure_bdd_aux next
        in closure_bdd_aux (produce_id man pk1 pk2)  	 

let rec epsilon_k (man:MLBDD.man)(pk1:pk)(pk2:pk)(nk:netkat): MLBDD.t=
    match nk with
    | Pred pred -> compile_pred_bdd man pk1 pred
    | Asgn (field, b) -> produce_assign man pk1 pk2 (bddvar pk1 field) b true
  	| Union(nk1,nk2) -> MLBDD.dor (epsilon_k man pk1 pk2 nk1) (epsilon_k man pk1 pk2 nk2)
  	| Seq(nk1,nk2) -> comp_bdd man pk1 pk2 epsilon_k nk1 nk2
  	| Star(nk) -> closure_bdd man pk1 pk2 epsilon_k nk
    | Dup -> MLBDD.dfalse man   

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
  (k_equivalent (fst nkr1) (fst nkr2))&&(r_equivalent (snd nkr1) (snd nkr2))

let canoicalize_nkr (nkr:netkat*rel):netkat*rel=
  ((canoicalize_nk (fst nkr)),(canoicalize_nk (snd nkr)))

(* We assume the invariant here is the arguments are canoicalized *)      
let rec add_mapping (con:'a) (bdd:MLBDD.t) (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(union:'a *'a -> 'a)(mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
      let rec update_mapping_aux (con:'a) (bdd:MLBDD.t) (mapping:('a*MLBDD.t)list) =
            match mapping with
              | [] ->[(con,bdd)]
              | (conh,bddh)::tl -> if equiv con conh then
                                    (conh,MLBDD.dor bdd bddh)::tl
                                  else (conh,bddh)::(update_mapping_aux con bdd tl)
      in
      let update_mapping (con:'a) (bdd:MLBDD.t) (mapping:('a *MLBDD.t)list) =
        if  MLBDD.is_false bdd then
          mapping
        else 
          (update_mapping_aux con bdd mapping)
      in
         if MLBDD.is_false bdd then
	        mapping
	      else 
          match mapping with
	          | [] -> [con,bdd]
	          | (conh,bddh)::tl -> update_mapping 
	                                (norm (union (con,conh)))
	                                (MLBDD.dand bdd bddh)
	                                (update_mapping
	                                   conh 
	                                   (MLBDD.dand (MLBDD.dnot bdd) bddh)
	                                   (add_mapping 
	                                      con 
	                                      (MLBDD.dand (MLBDD.dnot bddh) bdd)
                                        equiv
                                        norm
                                        union
	                                      tl))

let add_nk_mapping (nk:netkat) (bdd:MLBDD.t) (mapping:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
  add_mapping nk bdd nk_equivalent canoicalize_nk (fun (a,b) ->Union (a,b)) mapping
  
let add_r_mapping (rel:rel) (bdd:MLBDD.t) (mapping:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
  add_mapping rel bdd r_equivalent canoicalize_r (fun (a,b) ->OrR (a,b)) mapping
  
  (* We assume the invariant here is the arguments are canoicalized *)      
let rec union_mapping (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(union:'a *'a -> 'a)(mapping1:('a*MLBDD.t)list) (mapping2:('a*MLBDD.t)list):('a*MLBDD.t)list=
   match mapping1 with
   | [] -> mapping2
   | (con,bdd)::tl -> add_mapping con bdd equiv norm union (union_mapping equiv norm union tl mapping2)

let union_nk_mapping (mapping1:(netkat*MLBDD.t)list) (mapping2:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
  union_mapping nk_equivalent canoicalize_nk (fun (a,b) ->Union (a,b)) mapping1 mapping2

let union_r_mapping (mapping1:(rel*MLBDD.t)list) (mapping2:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
  union_mapping r_equivalent canoicalize_r (fun (a,b) ->OrR (a,b)) mapping1 mapping2
  
let canonicalize (equiv:'a -> 'a -> bool)(norm:'a -> 'a )(union:'a *'a -> 'a)(mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
   union_mapping equiv norm union mapping []

let canonicalize_nk_mapping (mapping:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
   canonicalize nk_equivalent canoicalize_nk (fun (a,b) ->Union (a,b)) mapping

let canonicalize_r_mapping (mapping:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
   canonicalize r_equivalent canoicalize_r (fun (a,b) ->OrR (a,b)) mapping
   
let apply_mapping (bdd:MLBDD.t)(equiv:'a -> 'a -> bool)(norm:'a -> 'a ) (union:'a *'a -> 'a) (mapping:('a*MLBDD.t)list):('a*MLBDD.t)list=
  (canonicalize equiv norm union (List.map (fun (a,b)-> (a,MLBDD.dand b bdd)) mapping))

let apply_nk_mapping (bdd:MLBDD.t) (mapping:(netkat*MLBDD.t)list):(netkat*MLBDD.t)list=
  apply_mapping bdd nk_equivalent canoicalize_nk (fun (a,b) ->Union (a,b)) mapping

let apply_r_mapping (bdd:MLBDD.t) (mapping:(rel*MLBDD.t)list):(rel*MLBDD.t)list=
  apply_mapping bdd r_equivalent canoicalize_r  (fun (a,b) ->OrR (a,b)) mapping

let concatenate_mapping (mapping:('a*MLBDD.t)list) (seq:'a*'a->'a)(con:'a):('a*MLBDD.t)list=
  (List.map (fun (a,b)-> (seq (a,con),b)) mapping)

let concatenate_nk_mapping (mapping:(netkat*MLBDD.t)list) (nk:netkat):(netkat*MLBDD.t)list=
  concatenate_mapping mapping (fun (a,b)->Seq (a,b)) nk

let concatenate_r_mapping (mapping:(rel*MLBDD.t)list) (rel:rel):(rel*MLBDD.t)list=
  concatenate_mapping mapping (fun (a,b)->SeqR (a,b)) rel

(* We assume the invariant here is the return value is canoicalized *)
let rec delta_k (man:MLBDD.man)(pk1:pk)(pk2:pk)(nk:netkat): (netkat*MLBDD.t)list=
    match nk with
    	| Pred _ -> []  
    	| Asgn _ -> []
  	  | Union(nk1,nk2) -> union_nk_mapping  (delta_k man pk1 pk2 nk1) (delta_k man pk1 pk2 nk2)
  	  | Seq(nk1,nk2) -> union_nk_mapping (concatenate_nk_mapping (delta_k man pk1 pk2 nk1) nk2)
  	                      (apply_nk_mapping (epsilon_k man pk1 pk2 nk1) (delta_k man pk1 pk2 nk2))
  	  | Star nk -> concatenate_nk_mapping (apply_nk_mapping (epsilon_k man pk1 pk2 (Star nk)) (delta_k man pk1 pk2 nk)) (Star nk) 
      | Dup -> [(Pred True,produce_id man pk1 pk2)]
(* For epsilon kr, there is no transition on the y or the input tape, thus we only need two tape denoting the before
and after hidden state *)
let rec empty_r (rel:rel):bool =
  match rel with
    | StarR rel -> true
    | OrR (r1,r2) -> empty_r r1||empty_r r2 
    | SeqR (r1,r2) -> empty_r r1&&empty_r r2
    | _ -> false

let rec epsilon_r (man:MLBDD.man) (pk1:pk) (pk2:pk) (rel:rel):MLBDD.t =
  match rel with
  | Left pred -> compile_pred_bdd man pk1 pred
  | Right pred -> compile_pred_bdd man pk2 pred
  | Binary pkr -> compile_pkr_bdd man pk1 pk2 pkr
  | OrR (r1,r2) -> MLBDD.dor (epsilon_r man pk1 pk2 r1) (epsilon_r man pk1 pk2 r2)
  | SeqR (r1,r2) -> if empty_r r1 then
                      (epsilon_r man pk1 pk2 r1)
                    else
                      MLBDD.dfalse man
  | StarR r -> epsilon_r man pk1 pk2 r

let rec delta_r (man:MLBDD.man) (pk1:pk) (pk2:pk) (rel:rel):(rel*MLBDD.t)list=
  match rel with
  | OrR (r1,r2) -> union_r_mapping (delta_r man pk1 pk2 r1) (delta_r man pk1 pk2 r2)
  | SeqR (r1,r2) -> if empty_r r1 then
                      union_r_mapping (delta_r man pk1 pk2 r2) (add_r_mapping r2 (epsilon_r man pk1 pk2 r1) (delta_r man pk1 pk2 r1))
                    else
                      (add_r_mapping r2 (epsilon_r man pk1 pk2 r1) (delta_r man pk1 pk2 r1))
  | StarR r -> delta_r man pk1 pk2 r
  | _ -> []

let rec epsilon_l_kr (man:MLBDD.man) (pk1:pk) (pk2:pk) (nk:netkat)(rel:rel): (netkat*rel*MLBDD.t)list=
  (* Calculate the one step rel bdd on left *)
  let rec epsilon_l_kr_aux(pk1:pk)(pk2:pk)(rel:rel):MLBDD.t =
    match rel with
    | Left pred -> (compile_pred_bdd man pk2 pred) 
    | OrR (r1,r2) -> MLBDD.dor (epsilon_l_kr_aux pk1 pk2 r1) (epsilon_l_kr_aux pk1 pk2 r2)
    | SeqR (r1,r2) -> if empty_r r1 then
                        epsilon_l_kr_aux pk1 pk2 r2
                      else
                        MLBDD.dfalse man   
    | StarR r -> epsilon_l_kr_aux pk1 pk2 r
    | _ -> MLBDD.dfalse man
  in  
  match rel with
    | Left pred -> MLBDD.dand (compile_pred_bdd man pk1 pred) (epsilon_k man pk1 pk2 nk)
    | OrR (r1,r2) -> MLBDD.dor (epsilon_l_kr man pk1 pk2 nk r1) (epsilon_l_kr man pk1 pk2 nk r2)
    | SeqR (r1,r2) -> let pk3 = generate_unused_pk pk1 pk2 in
                          List.fold_left (fun acc -> fun (nk,bdd) -> MLBDD.dor acc (MLBDD.exists (generate_support pk3)
                              (MLBDD.dand (MLBDD.dand (epsilon_l_kr_aux pk1 pk3 r1) bdd)(epsilon_l_kr man pk3 pk2 nk r2))))
                             (MLBDD.dfalse man) (delta_k man pk1 pk3 nk)
    | StarR r -> epsilon_r man pk1 pk2 r
    | _ -> MLBDD.dfalse man  

let rec epsilon_l_kr (man:MLBDD.man) (pk1:pk) (pk2:pk) (nk:netkat)(rel:rel): MLBDD.t=
  (* Calculate the one step rel bdd on left *)
  let rec epsilon_l_kr_aux(pk1:pk)(pk2:pk)(rel:rel):MLBDD.t =
    match rel with
    | Left pred -> (compile_pred_bdd man pk2 pred) 
    | OrR (r1,r2) -> MLBDD.dor (epsilon_l_kr_aux pk1 pk2 r1) (epsilon_l_kr_aux pk1 pk2 r2)
    | SeqR (r1,r2) -> if empty_r r1 then
                        epsilon_l_kr_aux pk1 pk2 r2
                      else
                        MLBDD.dfalse man   
    | StarR r -> epsilon_l_kr_aux pk1 pk2 r
    | _ -> MLBDD.dfalse man
  in  
  match rel with
    | Left pred -> MLBDD.dand (compile_pred_bdd man pk1 pred) (epsilon_k man pk1 pk2 nk)
    | OrR (r1,r2) -> MLBDD.dor (epsilon_l_kr man pk1 pk2 nk r1) (epsilon_l_kr man pk1 pk2 nk r2)
    | SeqR (r1,r2) -> let pk3 = generate_unused_pk pk1 pk2 in
                          List.fold_left (fun acc -> fun (nk,bdd) -> MLBDD.dor acc (MLBDD.exists (generate_support pk3)
                              (MLBDD.dand (MLBDD.dand (epsilon_l_kr_aux pk1 pk3 r1) bdd)(epsilon_l_kr man pk3 pk2 nk r2))))
                             (MLBDD.dfalse man) (delta_k man pk1 pk3 nk)
    | StarR r -> epsilon_r man pk1 pk2 r
    | _ -> MLBDD.dfalse man  

  
      
    
    
    
    
    
    

