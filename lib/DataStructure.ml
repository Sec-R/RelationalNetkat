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

module rec NK : sig
    type t = 
    | Pred of pred
    | Asgn of field * bool
    | Union of SNK.t
    | Seq of t * t
    | Star of t
    | Dup
    val compare: t -> t -> int
  end
= struct
   type t = 
    | Pred of pred
    | Asgn of field * bool
    | Union of SNK.t
    | Seq of t * t
    | Star of t
    | Dup
  let rec compare t1 t2 =
      match (t1, t2) with
      | (Pred p1, Pred p2) -> Stdlib.compare p1 p2
      | (Pred _, _) -> 1
      | (_, Pred _) -> -1
      | (Asgn (f1, b1),Asgn (f2, b2)) -> Stdlib.compare (f1,b1) (f2,b2)
      | (Asgn _, _) -> 1
      | (_, Asgn _) -> -1
      | (Union sk1, Union sk2) -> SNK.compare sk1 sk2
      | (Union _, _) -> 1
      | (_, Union _) -> -1
      | (Seq (t1, t2), Seq (t3, t4)) -> let c = compare t1 t3 in if c = 0 then compare t2 t4 else c
      | (Seq _, _) -> 1
      | (_, Seq _) -> -1
      | (Star t1, Star t2) -> compare t1 t2
      | (Star _, _) -> 1
      | (_, Star _) -> -1
      | (Dup, Dup) -> 0
  end
and SNK : Set.S with type elt = NK.t
= Set.Make(NK)



module rec Rel : sig
  type t = 
  | Left of pred
  | Right of pred
  | Binary of pkr
  | OrR of SR.t
  | SeqR of t * t
  | StarR of t
  val compare: t -> t -> int
end
= struct
 type t = 
 | Left of pred
 | Right of pred
 | Binary of pkr
 | OrR of SR.t
 | SeqR of t * t
 | StarR of t
let rec compare t1 t2 =
    match (t1, t2) with
    | (Left p1, Left p2) -> Stdlib.compare p1 p2
    | (Left _, _) -> 1
    | (_, Left _) -> -1
    | (Right p1, Right p2) -> Stdlib.compare p1 p2
    | (Right _, _) -> 1
    | (_, Right _) -> -1
    | (Binary p1, Binary p2) -> Stdlib.compare p1 p2
    | (Binary _, _) -> 1
    | (_, Binary _) -> -1
    | (OrR sr1, OrR sr2) -> SR.compare sr1 sr2
    | (OrR _, _) -> 1
    | (_, OrR _) -> -1
    | (SeqR (r1, r2), SeqR (r3, r4)) -> let c = compare r1 r3 in if c = 0 then compare r2 r4 else c
    | (SeqR _, _) -> 1
    | (_, SeqR _) -> -1
    | (StarR r1, StarR r2) -> compare r1 r2
end
and SR : Set.S with type elt = Rel.t
= Set.Make(Rel)

module NKOMap = Map.Make(
  struct type t = NK.t option 
  let compare = compare end)

module NKROMap = Map.Make(
  struct type t = (NK.t option*Rel.t option) 
  let compare = compare
end)

module BMap = Map.Make(
  struct type t = MLBDD.t 
  let compare a b = compare (MLBDD.id a) (MLBDD.id b) 
end)

module NKROBMap = Map.Make(
  struct type t = (NK.t option*Rel.t option)*MLBDD.t 
  let compare a b = let c = compare (fst a) (fst b) in if c = 0 then compare (MLBDD.id (snd a)) (MLBDD.id (snd b)) else c
end)

module NKROBSet = Set.Make(
  struct type t = (NK.t option*Rel.t option)*MLBDD.t 
  let compare a b = let c = compare (fst a) (fst b) in if c = 0 then compare (MLBDD.id (snd a)) (MLBDD.id (snd b)) else c
end)

module NKROBSMap = Map.Make(
  struct type t = NKROBSet.t 
  let compare  = NKROBSet.compare
end)

module NKROBSSMap = Map.Make(
  struct type t = NKROBSet.t*NKROBSet.t 
  let compare a b = let c = NKROBSet.compare (fst a) (fst b) in if c = 0 then NKROBSet.compare (snd a) (snd b) else c 
end)

type man = {
  field_max: field;
  bman:MLBDD.man;
}


(* The variable is in order of x x' y y' --> 4k, 4k+1, 4k+2, 4k+3*)
let bddvar (man:man) (pk:pk) (field:field) = if field mod 4 = 0 then field*2
                      else if field mod 4 = 1 then field*2 + 1
                      else if field mod 4 = 2 then man.field_max*2 + field
                      else man.field_max*3 + field

let generate_single_var (man:man) (pk:pk) (field:field):MLBDD.t =
    MLBDD.ithvar (man.bman) (bddvar man pk field)

let bdd_true (man:man):MLBDD.t = MLBDD.dtrue man.bman    

let bdd_false (man:man):MLBDD.t = MLBDD.dtrue man.bman    

let compile_pred_bdd (man:man)(pk:pk) (predicate:pred):MLBDD.t = 
     let rec compile_pred_bdd_aux (predicate:pred):MLBDD.t =
	match predicate with
    	| True -> bdd_true man
    	| False -> bdd_false man
  		| Test (field,false) -> MLBDD.dnot (generate_single_var man pk field)
  		| Test (field,true) -> generate_single_var man pk field
  		| And (pred1,pred2) -> MLBDD.dand (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| Or (pred1,pred2) -> MLBDD.dor (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| Neg predicate -> MLBDD.dnot (compile_pred_bdd_aux predicate)
  	in compile_pred_bdd_aux predicate

let produce_id (man:man) (pk1:pk) (pk2:pk):MLBDD.t =
     let rec produce_id_aux (cur:field):MLBDD.t =
         if cur > man.field_max then 
          bdd_true man
         else  
          MLBDD.dand (MLBDD.nxor (generate_single_var man pk1 cur) ((generate_single_var man pk2 cur))) (produce_id_aux (cur+1))
     in produce_id_aux 0

let produce_assign (man:man) (pk1:pk) (pk2:pk) (bvar:int)(asgn:bool) (left:bool):MLBDD.t =
     let rec produce_assign_aux (cur:field):MLBDD.t =
         if cur > man.field_max then 
           bdd_true man
         else if left && (bvar = (bddvar man pk1 cur)) then 
                   MLBDD.dand (if asgn then 
                                  (generate_single_var man pk1 cur)
                               else 
                                  MLBDD.dnot (generate_single_var man pk1 cur))
                              (produce_assign_aux (cur+1))         
         else if (not left) && (bvar = (bddvar man pk2 cur)) then
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

let generate_support (man:man) (pk:pk):MLBDD.support =
  let rec generate_list (cur:field):int list =
     if cur > man.field_max then []
     else (bddvar man pk cur)::(generate_list (cur+1))
  in MLBDD.support_of_list (generate_list 0)

  
let comp_bdd (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> 'a -> MLBDD.t) (con1: 'a) (con2: 'a):MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    MLBDD.exists (generate_support man pk3) (MLBDD.dand (compiler man pk1 pk3 con1) (compiler man pk3 pk2 con2))
      
let rec compile_pkr_bdd (man:man)(pk1:pk) (pk2:pk) (pkr:pkr):MLBDD.t = 
     let rec compile_pkr_bdd_aux (pkr:pkr):MLBDD.t =
	match pkr with
	  | Id -> produce_id man pk1 pk2
	  | Empty -> bdd_false man
	  | LeftTest (field, false) -> MLBDD.dnot (generate_single_var man pk1 field)
	  | LeftTest (field, true) -> generate_single_var man pk1 field
	  | RightTest (field, false) -> MLBDD.dnot (generate_single_var man pk2 field)
	  | RightTest (field, true) -> generate_single_var man pk2 field
	  | LeftAsgn (field, b) -> produce_assign man pk1 pk2 (bddvar man pk1 field) b true  
	  | RightAsgn (field, b) -> produce_assign man pk1 pk2 (bddvar man pk2 field) b false  
	  | Eqf field -> MLBDD.nxor (generate_single_var man pk1 field) (generate_single_var man pk2 field)
	  | Comp (pkr1, pkr2) -> comp_bdd man pk1 pk2 compile_pkr_bdd pkr1 pkr2
    | Or (pkr1,pkr2)-> MLBDD.dor (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
  	| And (pkr1,pkr2)-> MLBDD.dand (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
  	| Neg pkr -> MLBDD.dnot (compile_pkr_bdd_aux pkr)
  	in compile_pkr_bdd_aux pkr

(* A naive implementation, to be optimized*)    
let closure_bdd (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> 'a -> MLBDD.t) (con:'a) :MLBDD.t =
  (* input cur is of pk1 and pk2 *)
  let pk3 = generate_unused_pk pk1 pk2 in
    let support2 = generate_support man pk2 in
      let support3 = generate_support man pk3 in
        let id23 = (produce_id man pk2 pk3) in
          let rec closure_bdd_aux  (cur:MLBDD.t):MLBDD.t =
             let next = (MLBDD.dor cur (MLBDD.exists support3 (MLBDD.dand (MLBDD.exists support2 (MLBDD.dand cur (compiler man pk2 pk3 con))) id23))) in
              if MLBDD.equal cur next then
	                  cur
  	              else 
                    closure_bdd_aux next
          in closure_bdd_aux (produce_id man pk1 pk2)  	 

let add_nko_mapping (con:NK.t option) (bdd:MLBDD.t) (mapping:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
    if MLBDD.is_false bdd then
	        mapping
	  else
      NKOMap.update con (function
        | None -> Some bdd
        | Some bdd' -> Some (MLBDD.dor bdd bdd')) mapping


let add_nkro_mapping (con:NK.t option*Rel.t option) (bdd:MLBDD.t) (mapping:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
    if MLBDD.is_false bdd then
	        mapping
	  else
      NKROMap.update con (function
        | None -> Some bdd
        | Some bdd' -> Some (MLBDD.dor bdd bdd')) mapping

let add_nkro_mapping_updated (con:NK.t option*Rel.t option) (bdd:MLBDD.t) (mapping:(MLBDD.t)NKROMap.t):((MLBDD.t)NKROMap.t*bool)=
    if MLBDD.is_false bdd then
	        (mapping,false)
	  else
      match NKROMap.find_opt con mapping with
        | None -> (NKROMap.add con bdd mapping,true)
        | Some bdd' -> if MLBDD.equal (MLBDD.dor bdd bdd') bdd' then
                          (mapping,false)
                       else (NKROMap.add con (MLBDD.dor bdd bdd') mapping,true)
      
let union_nko_mapping (mapping1:(MLBDD.t)NKOMap.t) (mapping2:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
   NKOMap.fold add_nko_mapping mapping1 mapping2

let union_nkro_mapping (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
   NKROMap.fold add_nkro_mapping mapping1 mapping2

let union_nkro_mapping_updated (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):((MLBDD.t)NKROMap.t*bool)=
   NKROMap.fold (fun con bdd (mapping,changed) -> 
            match add_nkro_mapping_updated con bdd mapping with
              | (mapping',true) -> (mapping',true)
              | (mapping',false) -> (mapping',changed)
            ) mapping1 (mapping2,false)

let apply_nko_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
  NKOMap.filter_map (fun a bdd-> let nbdd = tobdd bdd in 
                                    if (MLBDD.is_false nbdd) then
                                       None
                                    else Some nbdd) mapping

let apply_nkro_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
  NKROMap.filter_map (fun a bdd-> let nbdd = tobdd bdd in 
                                    if (MLBDD.is_false nbdd) then
                                       None
                                    else Some nbdd) mapping

                                    
let concatenate_nko_mapping (mapping:(MLBDD.t)NKOMap.t) (nko2:NK.t option):(MLBDD.t)NKOMap.t=
  NKOMap.fold (fun nko1 bdd acc -> NKOMap.add (match (nko1,nko2) with
                                                    | (None,_) -> nko2
                                                    | (_, None) -> nko1
                                                    | (Some nk1,Some nk2) -> Some (Seq (nk1,nk2))
                                                   ) bdd acc) mapping NKOMap.empty

let concatenate_nkro_mapping (mapping:(MLBDD.t)NKROMap.t) (nkro2:NK.t option*Rel.t option):(MLBDD.t)NKROMap.t=
  NKROMap.fold (fun nkro1 bdd acc -> NKROMap.add ((match (fst nkro1,fst nkro2) with
                                                              | (None,nko2) -> nko2
                                                              | (nko1, None) -> nko1
                                                              | (Some nk1,Some nk2) -> Some (Seq (nk1,nk2))),
                                                              (match (snd nkro1,snd nkro2) with
                                                              | (None,ro2) -> ro2
                                                              | (ro1, None) -> ro1
                                                              | (Some r1,Some r2) -> Some (SeqR (r1,r2))                                                             
                                                              )) bdd acc) mapping NKROMap.empty

let folding_epsilon (man:man) (nkom:(MLBDD.t)NKOMap.t):MLBDD.t =
  NKOMap.fold 
  (fun nko bdd acc -> match nko with 
                            | None -> MLBDD.dor acc bdd
                            | _ -> acc) 
                            nkom (bdd_false man)                                                        
(* We assume the invariant here is the return value is canoicalized *) 
let rec delta_k (man:man)(pk1:pk)(pk2:pk)(nko:NK.t option): (MLBDD.t)NKOMap.t=
    match nko with
      | None -> NKOMap.empty
    	| Some (Pred pred) -> NKOMap.singleton None (MLBDD.dand (compile_pred_bdd man pk1 pred) (produce_id man pk1 pk2))  
    	| Some (Asgn (field, b)) -> NKOMap.singleton None (produce_assign man pk1 pk2 (bddvar man pk1 field) b true)
  	  | Some (Union nks) -> SNK.fold (fun nk acc -> union_nko_mapping (delta_k man pk1 pk2 (Some nk)) acc) nks NKOMap.empty
  	  | Some (Seq(nk1,nk2)) -> let pk3 =  generate_unused_pk pk1 pk2 in
                                  let support = generate_support man pk3 in
                                    union_nko_mapping (concatenate_nko_mapping (delta_k man pk1 pk2 (Some nk1)) (Some nk2))
  	                                (let epsilon = folding_epsilon man (delta_k man pk1 pk3 (Some nk1)) in
                                      (apply_nko_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) (delta_k man pk3 pk2 (Some nk2))))
  	  | Some (Star nk) -> concatenate_nko_mapping (let pk3 = generate_unused_pk pk1 pk2 in
                      	                      let support = generate_support man pk3 in
                                                let epsilon = closure_bdd man pk1 pk3 (fun man pk1 pk2 nk 
                                                                                            -> folding_epsilon man (delta_k man pk1 pk2 (Some nk))) nk in                         
                                                 (apply_nko_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) (delta_k man pk3 pk2 (Some nk)))) (Some (Star nk)) 
      | Some Dup -> NKOMap.singleton (Some (Pred True)) (produce_id man pk1 pk2)
(* For epsilon kr, there is no transition on the y or the input tape, thus we only need two tape denoting the before
and after hidden state *)

let comp_nkro_list (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> (NK.t option*Rel.t option)
       -> (MLBDD.t)NKROMap.t) (nko: NK.t option) (r1: Rel.t) (r2:Rel.t):(MLBDD.t)NKROMap.t =
       union_nkro_mapping (concatenate_nkro_mapping (compiler man pk1 pk2 (nko,Some r1)) (None,(Some r2)))
                          (let pk3 = generate_unused_pk pk1 pk2 in
                            let support = generate_support man pk3 in
                              NKROMap.fold (fun (nko,ro) bdd acc -> 
                                                               match ro with
                                                              | None -> union_nkro_mapping (apply_nkro_mapping (fun nbdd -> MLBDD.exists support (MLBDD.dand bdd nbdd)) (compiler man pk3 pk2 (nko,Some r2))) acc
                                                              | Some _ -> acc
                              ) (compiler man pk1 pk3 (nko,Some r1)) NKROMap.empty) 
          
let closure_nkro_list (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> (NK.t option*Rel.t option)
       -> (MLBDD.t)NKROMap.t) (nko: NK.t option) (r: Rel.t):(MLBDD.t)NKROMap.t =
       let pk3 = generate_unused_pk pk1 pk2 in
         let support2 = generate_support man pk2 in
           let support3 = generate_support man pk3 in
             let id23 = (produce_id man pk2 pk3) in
                let rec closure_nkro_list_aux (cur:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t =
                  match union_nkro_mapping_updated (NKROMap.fold (fun (nko,ro) bdd acc
                                        -> match ro with
                                              | None -> union_nkro_mapping (apply_nkro_mapping (fun nbdd 
                                                  -> (MLBDD.exists support3 (MLBDD.dand id23 
                                                          (MLBDD.exists support2 (MLBDD.dand bdd nbdd))))) (compiler man pk2 pk3 (nko,Some r))) acc
                                              | Some _ -> acc) cur NKROMap.empty) cur with
                    | (next,false) -> next
                    | (next,true) -> closure_nkro_list_aux next
                in closure_nkro_list_aux (NKROMap.singleton (nko,Some r) (produce_id man pk1 pk2))                        
                                             
let rec epsilon_kr (man:man) (pk1:pk) (pk2:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t =
  add_nkro_mapping nkro (produce_id man pk1 pk2)
  (match nkro with
    | (nko,None) -> NKROMap.empty
    | (nko,Some (Left pred)) -> let pred_bdd = compile_pred_bdd man pk1 pred in
                                  NKOMap.fold (fun nko bdd acc -> NKROMap.add (nko,None) bdd acc) (apply_nko_mapping (fun bdd -> MLBDD.dand bdd pred_bdd) (delta_k man pk1 pk2 nko)) NKROMap.empty
    | (nko,Some (Right pred)) -> NKROMap.empty
    | (nko,Some (Binary pkr)) -> NKROMap.empty
    | (nko,Some (OrR rs)) -> SR.fold (fun r acc -> union_nkro_mapping (epsilon_kr man pk1 pk2 (nko,Some r)) acc) rs NKROMap.empty
    | (nko,Some (SeqR (r1,r2))) -> comp_nkro_list man pk1 pk2 epsilon_kr nko r1 r2
    | (nko,Some (StarR r)) -> closure_nkro_list man pk1 pk2 epsilon_kr nko r)                                       

let generate_unused_tri_pk (pk1:pk) (pk2:pk) (pk3:pk):pk =
  6 - pk1 - pk2 - pk3  

let delta_kr (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t=
   let rec delta_kr_aux (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t=
      let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
        let support = generate_support man pk4 in
          (NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (fun ebdd -> (MLBDD.exists support (MLBDD.dand bdd ebdd))) (epsilon_kr man pk4 pk2 nkro)) acc)
      (match nkro with
        | (nko,None) -> NKROMap.empty
        | (nko,Some (Left pred)) -> NKROMap.empty
        | (nko,Some (Right pred)) -> let pred_bdd = compile_pred_bdd man pk3 pred in
                                        NKROMap.singleton (nko,None) pred_bdd
        | (nko,Some (Binary pkr)) -> let pkr_bdd = compile_pkr_bdd man pk4 pk3 pkr in
                                        NKOMap.fold (fun nko bdd acc -> NKROMap.add (nko,None) bdd acc) (apply_nko_mapping (fun bdd -> MLBDD.dand bdd pkr_bdd) (delta_k man pk1 pk4 nko)) NKROMap.empty
        | (nko,Some (OrR rs)) -> SR.fold (fun r acc -> union_nkro_mapping (delta_kr_aux man pk1 pk4 pk3 (nko,Some r)) acc) rs NKROMap.empty                                
        | (nko,Some (SeqR (r1,r2))) -> (concatenate_nkro_mapping (delta_kr_aux man pk1 pk4 pk3 (nko,Some r1)) (None,(Some r2)))
        | (nko,Some (StarR r)) -> (concatenate_nkro_mapping (delta_kr_aux man pk1 pk4 pk3 (nko,Some r)) (None,(Some (StarR r))))) NKROMap.empty)
    in       
      let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
        let support = generate_support man pk4 in
        (NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (fun ebdd -> (MLBDD.exists support (MLBDD.dand bdd ebdd))) 
            (delta_kr_aux man pk4 pk2 pk3 nkro)) acc) (epsilon_kr man pk1 pk4 nkro) NKROMap.empty)
            
let calculate_reachable_set (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (nkr:NK.t*Rel.t):(MLBDD.t)NKROMap.t =
  let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
    let support2 = generate_support man pk2 in
    let support3 = generate_support man pk3 in
    let support1 = generate_support man pk1 in
    let id12 = produce_id man pk1 pk2 in
    let id34 = produce_id man pk3 pk4 in
    let worklist = Queue.create() in
      let rec calculate_reachable_set_aux (cur:(MLBDD.t)NKROMap.t): (MLBDD.t)NKROMap.t=
        match Queue.take_opt worklist with
          | None -> cur
          | Some (nkro,bdd) -> 
            calculate_reachable_set_aux (NKROMap.fold (fun nkro bdd acc-> match (add_nkro_mapping_updated nkro bdd cur) with
                                                | (cur,true) -> Queue.add (nkro,bdd) worklist; cur
                                                | (cur,false) -> cur) 
                                                (apply_nkro_mapping 
                  (fun nbdd -> (MLBDD.exists support2 (MLBDD.exists support3 (MLBDD.dand id34 (MLBDD.dand id12 (MLBDD.exists support1 (MLBDD.dand nbdd bdd)))))))
                    (delta_kr man pk1 pk2 pk3 nkro)) cur)
     in Queue.add ((Some (fst nkr),Some (snd nkr)),(produce_id man pk1 pk4)) worklist;
       calculate_reachable_set_aux NKROMap.empty 
    

let generate_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (nkr:NK.t*Rel.t):(MLBDD.t*(MLBDD.t)NKROMap.t)NKROMap.t=
  let support2 = generate_support man pk2 in
  let support3 = generate_support man pk3 in
  let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
  let support4 = generate_support man pk4 in  
    NKROMap.mapi (fun nkro bdd -> let new_delta = apply_nkro_mapping (fun tbdd -> MLBDD.dand tbdd bdd) (delta_kr man pk1 pk2 pk3 nkro)
                                  in let hidden_state = MLBDD.exists support2 (MLBDD.exists support3
                                     (MLBDD.exists support4 (NKROMap.fold (fun nkro bdd acc -> MLBDD.dor acc bdd) new_delta (bdd_false man)))) in
                                      (hidden_state,new_delta)) (calculate_reachable_set man pk1 pk2 pk3 nkr)
      
                                    
let spliting_bdd (man:man) (bdd:MLBDD.t): MLBDD.t list =
  MLBDD.foldb (fun btree -> match btree with
                            | MLBDD.BFalse -> []
                            | MLBDD.BTrue -> [bdd_true man]
                            | MLBDD.BIf (low,var,high) -> List.append (List.map (fun bdd -> MLBDD.dand (MLBDD.ithvar man.bman var) bdd) high) (List.map (fun bdd -> MLBDD.dand (MLBDD.dnot (MLBDD.ithvar man.bman var)) bdd) low)
                            ) bdd

let find_bdd (nkro:NK.t option*Rel.t option)(transition:(MLBDD.t*(MLBDD.t)NKROMap.t)NKROMap.t):MLBDD.t =
  match NKROMap.find_opt nkro transition with
    | None -> failwith "Transition not found"
    | Some (bdd,_) -> bdd                           

let simplify_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (nkr:NK.t*Rel.t):((MLBDD.t)NKROBMap.t)NKROBMap.t=
  let id12 = produce_id man pk1 pk2 in
  let support1 = generate_support man pk1 in
  let pk4 = generate_unused_tri_pk pk1 pk2 pk3 in
  let support2 = generate_support man pk2 in
  let support4 = generate_support man pk4 in  
  let all_transition = generate_all_transition man pk1 pk2 pk3 nkr in
    NKROMap.fold (fun nkro1 (hbdd1,nkrom) acc -> let hbddl1 = spliting_bdd man hbdd1 in
                                        List.fold_right (fun hbdd1 acc -> 
                                          NKROMap.fold (fun nkro2 tbdd acc -> 
                                            let hbddl2 = spliting_bdd man (find_bdd nkro2 all_transition)
                                            in List.fold_right (fun hbdd2 acc -> 
                                              let tbddf = MLBDD.dand (MLBDD.dand hbdd1 tbdd) (MLBDD.exists support1 (MLBDD.dand hbdd2 id12)) in
                                              if MLBDD.is_false tbddf then
                                                acc
                                              else
                                                NKROBMap.add (nkro1,hbdd1) (NKROBMap.singleton (nkro2,hbdd2) (MLBDD.exists support4 (MLBDD.exists support2 tbddf))) acc)
                                          hbddl2 acc
                                        ) nkrom acc) hbddl1 acc) all_transition NKROBMap.empty

let is_final_state (nkro:NK.t option*Rel.t option):bool =
  match nkro with
    | (None,None) -> true
    | _ -> false                         

let is_final_state_S (nkrobs:NKROBSet.t):bool =
  NKROBSet.exists (fun (nkro,bdd) -> is_final_state nkro) nkrobs

let determinize_transition (nexts:(MLBDD.t)NKROBMap.t):(MLBDD.t)NKROBSMap.t=
    let add_transition (nkrob:(NK.t option*Rel.t option)*MLBDD.t) (bdd:MLBDD.t) (acc:(MLBDD.t)NKROBSMap.t):(MLBDD.t)NKROBSMap.t=
        if MLBDD.is_false bdd then
          acc
        else
          let new_bdd = NKROBSMap.fold (fun nkrobs bddh acc -> MLBDD.dand (MLBDD.dnot bddh) acc) acc bdd in
          let next_map =
          NKROBSMap.fold (fun nkrobs bddh acc -> 
            let ibdd = MLBDD.dand bdd bddh in
            let dbdd = MLBDD.dand (MLBDD.dnot bdd) bddh in
            let temp = if MLBDD.is_false ibdd then
                         acc
                       else 
                         NKROBSMap.add (NKROBSet.add nkrob nkrobs) bddh acc in
              if MLBDD.is_false dbdd then
                         temp
              else NKROBSMap.add nkrobs bddh temp) acc NKROBSMap.empty in
          if MLBDD.is_false new_bdd then
            next_map
          else
            NKROBSMap.add (NKROBSet.singleton nkrob) new_bdd next_map
    in NKROBMap.fold (fun nkrob bdd acc -> add_transition nkrob bdd acc) nexts NKROBSMap.empty
   
let determinization (start:NKROBSet.t) (transition:((MLBDD.t)NKROBMap.t)NKROBMap.t):((MLBDD.t)NKROBSMap.t)NKROBSMap.t=
   let worklist = Queue.create() in
   let rec determinization_aux (acc:((MLBDD.t)NKROBSMap.t)NKROBSMap.t):((MLBDD.t)NKROBSMap.t)NKROBSMap.t=
      match Queue.take_opt worklist with
        | None -> acc
        | Some nkrobs -> 
                    if NKROBSMap.mem nkrobs acc then
                      acc
                    else
                      let nexts = NKROBSet.fold (fun nkrob acc -> NKROBMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) (NKROBMap.find nkrob transition) acc)
                                                     nkrobs NKROBMap.empty in
                    let dnexts = determinize_transition nexts in
                    NKROBSMap.iter (fun nkrobs _ -> Queue.add nkrobs worklist) dnexts;
                    determinization_aux (NKROBSMap.add nkrobs dnexts acc)
    in Queue.add start worklist;
       determinization_aux NKROBSMap.empty      

let bisim (man:man)(pk1:pk)(pk2:pk)(start1:NKROBSet.t)(start2:NKROBSet.t)(aut1:((MLBDD.t)NKROBSMap.t)NKROBSMap.t) (aut2:((MLBDD.t)NKROBSMap.t)NKROBSMap.t):bool =
  let support2 = generate_support man pk2 in
  let id12 = produce_id man pk1 pk2 in
  let worklist = Queue.create() in
  let rec bisim_aux (donelist:(MLBDD.t)NKROBSSMap.t):bool =
    match Queue.take_opt worklist with
      | None -> true
      | Some ((nkros1,nkros2),bdd) -> let (newdonelist,bdd) = match NKROBSSMap.find_opt (nkros1,nkros2) donelist with 
                                  | None -> (NKROBSSMap.add (nkros1,nkros2) bdd donelist,bdd)
                                  | Some dbdd -> (NKROBSSMap.add (nkros1,nkros2) (MLBDD.dor bdd dbdd) donelist,(MLBDD.dand bdd (MLBDD.dnot dbdd))) in
                                if MLBDD.is_false bdd then
                                  bisim_aux newdonelist
                                else
                                  if is_final_state_S nkros1 <> is_final_state_S nkros2 then
                                    false
                                  else
                                    let next1 = NKROBSMap.find nkros1 aut1 in
                                    let next2 = NKROBSMap.find nkros1 aut2 in
                                      NKROBSMap.iter (fun nkros1 bdd1 -> 
                                        NKROBSMap.iter (fun nkros2 bdd2 -> 
                                          Queue.add ((nkros1,nkros2),(MLBDD.exists support2(MLBDD.dand id12 (MLBDD.dand bdd (MLBDD.dand bdd1 bdd2))))) worklist) next2) next1;
                                          (let reachable_bdd = (NKROBSMap.fold (fun nkros2 bdd2 acc -> MLBDD.dor acc bdd2) next2 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros1 bdd1 -> 
                                              Queue.add ((nkros1,NKROBSet.empty),(MLBDD.exists support2(MLBDD.dand id12 (MLBDD.dand bdd (MLBDD.dand bdd1 (MLBDD.dnot reachable_bdd)))))) worklist) next1);
                                          (let reachable_bdd = (NKROBSMap.fold (fun nkros1 bdd1 acc -> MLBDD.dor acc bdd1) next1 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros2 bdd2 -> 
                                              Queue.add ((NKROBSet.empty,nkros2),(MLBDD.exists support2(MLBDD.dand id12 (MLBDD.dand bdd (MLBDD.dand (MLBDD.dnot reachable_bdd) bdd2))))) worklist) next2);    
                                          bisim_aux newdonelist
  in Queue.add ((start1,start2),bdd_true man) worklist;
     bisim_aux NKROBSSMap.empty 
  