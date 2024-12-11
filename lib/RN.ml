(*
  This module defines various data structures and functions for working with 
  Relational NetKAT using Binary Decision Diagrams (BDDs). 

  The main components include:
  - Types for representing fields, predicates, and packet relations.
  - Modules for representing NetKAT expressions (NK) and sets of NetKAT expressions (SNK).
  - Modules for representing relational expressions (Rel) and sets of relational expressions (SR).
  - Functions for compiling predicates and packet relations into BDDs.
  - Functions for manipulating BDDs, including generating support sets, renaming variables, and computing closures.
  - Functions for constructing and manipulating mappings between NetKAT expressions and BDDs.
  - Functions for computing reachable sets and transitions in a NetKAT automaton.
  - Functions for determinizing and bisimulating NetKAT automata.

  The main types and functions are:

  - type field: Represents a field in a packet.
  - type pk: Represents a packet.
  - type pred: Represents a predicate in NetKAT.
  - type pkr: Represents a packet relation in NetKAT.
  - module NK: Represents NetKAT expressions.
  - module SNK: Represents sets of NetKAT expressions.
  - module Rel: Represents relational expressions.
  - module SR: Represents sets of relational expressions.
  - module NKOMap: Represents a mapping from optional NetKAT expressions to BDDs.
  - module BMap: Represents a mapping from BDDs to other values.
  - module NKROMap: Represents a mapping from pairs of optional NetKAT and relational expressions to BDDs.
  - module NKROBMap: Represents a mapping from pairs of optional NetKAT and relational expressions and BDDs to other values.
  - module BSet: Represents a set of BDDs.
  - module NKROBSet: Represents a set of pairs of optional NetKAT and relational expressions and BDDs.
  - module NKROBSMap: Represents a mapping from sets of pairs of optional NetKAT and relational expressions and BDDs to other values.
  - type man: Represents a manager for BDD operations.
  - let bddvar: Computes the BDD variable index for a given field and packet.
  - let generate_single_var: Generates a BDD for a single variable.
  - let bdd_true: Returns the BDD representing true.
  - let bdd_false: Returns the BDD representing false.
  - let compile_pred_bdd: Compiles a predicate into a BDD.
  - let produce_id: Produces a BDD representing the identity relation.
  - let produce_assign: Produces a BDD representing an assignment.
  - let generate_unused_pk: Generates an unused packet index.
  - let generate_support: Generates the support set for a packet.
  - let generate_double_support: Generates the support set for two packets.
  - let comp_bdd: Composes two BDDs.
  - let compile_pkr_bdd: Compiles a packet relation into a BDD.
  - let rename_bdd: Renames the variables in a BDD.
  - let closure_bdd: Computes the closure of a BDD.
  - let add_nko_mapping: Adds a mapping from an optional NetKAT expression to a BDD.
  - let add_nkro_mapping: Adds a mapping from a pair of optional NetKAT and relational expressions to a BDD.
  - let add_nkro_mapping_updated: Adds a mapping from a pair of optional NetKAT and relational expressions to a BDD, with an update flag.
  - let union_nko_mapping: Unions two mappings from optional NetKAT expressions to BDDs.
  - let union_nkro_mapping: Unions two mappings from pairs of optional NetKAT and relational expressions to BDDs.
  - let union_nkro_mapping_updated: Unions two mappings from pairs of optional NetKAT and relational expressions to BDDs, with an update flag.
  - let apply_nko_mapping: Applies a function to the BDDs in a mapping from optional NetKAT expressions to BDDs.
  - let apply_nkro_mapping: Applies a function to the BDDs in a mapping from pairs of optional NetKAT and relational expressions to BDDs.
  - let concatenate_nko_mapping: Concatenates a mapping from optional NetKAT expressions to BDDs with an optional NetKAT expression.
  - let concatenate_nkro_mapping: Concatenates a mapping from pairs of optional NetKAT and relational expressions to BDDs with a pair of optional NetKAT and relational expressions.
  - let folding_epsilon: Computes the epsilon closure of a mapping from optional NetKAT expressions to BDDs.
  - let delta_k: Computes the delta transition for a NetKAT expression.
  - let comp_nkro_map: Composes two mappings from pairs of optional NetKAT and relational expressions to BDDs.
  - let closure_nkro_map: Computes the closure of a mapping from pairs of optional NetKAT and relational expressions to BDDs.
  - let epsilon_kr: Computes the epsilon transition for a pair of optional NetKAT and relational expressions.
  - let generate_unused_pk5: Generates an unused packet index from four packet indices.
  - let delta_kr: Computes the delta transition for a pair of optional NetKAT and relational expressions.
  - let calculate_reachable_set: Computes the reachable set for a NetKAT automaton.
  - let re_ordering: Reorders the variables in a BDD.
  - let back_ordering: Reverts the reordering of variables in a BDD.
  - let var_low_branch: Computes the low branch of a BDD for a given variable.
  - let var_high_branch: Computes the high branch of a BDD for a given variable.
  - let var_if: Computes the if-then-else of two BDDs for a given variable.
  - let splitting_bdd: Splits a BDD into a list of BDDs.
  - let generate_all_transition: Generates all transitions for a NetKAT automaton.
  - let find_bddl: Finds the BDD list for a given pair of optional NetKAT and relational expressions.
  - let simplify_all_transition: Simplifies all transitions for a NetKAT automaton.
  - let is_final_state: Checks if a pair of optional NetKAT and relational expressions is a final state.
  - let is_final_state_S: Checks if a set of pairs of optional NetKAT and relational expressions and BDDs contains a final state.
  - let determinize_transition: Determinizes a transition mapping.
  - let determinization: Determinizes a NetKAT automaton.
  - let bisim: Checks if two NetKAT automata are bisimilar.
*)
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
  | OrP of pred * pred
  | Neg of pred
  
type pkr =
  | Id
  | Empty
  | LeftTest of field * bool 
  | RightTest of field * bool
  | LeftAsgn of field * bool
  | RightAsgn of field * bool
  | Comp of pkr * pkr
  | Or of pkr * pkr

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
  | Left of pkr
  | Right of pkr
  | Binary of pkr
  | OrR of SR.t
  | SeqR of t * t
  | StarR of t
  val compare: t -> t -> int
end
= struct
 type t = 
 | Left of pkr
 | Right of pkr
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

module BMap = Map.Make(
  struct type t = MLBDD.t 
  let compare a b = compare (MLBDD.id a) (MLBDD.id b) 
end)  

module NKROMap = Map.Make(
  struct type t = (NK.t option*Rel.t option) 
  let compare = compare
end)

module NKROBMap = Map.Make(
  struct type t = (NK.t option*Rel.t option)*MLBDD.t 
  let compare a b = let c = compare (fst a) (fst b) in if c = 0 then compare (MLBDD.id (snd a)) (MLBDD.id (snd b)) else c
end)

module BSet = Set.Make(
  struct type t = MLBDD.t 
  let compare a b = compare (MLBDD.id a) (MLBDD.id b)
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
let rec pred_to_string (pred:pred):string= 
  match pred with
  | True -> "True"
  | False -> "False"
  | Test (field, b) -> "Test " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | And (pred1, pred2) -> "And " ^ (pred_to_string pred1) ^ " " ^ (pred_to_string pred2)
  | OrP (pred1, pred2) -> "OrP " ^ (pred_to_string pred1) ^ " " ^ (pred_to_string pred2)
  | Neg pred -> "Neg " ^ (pred_to_string pred)

let rec pkr_to_string (pkr:pkr):string= 
  match pkr with
  | Id -> "Id"
  | Empty -> "Empty"
  | LeftTest (field, b) -> "LeftTest " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | RightTest (field, b) -> "RightTest " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | LeftAsgn (field, b) -> "LeftAsgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | RightAsgn (field, b) -> "RightAsgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | Comp (pkr1, pkr2) -> "Comp " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)
  | Or (pkr1,pkr2) -> "Or " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)

let rec nk_to_string (nk:NK.t):string=
  match nk with
  | Pred pred -> "Pred " ^ (pred_to_string pred)
  | Asgn (field, b) -> "Asgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | Union nks -> "Union " ^ (SNK.fold (fun nk acc -> acc ^ (nk_to_string nk) ^ " ") nks "")
  | Seq (nk1, nk2) -> "Seq " ^ (nk_to_string nk1) ^ " " ^ (nk_to_string nk2)
  | Star nk -> "Star " ^ (nk_to_string nk)
  | Dup -> "Dup"

let rec rel_to_string (rel:Rel.t):string =
  match rel with
  | Left pkr -> "Left " ^ (pkr_to_string pkr)
  | Right pkr -> "Right " ^ (pkr_to_string pkr)
  | Binary pkr -> "Binary " ^ (pkr_to_string pkr)
  | OrR sr -> "OrR " ^ (SR.fold (fun r acc -> acc ^ (rel_to_string r) ^ " ") sr "")
  | SeqR (rel1, rel2) -> "SeqR " ^ (rel_to_string rel1) ^ " " ^ (rel_to_string rel2)
  | StarR rel -> "StarR " ^ (rel_to_string rel)  

let nkro_map_to_string (mapping:(MLBDD.t)NKROMap.t):string=
  let str = ref "" in
    NKROMap.iter (fun (nko,ro) bdd -> str := !str ^ (match nko with
                                                        | None -> "None"
                                                        | Some nk -> nk_to_string nk) ^ " " ^ (match ro with
                                                                                                    | None -> "None"
                                                                                                    | Some r -> rel_to_string r) ^ "\n") mapping;
    !str

let init_man (field_max:field) (bman_cache:int) = 
  {field_max = field_max; bman = MLBDD.init ~cache:bman_cache ()}
(* The variable is in order of x x' y y' --> 5k, 5k+1, 5k+2, 5k+3*)
let bddvar (man:man) (pk:pk) (field:field) = field*5 + pk

let generate_single_var (man:man) (pk:pk) (field:field):MLBDD.t =
    MLBDD.ithvar (man.bman) (bddvar man pk field)

let bdd_true (man:man):MLBDD.t = MLBDD.dtrue man.bman    

let bdd_false (man:man):MLBDD.t = MLBDD.dfalse man.bman    

let compile_pred_bdd (man:man)(pk:pk) (predicate:pred):MLBDD.t = 
     let rec compile_pred_bdd_aux (predicate:pred):MLBDD.t =
	match predicate with
    	| True -> bdd_true man
    	| False -> bdd_false man
  		| Test (field,false) -> MLBDD.dnot (generate_single_var man pk field)
  		| Test (field,true) -> generate_single_var man pk field
  		| And (pred1,pred2) -> MLBDD.dand (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| OrP (pred1,pred2) -> MLBDD.dor (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
  		| Neg predicate -> MLBDD.dnot (compile_pred_bdd_aux predicate)
  	in compile_pred_bdd_aux predicate

let produce_id (man:man) (pk1:pk) (pk2:pk):MLBDD.t =
     let rec produce_id_aux (cur:field):MLBDD.t =
         if cur > man.field_max then 
          bdd_true man
         else  
          MLBDD.dand (MLBDD.nxor (generate_single_var man pk1 cur) ((generate_single_var man pk2 cur))) (produce_id_aux (cur+1))
     in produce_id_aux 0

let produce_assign (man:man) (pk1:pk) (pk2:pk) (field:field)(asgn:bool) (left:bool):MLBDD.t =
     let rec produce_assign_aux (cur:field):MLBDD.t =
         if cur > man.field_max then 
           bdd_true man
         else if left && field = cur then 
                   MLBDD.dand (if asgn then 
                                  (generate_single_var man pk1 cur)
                               else 
                                  MLBDD.dnot (generate_single_var man pk1 cur))
                              (produce_assign_aux (cur+1))         
         else if (not left) && field = cur then
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

let generate_double_support (man:man) (pk1:pk) (pk2:pk):MLBDD.support =
  let rec generate_list (cur:field):int list =
      if cur > man.field_max then []
      else (bddvar man pk1 cur)::(bddvar man pk2 cur)::(generate_list (cur+1))
  in MLBDD.support_of_list (generate_list 0)
  
  
let comp_bdd (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> 'a -> MLBDD.t) (con1: 'a) (con2: 'a):MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    MLBDD.exists (generate_support man pk3) (MLBDD.dand (compiler man pk1 pk3 con1) (compiler man pk3 pk2 con2))    
      
let rec compile_pkr_bdd (man:man)(pk1:pk) (pk2:pk) (pkr:pkr):MLBDD.t = 
     let rec compile_pkr_bdd_aux (pkr:pkr):MLBDD.t =
	match pkr with
	  | Id -> produce_id man pk1 pk2
	  | Empty -> bdd_false man
	  | LeftTest (field, false) -> (MLBDD.dand (produce_id man pk1 pk2) (MLBDD.dnot (generate_single_var man pk1 field)))
	  | LeftTest (field, true) -> (MLBDD.dand (produce_id man pk1 pk2) (generate_single_var man pk1 field))
	  | RightTest (field, false) -> (MLBDD.dand (produce_id man pk1 pk2) (MLBDD.dnot (generate_single_var man pk2 field)))
	  | RightTest (field, true) -> (MLBDD.dand (produce_id man pk1 pk2) (generate_single_var man pk2 field))
	  | LeftAsgn (field, b) -> produce_assign man pk1 pk2 field b true  
	  | RightAsgn (field, b) -> produce_assign man pk1 pk2 field b false  
	  | Comp (pkr1, pkr2) -> comp_bdd man pk1 pk2 compile_pkr_bdd pkr1 pkr2
    | Or (pkr1,pkr2)-> MLBDD.dor (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
  	in compile_pkr_bdd_aux pkr

let rename_bdd (man:man) (pk1:pk) (pk2:pk) (bdd:MLBDD.t):MLBDD.t =
  let id12 = produce_id man pk1 pk2 in
    let support = generate_support man pk1 in
    (MLBDD.exists support (MLBDD.dand id12 bdd))

(* A naive implementation, to be optimized*)    
let closure_bdd (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> 'a -> MLBDD.t) (con:'a) :MLBDD.t =
  (* input cur is of pk1 and pk2 *)
  let pk3 = generate_unused_pk pk1 pk2 in
    let support2 = generate_support man pk2 in
      let con_bdd_23 = compiler man pk2 pk3 con in
       let rec closure_bdd_aux (cur_12:MLBDD.t):MLBDD.t =
         let next = MLBDD.dor cur_12 (rename_bdd man pk3 pk2 (MLBDD.exists support2 (MLBDD.dand cur_12 con_bdd_23))) in
           if MLBDD.equal cur_12 next then
               cur_12
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
   NKOMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) mapping1 mapping2

let union_nkro_mapping (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
   NKROMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) mapping1 mapping2

let union_nkro_mapping_updated (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):((MLBDD.t)NKROMap.t*bool)=
   NKROMap.fold (fun con bdd (mapping,changed) -> 
            match add_nkro_mapping_updated con bdd mapping with
              | (mapping',true) -> (mapping',true)
              | (mapping',false) -> (mapping',changed)
            ) mapping1 (mapping2,false)

let apply_nko_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
  NKOMap.filter_map (fun _ bdd-> let nbdd = tobdd bdd in 
                                    if (MLBDD.is_false nbdd) then
                                       None
                                    else Some nbdd) mapping

let apply_nkro_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
  NKROMap.filter_map (fun _ bdd-> let nbdd = tobdd bdd in 
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

let filtering_epsilon (nkom:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t =
  NKOMap.remove None nkom  
                            
(* We assume the invariant here is the return value is canoicalized *) 
let rec delta_k (man:man)(pk1:pk)(pk2:pk)(nko:NK.t option): (MLBDD.t)NKOMap.t=
    match nko with
      | None -> NKOMap.empty
    	| Some (Pred pred) -> NKOMap.singleton None (MLBDD.dand (compile_pred_bdd man pk1 pred) (produce_id man pk1 pk2))  
    	| Some (Asgn (field, b)) -> NKOMap.singleton None (produce_assign man pk1 pk2 field b false)
  	  | Some (Union nks) -> SNK.fold (fun nk acc -> union_nko_mapping (delta_k man pk1 pk2 (Some nk)) acc) nks NKOMap.empty
  	  | Some (Seq(nk1,nk2)) -> let pk3 =  generate_unused_pk pk1 pk2 in
                                  let support = generate_support man pk3 in
                                    union_nko_mapping (concatenate_nko_mapping (filtering_epsilon (delta_k man pk1 pk2 (Some nk1))) (Some nk2))
  	                                (let epsilon = folding_epsilon man (delta_k man pk1 pk3 (Some nk1)) in
                                      (apply_nko_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) (delta_k man pk3 pk2 (Some nk2))))
  	  | Some (Star nk) -> let pk3 = generate_unused_pk pk1 pk2 in
                      	                      let support = generate_support man pk3 in
                                                let epsilon = closure_bdd man pk1 pk3 (fun man pk1 pk2 nk 
                                                                                            -> folding_epsilon man (delta_k man pk1 pk2 (Some nk))) nk in                         
                                                 apply_nko_mapping (fun bdd -> MLBDD.exists support (MLBDD.dand epsilon bdd)) 
                                                 (add_nko_mapping None (produce_id man pk3 pk2)
                                                  (concatenate_nko_mapping (filtering_epsilon (delta_k man pk3 pk2 (Some nk))) (Some (Star nk)))) 
      | Some Dup -> NKOMap.singleton (Some (Pred True)) (produce_id man pk1 pk2)
(* For epsilon kr, there is no transition on the y or the input tape, thus we only need two tape denoting the before
and after hidden state *)

let comp_nkro_map (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> (NK.t option*Rel.t option)
       -> (MLBDD.t)NKROMap.t) (nko: NK.t option) (r1: Rel.t) (r2:Rel.t):(MLBDD.t)NKROMap.t =
       union_nkro_mapping (concatenate_nkro_mapping (compiler man pk1 pk2 (nko,Some r1)) (None,(Some r2)))
                          (let pk3 = generate_unused_pk pk1 pk2 in
                            let support = generate_support man pk3 in
                              NKROMap.fold (fun (nko,ro) bdd acc -> 
                                                               match ro with
                                                              | None
                                                              | Some (StarR _) -> union_nkro_mapping (apply_nkro_mapping (fun nbdd -> MLBDD.exists support (MLBDD.dand bdd nbdd)) (compiler man pk3 pk2 (nko,Some r2))) acc
                                                              | _ -> acc
                              ) (compiler man pk1 pk3 (nko,Some r1)) NKROMap.empty) 
          
let closure_nkro_map (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> (NK.t option*Rel.t option)
       -> (MLBDD.t)NKROMap.t) (nko: NK.t option) (r: Rel.t):(MLBDD.t)NKROMap.t =
       let pk3 = generate_unused_pk pk1 pk2 in
         let support2 = generate_support man pk2 in
           let rec closure_nkro_map_aux (cur:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t =
              match union_nkro_mapping_updated (NKROMap.fold (fun (nko,ro) bdd acc
                                        -> match ro with
                                              | None
                                              | Some (StarR _) -> union_nkro_mapping (apply_nkro_mapping (fun nbdd 
                                                  -> (rename_bdd man pk3 pk2 
                                                          (MLBDD.exists support2 (MLBDD.dand bdd nbdd)))) (compiler man pk2 pk3 (nko,Some r))) acc
                                              |  _ -> acc) cur NKROMap.empty) cur with
                    | (next,false) -> next
                    | (next,true) -> closure_nkro_map_aux next
                in let closure_map =  (closure_nkro_map_aux (NKROMap.singleton (nko,None) (produce_id man pk1 pk2))) in
                  (concatenate_nkro_mapping closure_map (None,(Some (StarR r))))                        
                                             
let rec epsilon_kr (man:man) (pk1:pk) (pk2:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t =
  add_nkro_mapping nkro (produce_id man pk1 pk2)
  (match nkro with
    | (nko,None) -> NKROMap.empty
    | (nko,Some (Left pkr)) -> let pkr_bdd = compile_pkr_bdd man pk1 pk2 pkr in
                                  NKOMap.fold (fun nko bdd acc -> NKROMap.add (nko,None) bdd acc) (apply_nko_mapping (fun bdd -> MLBDD.dand bdd pkr_bdd) (delta_k man pk1 pk2 nko)) NKROMap.empty
    | (nko,Some (Right pkr)) -> NKROMap.empty
    | (nko,Some (Binary pkr)) -> NKROMap.empty
    | (nko,Some (OrR rs)) -> SR.fold (fun r acc -> union_nkro_mapping (epsilon_kr man pk1 pk2 (nko,Some r)) acc) rs NKROMap.empty
    | (nko,Some (SeqR (r1,r2))) -> comp_nkro_map man pk1 pk2 epsilon_kr nko r1 r2
    | (nko,Some (StarR r)) -> closure_nkro_map man pk1 pk2 epsilon_kr nko r)                                       

let generate_unused_pk5 (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk):pk =
  10 - pk1 - pk2 - pk3 - pk4 

(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(* Note that we have the epsilon equivalence class, we do the epsilon in the beginning, and then every delta transition then is
followed by epsilon
*)
let delta_kr (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t=
   let rec delta_kr_aux (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkro:(NK.t option*Rel.t option)) :(MLBDD.t)NKROMap.t=
      let pk5 = generate_unused_pk5 pk1 pk2 pk3 pk4 in
        let support = generate_support man pk5 in
          (NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (fun ebdd -> (MLBDD.exists support (MLBDD.dand bdd ebdd))) (epsilon_kr man pk5 pk2 nkro)) acc)
      (*Here we switch from pk1 pk2 pk3 pk4 to pk1 pk5 pk3 pk4*)   
      (match nkro with
        | (nko,None) -> NKROMap.empty
        | (nko,Some (Left pkr)) -> NKROMap.empty
        | (nko,Some (Right pkr)) -> let pkr_bdd = compile_pkr_bdd man pk3 pk4 pkr in
                                        NKROMap.singleton (nko,None) pkr_bdd
        | (nko,Some (Binary pkr)) -> let pkr_bdd = compile_pkr_bdd man pk5 pk4 pkr in
                                        NKOMap.fold (fun nko bdd acc -> NKROMap.add (nko,None) bdd acc) (apply_nko_mapping (fun bdd -> MLBDD.dand bdd pkr_bdd) (delta_k man pk1 pk5 nko)) NKROMap.empty
        | (nko,Some (OrR rs)) -> SR.fold (fun r acc -> union_nkro_mapping (delta_kr_aux man pk1 pk5 pk3 pk4 (nko,Some r)) acc) rs NKROMap.empty                                
     (*Here we already start with the epsilon closure of a (nko,r1), thus we don't need to deal with the epsilon cases*)
        | (nko,Some (SeqR (r1,r2))) -> (concatenate_nkro_mapping (delta_kr_aux man pk1 pk5 pk3 pk4 (nko,Some r1)) (None,(Some r2)))
        | (nko,Some (StarR r)) -> (concatenate_nkro_mapping (delta_kr_aux man pk1 pk5 pk3 pk4 (nko,Some r)) (None,(Some (StarR r))))) 
          NKROMap.empty)
    in       
      let pk5 = generate_unused_pk5 pk1 pk2 pk3 pk4 in
        let support = generate_support man pk5 in
        (NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (fun ebdd -> (MLBDD.exists support (MLBDD.dand bdd ebdd))) 
            (delta_kr_aux man pk5 pk2 pk3 pk4 nkro)) acc) (epsilon_kr man pk1 pk5 nkro) NKROMap.empty)
            
let calculate_reachable_set (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkr:NK.t*Rel.t):(MLBDD.t)NKROMap.t =
  let support12 = generate_double_support man pk1 pk2 in
  let worklist = Queue.create() in
      let rec calculate_reachable_set_aux (cur:(MLBDD.t)NKROMap.t): (MLBDD.t)NKROMap.t=
        match Queue.take_opt worklist with
          | None -> cur
          | Some (nkro,bdd) -> 
            calculate_reachable_set_aux (NKROMap.fold (fun nkro bdd acc-> match (add_nkro_mapping_updated nkro bdd cur) with
                                                | (cur,true) -> Queue.add (nkro,bdd) worklist; cur
                                                | (cur,false) -> cur) 
                                                (apply_nkro_mapping 
                  (fun nbdd -> (rename_bdd man pk3 pk1 (rename_bdd man pk4 pk2 (MLBDD.exists support12 (MLBDD.dand nbdd bdd)))))
                    (delta_kr man pk1 pk2 pk3 pk4 nkro)) cur)
     in Queue.add ((Some (fst nkr),Some (snd nkr)),(produce_id man pk1 pk2)) worklist;
       calculate_reachable_set_aux NKROMap.empty 
    
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
let re_ordering (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd:MLBDD.t):MLBDD.t=
let permute var = if var mod 5 = pk3 then
                      (var / 5)
                    else if var mod 4 = pk1 then
                      (var / 5) + man.field_max
                    else if var mod 4 = pk2 then
                      2*(var / 5) + 2*man.field_max
                    else
                      2*(var / 5) + 2*man.field_max + 1
                    in MLBDD.permutef permute bdd

let back_ordering (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd:MLBDD.t):MLBDD.t=
  let permute var = if var < man.field_max then
                      5 * var + pk3
                    else if var < 2*man.field_max then
                      5* (var - man.field_max) + pk1
                    else if var mod 2 = 0 then
                      (var - 2* man.field_max) / 2 * 5 + pk2
                    else
                      (var - 2* man.field_max -1) / 2 * 5 + pk4
                    in MLBDD.permutef permute bdd

let var_low_branch (man:man) (var:int) (bdd:MLBDD.t):MLBDD.t=
 (MLBDD.dand (MLBDD.dnot (MLBDD.ithvar man.bman var)) bdd)

let var_high_branch (man:man) (var:int) (bdd:MLBDD.t):MLBDD.t=
 (MLBDD.dand (MLBDD.ithvar man.bman var) bdd)

let var_if (man:man) (var:int) (lbdd:MLBDD.t) (hbdd:MLBDD.t):MLBDD.t=
 (MLBDD.dor (var_low_branch man var lbdd) (var_high_branch man var lbdd))

let splitting_bdd (man:man)(pk1:pk)(pk2:pk)(pk3:pk)(pk4:pk) (bdd:MLBDD.t): MLBDD.t list =
  let splitting_bdd_aux (bdd:MLBDD.t): MLBDD.t * MLBDD.t =  
  MLBDD.foldb (fun btree -> 
                      match btree with
                            | MLBDD.BFalse -> (bdd_false man,bdd_false man)  
                            | MLBDD.BTrue -> (bdd_true man,bdd_false man) 
                            | MLBDD.BIf (low,var,high) -> if var < man.field_max then
                                                             (var_if man var (fst low) (fst high), var_if man var (snd low) (snd high))
                                                          else if var < man.field_max*2 then
                                                             if MLBDD.is_false (fst low) then
                                                               (var_high_branch man var (fst high),var_high_branch man var(snd high))
                                                             else 
                                                               (var_low_branch man var (fst low),MLBDD.dand (var_low_branch man var (snd low)) (var_if man var (fst high) (snd high))) 
                                                          else   
                                                            (var_if man var (fst low) (fst high), bdd_false man)                               
                            ) bdd in
    let rec loop (cur:MLBDD.t list) (bdd:MLBDD.t):MLBDD.t list = 
      if MLBDD.is_false bdd then cur
      else let (low,high) = splitting_bdd_aux bdd in
            loop (low::cur) high in
    List.map (fun bdd -> back_ordering man pk1 pk2 pk3 pk4 bdd) (loop [] (re_ordering man pk1 pk2 pk3 pk4 bdd))                         
 
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
let generate_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkr:NK.t*Rel.t):((MLBDD.t)list*((MLBDD.t)list)NKROMap.t)NKROMap.t=
  let support24 = generate_double_support man pk2 pk4 in
  NKROMap.mapi (fun nkro bdd -> let new_delta = NKROMap.map (fun bdd -> splitting_bdd man pk1 pk2 pk3 pk4 bdd) 
                                    (apply_nkro_mapping (fun tbdd -> (MLBDD.dand tbdd bdd)) (delta_kr man pk1 pk2 pk3 pk4 nkro)) in
                                  let hidden_state_l = (NKROMap.fold (fun nkro blist acc -> List.append (List.map (fun bdd -> MLBDD.exists support24 bdd) blist) acc) new_delta []) in
                                      (hidden_state_l,new_delta)) (calculate_reachable_set man pk1 pk2 pk3 pk4 nkr)

let find_bddl (nkro:NK.t option*Rel.t option)(transition:((MLBDD.t)list*((MLBDD.t)list)NKROMap.t)NKROMap.t):MLBDD.t list=
  match NKROMap.find_opt nkro transition with
    | None -> failwith "Transition not found"
    | Some (bddl,_) -> bddl                           

let simplify_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkr:NK.t*Rel.t):((MLBDD.t)NKROBMap.t)NKROBMap.t=
  let support12 = generate_double_support man pk1 pk2 in
  let all_transition = generate_all_transition man pk1 pk2 pk3 pk4 nkr in
    NKROMap.fold (fun nkro1 (_,nkrom) acc -> NKROMap.fold (fun nkro2 hbddl1 acc ->
                                        let hbddl2 = find_bddl nkro2 all_transition
                                          in List.fold_right (fun hbdd1 acc -> 
                                             List.fold_right (fun hbdd2 acc -> 
                                              let tbddf = MLBDD.dand hbdd1 (rename_bdd man pk1 pk2 (rename_bdd man pk3 pk4 hbdd2)) in
                                              if MLBDD.is_false tbddf then
                                                acc
                                              else
                                                NKROBMap.add (nkro1,hbdd1) (NKROBMap.singleton (nkro2,hbdd2) (MLBDD.exists support12 tbddf)) acc)
                                          hbddl2 acc) hbddl1 acc) nkrom acc) all_transition NKROBMap.empty
                                        
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
                                          Queue.add ((nkros1,nkros2),(rename_bdd man pk2 pk1 (MLBDD.dand bdd (MLBDD.dand bdd1 bdd2)))) worklist) next2) next1;
                                          (let reachable_bdd = (NKROBSMap.fold (fun nkros2 bdd2 acc -> MLBDD.dor acc bdd2) next2 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros1 bdd1 -> 
                                              Queue.add ((nkros1,NKROBSet.empty),(rename_bdd man pk2 pk1 (MLBDD.dand bdd (MLBDD.dand bdd1 (MLBDD.dnot reachable_bdd))))) worklist) next1);
                                          (let reachable_bdd = (NKROBSMap.fold (fun nkros1 bdd1 acc -> MLBDD.dor acc bdd1) next1 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros2 bdd2 -> 
                                              Queue.add ((NKROBSet.empty,nkros2),(rename_bdd man pk2 pk1 (MLBDD.dand bdd (MLBDD.dand (MLBDD.dnot reachable_bdd) bdd2)))) worklist) next2);    
                                          bisim_aux newdonelist
  in Queue.add ((start1,start2),bdd_true man) worklist;
     bisim_aux NKROBSSMap.empty 
  