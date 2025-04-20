 (* 
  This module implements a framework for working with Relational NetKAT using Binary Decision Diagrams (BDDs). 
  It provides data structures, types, and functions for representing and manipulating NetKAT expressions, 
  relational expressions, and their corresponding BDD representations. The module supports operations such as 
  determinization, bisimulation, and transition computation, making it suitable for formal verification and 
  reasoning about network behaviors.

  Key Features:
  - Data Structures: Types for representing fields, predicates, packet relations, and NetKAT expressions.
  - BDD Operations: Functions for creating, manipulating, and composing BDDs.
  - Mappings and Sets: Utilities for constructing and manipulating mappings between NetKAT expressions, 
    relational expressions, and BDDs.
  - Transition Computation: Functions for computing reachable sets and transitions in a NetKAT automaton.
  - Determinization: Functions for determinizing NetKAT automata.
  - Bisimulation: Functions for checking bisimilarity between two NetKAT automata.
  - String Conversion: Utilities for converting NetKAT and relational expressions to strings for debugging.

  Main Components:
  - Types:
    - `field`: Represents a field in a packet.
    - `pk`: Represents a packet.
    - `pred`: Represents a predicate in NetKAT (e.g., `True`, `False`, `Test`, `And`, `Or`, `Neg`).
    - `pkr`: Represents a packet relation in NetKAT (e.g., `Id`, `Empty`, `Test`, `LeftAsgn`, `RightAsgn`, `Comp`, etc.).
    - `next_step`: Represents the next step in a transition (`E`, `X`, `Y`, `XY`).

  - Modules:
    - `NK`: Represents NetKAT expressions (e.g., `Pred`, `Pkr`, `Asgn`, `Union`, `Seq`, `Inter`, `Diff`, `Star`, `Dup`).
    - `SNK`: Represents sets of NetKAT expressions.
    - `Rel`: Represents relational expressions (e.g., `Left`, `Right`, `Binary`, `App`, `Id`, `Nil`, `OrR`, `SeqR`, `StarR`).
    - `SR`: Represents sets of relational expressions.
    - `NKOMap`: Represents a mapping from optional NetKAT expressions to BDDs.
    - `ROMap`: Represents a mapping from optional relational expressions to BDDs.
    - `NKROMap`: Represents a mapping from pairs of optional NetKAT and relational expressions to BDDs.
    - `NKROBMap`: Represents a mapping from pairs of optional NetKAT and relational expressions and BDDs to other values.
    - `BSet`: Represents a set of BDDs.
    - `NKROBSet`: Represents a set of pairs of optional NetKAT and relational expressions and BDDs.
    - `NKROBSMap`: Represents a mapping from sets of pairs of optional NetKAT and relational expressions and BDDs to other values.

  - Functions:
    - BDD Operations:
      - `bddvar`: Computes the BDD variable index for a given field and packet.
      - `generate_single_var`: Generates a BDD for a single variable.
      - `bdd_true` / `bdd_false`: Returns the BDD representing `true` or `false`.
      - `compile_pred_bdd`: Compiles a predicate into a BDD.
      - `produce_id`: Produces a BDD representing the identity relation.
      - `produce_assign`: Produces a BDD representing an assignment.
      - `rename_bdd`: Renames variables in a BDD.
      - `closure_bdd`: Computes the closure of a BDD.
      - `comp_bdd` / `comp_bdd_2` / `comp_bdd_4`: Composes BDDs for transitions.

    - Mapping and Set Operations:
      - `add_nko_mapping`, `add_ro_mapping`, `add_nkro_mapping`: Add mappings to BDDs.
      - `union_nko_mapping`, `union_ro_mapping`, `union_nkro_mapping`: Union mappings.
      - `apply_nko_mapping`, `apply_ro_mapping`, `apply_nkro_mapping`: Apply transformations to mappings.
      - `concatenate_nko_mapping`, `concatenate_ro_mapping`, `concatenate_nkro_mapping`: Concatenate mappings.

    - Delta and Transition Functions:
      - `delta_k`: Computes the delta transition for a NetKAT expression.
      - `delta_r`: Computes the delta transition for a relational expression.
      - `delta_krx`: Computes the delta transition with epsilon closure.
      - `delta_kr`: Computes the delta transition for a pair of NetKAT and relational expressions.

    - Determinization and Simplification:
      - `determinize_transition`: Determinizes a transition mapping.
      - `determinization`: Determinizes a NetKAT automaton.
      - `simplify_all_transition`: Simplifies all transitions for a NetKAT automaton.

    - Bisimulation:
      - `bisim`: Checks if two NetKAT automata are bisimilar.

    - String Conversion:
      - `pred_to_string`, `pkr_to_string`, `nk_to_string`, `rel_to_string`, `nkro_to_string`: Convert expressions to strings.

    - Utility Functions:
      - `generate_unused_pk`: Generates an unused packet index.
      - `generate_support`: Generates the support set for a packet.
      - `splitting_bdd`: Splits a BDD into a list of BDDs.
      - `is_final_nkro`, `is_final_nkrob`, `is_final_nkrobs`: Check if states are final.

    - Reordering Functions:
      - `re_ordering`: Reorders variables in a BDD.
      - `back_ordering`: Reverts the reordering of variables in a BDD.

    - Variable Branching:
      - `var_low_branch`, `var_high_branch`, `var_if`: Compute branches of a BDD for a given variable.

  - Purpose:
    This module provides a comprehensive framework for working with Relational NetKAT, enabling the representation, manipulation, and analysis of NetKAT automata using BDDs. It supports operations like determinization, bisimulation, and transition computation, making it suitable for formal verification and reasoning about network behaviors.
*)

  
type field = int
type pk = int

type pred =
  | True
  | False
  | Test of field * bool
  | And of pred * pred
  | Or of pred * pred
  | Neg of pred


type next_step =
 | E
 | X  
 | Y
 | XY
 
type pkr =
  | Id
  | Empty
  | Test of field * bool 
  | LeftAsgn of field * bool
  | RightAsgn of field * bool
  | Comp of pkr * pkr
  | OrP of pkr * pkr
  | AndP of pkr * pkr
  | Binary of pred * pred
  | FMap of field * field

module rec NK : sig
    type t = 
    | Pred of pred
    | Pkr of pkr
    | Asgn of field * bool
    | Union of SNK.t
    | Seq of t * t
    | Inter of t * t
    | Diff of t * t
    | Star of t
    | Dup
    val compare: t -> t -> int
  end
= struct
   type t = 
    | Pred of pred
    | Pkr of pkr
    | Asgn of field * bool
    | Union of SNK.t
    | Seq of t * t
    | Inter of t * t
    | Diff of t * t
    | Star of t
    | Dup
  let rec compare t1 t2 =
      match (t1, t2) with
      | (Pred p1, Pred p2) -> Stdlib.compare p1 p2
      | (Pred _, _) -> 1
      | (_, Pred _) -> -1
      | (Pkr p1,Pkr p2) -> Stdlib.compare p1 p2
      | (Pkr _, _) -> 1
      | (_, Pkr _) -> -1
      | (Asgn (f1, b1), Asgn (f2, b2)) -> let c = Stdlib.compare f1 f2 in if c = 0 then Stdlib.compare b1 b2 else c
      | (Asgn _, _) -> 1
      | (_, Asgn _) -> -1
      | (Union sk1, Union sk2) -> SNK.compare sk1 sk2
      | (Union _, _) -> 1
      | (_, Union _) -> -1
      | (Seq (t1, t2), Seq (t3, t4)) -> let c = compare t1 t3 in if c = 0 then compare t2 t4 else c
      | (Seq _, _) -> 1
      | (_, Seq _) -> -1
      | (Inter (t1, t2), Inter (t3, t4)) -> let c = compare t1 t3 in if c = 0 then compare t2 t4 else c
      | (Inter _, _) -> 1
      | (_, Inter _) -> -1
      | (Diff (t1, t2), Diff (t3, t4)) -> let c = compare t1 t3 in if c = 0 then compare t2 t4 else c
      | (Diff _, _) -> 1
      | (_, Diff _) -> -1
      | (Star t1, Star t2) -> compare t1 t2
      | (Star _, _) -> 1
      | (_, Star _) -> -1
      | (Dup, Dup) -> 0
  end
and SNK : Set.S with type elt = NK.t
= Set.Make(NK)



module rec Rel : sig
  type t = 
  | Left of NK.t
  | Right of NK.t
  | Binary of NK.t * NK.t
  | App of pkr * pkr
  | Id of NK.t
  | Nil of pkr
  | OrR of SR.t
  | SeqR of t * t
  | StarR of t
  | IdComp of NK.t option * t
  val compare: t -> t -> int
end
= struct
 type t = 
 | Left of NK.t
 | Right of NK.t
 | Binary of NK.t * NK.t
 | App of pkr * pkr
 | Id of NK.t
 | Nil of pkr
 | OrR of SR.t
 | SeqR of t * t
 | StarR of t
 | IdComp of NK.t option * t
 let rec compare t1 t2 =
  match (t1, t2) with
  | (Left nk1, Left nk2) -> NK.compare nk1 nk2
  | (Left _, _) -> 1
  | (_, Left _) -> -1
  | (Right nk1, Right nk2) -> NK.compare nk1 nk2
  | (Right _, _) -> 1
  | (_, Right _) -> -1
  | (Binary (nk11,nk12), Binary (nk21,nk22)) -> let c = NK.compare nk11 nk21 in if c = 0 then NK.compare nk12 nk22 else c
  | (Binary _, _) -> 1
  | (_, Binary _) -> -1
  | (App (pkr1, pkr2), App (pkr3, pkr4)) -> let c = Stdlib.compare pkr1 pkr3 in if c = 0 then Stdlib.compare pkr2 pkr4 else c
  | (App _, _) -> 1
  | (_, App _) -> -1
  | (Id nk1, Id nk2) -> NK.compare nk1 nk2
  | (Id _, _) -> 1
  | (_, Id _) -> -1
  | (Nil p1, Nil p2) -> Stdlib.compare p1 p2
  | (Nil _, _) -> 1
  | (_, Nil _) -> -1
  | (OrR sr1, OrR sr2) -> SR.compare sr1 sr2
  | (OrR _, _) -> 1
  | (_, OrR _) -> -1
  | (SeqR (t1, t2), SeqR (t3, t4)) -> let c = compare t1 t3 in if c = 0 then compare t2 t4 else c
  | (SeqR _, _) -> 1
  | (_, SeqR _) -> -1
  | (StarR t1, StarR t2) -> compare t1 t2
  | (StarR _, _) -> 1
  | (_, StarR _) -> -1
  | (IdComp (nko1, t1), IdComp (nko2, t2)) -> let c = Option.compare NK.compare nko1 nko2 in if c = 0 then compare t1 t2 else c
  end
and SR : Set.S with type elt = Rel.t
= Set.Make(Rel)

module NKOMap = Map.Make(
  struct type t = NK.t option 
  let compare = (Option.compare NK.compare) end)

module ROMap = Map.Make(
  struct type t = Rel.t option 
  let compare = (Option.compare Rel.compare) end)

module BMap = Map.Make(
  struct type t = MLBDD.t 
  let compare a b = compare (MLBDD.id a) (MLBDD.id b) 
end)  

let nkro_compare a b = 
  let c = Option.compare NK.compare (fst a) (fst b) in
  if c = 0 then Option.compare Rel.compare (snd a) (snd b) else c


module NKROMap = Map.Make(
struct type t = (NK.t option*Rel.t option) 
let compare = nkro_compare
end)

module NKROBMap = Map.Make(
struct type t = (NK.t option*Rel.t option)*MLBDD.t 
let compare a b = let c = nkro_compare (fst a) (fst b) in if c = 0 then compare (MLBDD.id (snd a)) (MLBDD.id (snd b)) else c
end)

module BSet = Set.Make(
  struct type t = MLBDD.t 
  let compare a b = compare (MLBDD.id a) (MLBDD.id b)
end)

module NKROBSet = Set.Make(
  struct type t = (NK.t option*Rel.t option)*MLBDD.t 
  let compare a b = let c = nkro_compare (fst a) (fst b) in if c = 0 then compare (MLBDD.id (snd a)) (MLBDD.id (snd b)) else c
end)
  
module NKROBSMap = Map.Make(
  struct type t = NKROBSet.t
  let compare = NKROBSet.compare
end)

module NKROBSSMap = Map.Make(
  struct type t = (NKROBSet.t*NKROBSet.t) 
  let compare a b = let c = NKROBSet.compare (fst a) (fst b) in if c = 0 then NKROBSet.compare (snd a) (snd b) else c
end)

type man = {
  field_max: field;
  bman:MLBDD.man;
  split_hist:MLBDD.t MLBDD.hist;
}
let rec pred_to_string (pred:pred):string= 
  match pred with
  | True -> "True"
  | False -> "False"
  | Test (field, b) -> "Test " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | And (pred1, pred2) -> "And " ^ (pred_to_string pred1) ^ " " ^ (pred_to_string pred2)
  | Or (pred1, pred2) -> "Or " ^ (pred_to_string pred1) ^ " " ^ (pred_to_string pred2)
  | Neg pred -> "Neg " ^ (pred_to_string pred)

let rec pkr_to_string (pkr:pkr):string= 
  match pkr with
  | Id -> "Id"
  | Empty -> "Empty"
  | Test (field, b) -> "Test " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | LeftAsgn (field, b) -> "LeftAsgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | RightAsgn (field, b) -> "RightAsgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | Comp (pkr1, pkr2) -> "Comp " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)
  | OrP (pkr1,pkr2) -> "OrP " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)
  | AndP (pkr1,pkr2) -> "AndP " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)
  | Binary (pred1,pred2) -> "Binary (" ^ (pred_to_string pred1) ^ ", " ^ (pred_to_string pred2) ^ ")"
  | FMap (field1,field2) -> "FMap " ^ (string_of_int field1) ^ " " ^ (string_of_int field2)

let rec nk_to_string (nk:NK.t):string=
  match nk with
  | Pred pred -> "Pred " ^ (pred_to_string pred)
  | Pkr pkr -> "Pkr " ^ (pkr_to_string pkr)
  | Asgn (field, b) -> "Asgn " ^ (string_of_int field) ^ " " ^ (string_of_bool b)
  | Union sk -> "Union " ^ (SNK.fold (fun nk acc -> acc ^ (nk_to_string nk) ^ " ") sk "")
  | Seq (nk1, nk2) -> "Seq " ^ (nk_to_string nk1) ^ " " ^ (nk_to_string nk2)
  | Inter (nk1, nk2) -> "Inter " ^ (nk_to_string nk1) ^ " " ^ (nk_to_string nk2)
  | Diff (nk1, nk2) -> "Diff " ^ (nk_to_string nk1) ^ " " ^ (nk_to_string nk2)
  | Star nk -> "Star " ^ (nk_to_string nk)
  | Dup -> "Dup"

let rec rel_to_string (rel:Rel.t):string =
  match rel with
  | Left nk -> "Left " ^ (nk_to_string nk)
  | Right nk -> "Right " ^ (nk_to_string nk)
  | Binary (nk1, nk2) -> "Binary (" ^ (nk_to_string nk1) ^ ", " ^ (nk_to_string nk2) ^ ")"
  | App (pkr1, pkr2) -> "App " ^ (pkr_to_string pkr1) ^ " " ^ (pkr_to_string pkr2)
  | Id nk -> "Id " ^ (nk_to_string nk)
  | Nil pkr -> "Nil " ^ (pkr_to_string pkr)
  | OrR sr -> "OrR " ^ (SR.fold (fun rel acc -> acc ^ (rel_to_string rel) ^ " ") sr "")
  | SeqR (rel1, rel2) -> "SeqR " ^ (rel_to_string rel1) ^ " " ^ (rel_to_string rel2)
  | StarR rel -> "StarR " ^ (rel_to_string rel)
  | IdComp (None, rel) -> "IdComp None " ^ (rel_to_string rel)
  | IdComp (Some nk, rel) -> "IdComp " ^ (nk_to_string nk) ^ " " ^ (rel_to_string rel)
 
let nkro_to_string (nkro:NK.t option*Rel.t option):string=
  match nkro with
  | (None, None) -> "None, None"
  | (Some nk, None) -> (nk_to_string nk) ^ ", None"
  | (None, Some r) -> "None, " ^ (rel_to_string r)
  | (Some nk, Some r) -> (nk_to_string nk) ^ ", " ^ (rel_to_string r)

let nko_map_to_string (mapping:(MLBDD.t)NKOMap.t):string=
  let str = ref "" in
    NKOMap.iter (fun nko bdd -> str := !str ^ (match nko with
                                                  | None -> "None"
                                                  | Some nk -> nk_to_string nk) ^" bdd id: "^(string_of_int (MLBDD.id bdd)) ^ "\n") mapping;
    !str

let ro_map_to_string (mapping:(MLBDD.t)ROMap.t):string=
  let str = ref "" in
    ROMap.iter (fun ro bdd -> str := !str ^ (match ro with
                                                  | None -> "None"
                                                  | Some r -> rel_to_string r) ^" bdd id: "^(string_of_int (MLBDD.id bdd)) ^ "\n") mapping;
    !str


let bset_to_string (bset:BSet.t):string=
  let str = ref "" in
    BSet.iter (fun bdd -> str := !str ^ (string_of_int (MLBDD.id bdd)) ^ " ") bset;
    !str

let nkro_map_to_string (mapping:(MLBDD.t)NKROMap.t):string=
  let str = ref "" in
    NKROMap.iter (fun (nko,ro) bdd -> str := !str ^ (match nko with
                                                      | None -> "None"
                                                      | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                  | None -> "None"
                                                                                                  | Some r -> rel_to_string r) ^" bdd id: "^(string_of_int (MLBDD.id bdd)) ^ "\n") mapping;
  !str

let nkrob_map_to_string (mapping:(MLBDD.t)NKROBMap.t):string=
  let str = ref "" in
    NKROBMap.iter (fun ((nko,ro),bdd) bdd' -> str := !str ^ (match nko with
                                                        | None -> "None"
                                                        | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                    | None -> "None"
                                                                                                    | Some r -> rel_to_string r) ^" tag bdd id: "^(string_of_int (MLBDD.id bdd)) ^" transition bdd id: "^(string_of_int (MLBDD.id bdd')) ^ "\n") mapping;
    !str

let nkrobs_to_string (nkrobs:NKROBSet.t):string=
  let str = ref "" in
    NKROBSet.iter (fun ((nko,ro),bdd) -> str := !str ^ (match nko with
                                                        | None -> "None"
                                                        | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                    | None -> "None"
                                                                                                    | Some r -> rel_to_string r) ^" tag bdd id: "^(string_of_int (MLBDD.id bdd)) ^ "\n") nkrobs;
    !str
  
let nkrobs_map_to_string (mapping:(MLBDD.t)NKROBSMap.t):string=
  let str = ref "" in
    NKROBSMap.iter (fun nkrobs bdd -> str := !str ^ "\n" ^ (nkrobs_to_string nkrobs) ^"transition bdd id: "^(string_of_int (MLBDD.id bdd)) ^ "\n") mapping;
    !str

let nkros_map_to_string (mapping:(BSet.t)NKROMap.t):string=
  let str = ref "" in
    NKROMap.iter (fun (nko,ro) bdd_set -> str := !str ^ (match nko with
                                                          | None -> "None"
                                                          | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                      | None -> "None"
                                                                                                      | Some r -> rel_to_string r) ^ "\n" ^ (BSet.fold (fun bdd acc  -> acc ^ (string_of_int (MLBDD.id bdd) ^ " ")) bdd_set "") ^ "\n") mapping;
    !str
     
let transition_set_map_to_string (mapping:(BSet.t*(BSet.t)NKROMap.t)NKROMap.t):string=
  let str = ref "" in
    NKROMap.iter (fun (nko,ro) (bdd_set,bdd_map) -> str := !str ^ "Source node: \n" ^(match nko with
                                                                  | None -> "None"
                                                                  | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                  | None -> "None"
                                                                                                  | Some r -> rel_to_string r) ^ "\nSource bdd sets:\n" ^ (BSet.fold (fun bdd acc  -> acc ^ (string_of_int (MLBDD.id bdd) ^ " ")) bdd_set "") ^ "\nDest nodes:\n" ^ (nkros_map_to_string bdd_map) ^ "\n") mapping;
  !str

let transition_map_to_string (mapping:((MLBDD.t)NKROBMap.t)NKROBMap.t):string=
   let str = ref "" in
    NKROBMap.iter (fun ((nko,ro),bdd) bdd_map -> str := !str ^ "Source node: \n" ^(match nko with
                                                        | None -> "None"
                                                        | Some nk -> nk_to_string nk) ^ ", " ^ (match ro with
                                                                                                    | None -> "None"
                                                                                                    | Some r -> rel_to_string r) ^ " tag bdd id: " ^(string_of_int (MLBDD.id bdd)) ^ "\nDest nodes:\n" ^ (nkrob_map_to_string bdd_map) ^ "\n") mapping;
    !str

let determinized_transition_map_to_string (mapping:((MLBDD.t)NKROBSMap.t)NKROBSMap.t):string=
    let str = ref ""
    in NKROBSMap.iter (fun nkrobs nkrobs_map -> str := !str ^ "\nSource node: \n" ^ (nkrobs_to_string nkrobs)  ^ "\nDest nodes:\n" ^ (nkrobs_map_to_string nkrobs_map) ^ "\n") mapping;
    !str
    
let init_man (field_max:field) (bman_cache:int) = 
  let bman = MLBDD.init ~cache:bman_cache () in
  {field_max = field_max; bman = bman;split_hist = MLBDD.fold_init bman}
(* The variable is in order of x x' y y' --> 6k, 6k+1, 6k+2, 6k+3*)
let bddvar (pk:pk) (field:field) = field*6 + pk

let generate_single_var (man:man) (pk:pk) (field:field):MLBDD.t =
    MLBDD.ithvar (man.bman) (bddvar pk field)

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
      | Or (pred1,pred2) -> MLBDD.dor (compile_pred_bdd_aux pred1) (compile_pred_bdd_aux pred2)
      | Neg predicate -> MLBDD.dnot (compile_pred_bdd_aux predicate)
    in compile_pred_bdd_aux predicate

let produce_id (man:man) (pk1:pk) (pk2:pk):MLBDD.t =
     let rec produce_id_aux (cur:field):MLBDD.t =
         if cur >= man.field_max then 
          bdd_true man
         else  
          MLBDD.dand (MLBDD.nxor (generate_single_var man pk1 cur) ((generate_single_var man pk2 cur))) (produce_id_aux (cur+1))
     in produce_id_aux 0

let produce_assign (man:man) (pk1:pk) (pk2:pk) (field:field)(asgn:bool) (left:bool):MLBDD.t =
     let rec produce_assign_aux (cur:field):MLBDD.t =
         if cur >= man.field_max then 
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

let generate_unused_pk56 (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk):pk*pk =
  let all_pks = [0; 1; 2; 3; 4; 5] in
  let used_pks = [pk1; pk2; pk3; pk4] in
  let unused_pks = List.filter (fun pk -> not (List.mem pk used_pks)) all_pks in
match unused_pks with
  | [pk5; pk6] -> (pk5, pk6)
  | _ -> failwith "Unexpected number of unused packet indices"
  
let generate_support (man:man) (pk:pk):MLBDD.support =
  let rec generate_list (cur:field):int list =
     if cur >= man.field_max then []
     else (bddvar pk cur)::(generate_list (cur+1))
  in MLBDD.support_of_list (generate_list 0)

let generate_double_support (man:man) (pk1:pk) (pk2:pk):MLBDD.support =
  let rec generate_list (cur:field):int list =
      if cur >= man.field_max then []
      else (bddvar pk1 cur)::(bddvar pk2 cur)::(generate_list (cur+1))
  in MLBDD.support_of_list (generate_list 0)
  
  
let comp_bdd (man:man) (pk1:pk) (pk2:pk) (compiler:man -> pk -> pk -> 'a -> MLBDD.t) (con1: 'a) (con2: 'a):MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    MLBDD.exists (generate_support man pk3) (MLBDD.dand (compiler man pk1 pk3 con1) (compiler man pk3 pk2 con2))    
      
let rec compile_pkr_bdd (man:man)(pk1:pk) (pk2:pk) (pkr:pkr):MLBDD.t = 
     let rec compile_pkr_bdd_aux (pkr:pkr):MLBDD.t =
  match pkr with
    | Id -> produce_id man pk1 pk2
    | Empty -> bdd_false man
    | Test (field, false) -> (MLBDD.dand (produce_id man pk1 pk2) (MLBDD.dnot (generate_single_var man pk1 field)))
    | Test (field, true) -> (MLBDD.dand (produce_id man pk1 pk2) (generate_single_var man pk1 field))
    | LeftAsgn (field, b) -> produce_assign man pk1 pk2 field b true  
    | RightAsgn (field, b) -> produce_assign man pk1 pk2 field b false  
    | Comp (pkr1, pkr2) -> comp_bdd man pk1 pk2 compile_pkr_bdd pkr1 pkr2
    | OrP (pkr1,pkr2)-> MLBDD.dor (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
    | AndP (pkr1,pkr2)-> MLBDD.dand (compile_pkr_bdd_aux pkr1) (compile_pkr_bdd_aux pkr2)
    | Binary (pred1,pred2) -> MLBDD.dand (compile_pred_bdd man pk1 pred1) (compile_pred_bdd man pk2 pred2)
    | FMap (field1,field2) -> MLBDD.nxor (generate_single_var man pk1 field1) (generate_single_var man pk2 field2) 
    in compile_pkr_bdd_aux pkr

let rename_bdd  (pk1:pk) (pk2:pk) (bdd:MLBDD.t):MLBDD.t =
  let permute var = if var mod 6 = pk1 then
    var - pk1 + pk2 
  else if var mod 6 = pk2 then
    var - pk2 + pk1 
  else var
  in MLBDD.permutef permute bdd

(* pk1: x, pk2:x',*)
let comp_bdd_2 (man:man) (pk1:pk) (pk2:pk)  (bdd1:MLBDD.t) (bdd2:MLBDD.t):MLBDD.t =
  let pk3 = generate_unused_pk pk1 pk2 in
    let support = generate_support man pk3 in
    (* bdd1 now is pk1 pk3 *)
      let rename_bdd1 = rename_bdd pk3 pk2 bdd1 in
    (* bdd2 now is pk3 pk2 *)
        let rename_bdd2 = rename_bdd pk1 pk3 bdd2 in
          MLBDD.exists support (MLBDD.dand rename_bdd1 rename_bdd2)


(* pk1: x, pk2:x', pk3:y, pk4:y'*)
let comp_bdd_4 (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd1:MLBDD.t) (bdd2:MLBDD.t):MLBDD.t =
  let (pk5,pk6) = generate_unused_pk56 pk1 pk2 pk3 pk4 in
    let support = generate_double_support man pk5 pk6 in
    (* bdd1 now is pk1 pk5 pk3 pk6 *)
      let rename_bdd1 = rename_bdd pk5 pk2 (rename_bdd pk6 pk4 bdd1) in
    (* bdd2 now is pk5 pk2 pk6 pk4 *)
        let rename_bdd2 = rename_bdd pk1 pk5 (rename_bdd pk3 pk6 bdd2) in
          MLBDD.exists support (MLBDD.dand rename_bdd1 rename_bdd2)
  
(* A naive implementation, to be optimized*)    
let closure_bdd (man:man) (pk1:pk) (pk2:pk) (bdd: MLBDD.t) :MLBDD.t =
  (* input cur is of pk1 and pk2 *)
  let rec closure_bdd_aux (cur:MLBDD.t):MLBDD.t =
    let next = MLBDD.dor cur (comp_bdd_2 man pk1 pk2 cur bdd) in
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

        
let add_ro_mapping (con:Rel.t option) (bdd:MLBDD.t) (mapping:(MLBDD.t)ROMap.t):(MLBDD.t)ROMap.t=
    if MLBDD.is_false bdd then
          mapping
    else
      ROMap.update con (function
        | None -> Some bdd
        | Some bdd' -> Some (MLBDD.dor bdd bdd')) mapping


let add_nkro_mapping (con:NK.t option*Rel.t option) (bdd:MLBDD.t) (mapping:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
    if MLBDD.is_false bdd then
          mapping
    else
      NKROMap.update con (function
        | None -> Some bdd
        | Some bdd' -> Some (MLBDD.dor bdd bdd')) mapping

let add_nkrobs_mapping (con:NKROBSet.t) (bdd:MLBDD.t) (mapping:(MLBDD.t)NKROBSMap.t):(MLBDD.t)NKROBSMap.t=
    if MLBDD.is_false bdd then
          mapping
    else
      NKROBSMap.update con (function
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

let union_ro_mapping (mapping1:(MLBDD.t)ROMap.t) (mapping2:(MLBDD.t)ROMap.t):(MLBDD.t)ROMap.t=
   ROMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) mapping1 mapping2
   
let union_nkro_mapping (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):(MLBDD.t)NKROMap.t=
   NKROMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) mapping1 mapping2

let union_nkro_mapping_updated (mapping1:(MLBDD.t)NKROMap.t) (mapping2:(MLBDD.t)NKROMap.t):((MLBDD.t)NKROMap.t*bool)=
   NKROMap.fold (fun con bdd (mapping,changed) -> 
            match add_nkro_mapping_updated con bdd mapping with
              | (mapping',true) -> (mapping',true)
              | (mapping',false) -> (mapping',changed)
            ) mapping1 (mapping2,false)

let union_nkrob_mapping (mapping1:(MLBDD.t)NKROBMap.t) (mapping2:(MLBDD.t)NKROBMap.t):(MLBDD.t)NKROBMap.t=
   NKROBMap.union (fun _ bdd1 bdd2 -> Some (MLBDD.dor bdd1 bdd2)) mapping1 mapping2

let apply_nko_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
  NKOMap.filter_map (fun _ bdd-> let nbdd = tobdd bdd in 
                                    if (MLBDD.is_false nbdd) then
                                       None
                                    else Some nbdd) mapping

let apply_ro_mapping (tobdd:MLBDD.t->MLBDD.t) (mapping:(MLBDD.t)ROMap.t):(MLBDD.t)ROMap.t=
  ROMap.filter_map (fun _ bdd-> let nbdd = tobdd bdd in 
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

let concatenate_ro_mapping (mapping:(MLBDD.t)ROMap.t) (ro2:Rel.t option):(MLBDD.t)ROMap.t=
  ROMap.fold (fun ro1 bdd acc -> ROMap.add (match (ro1,ro2) with
                                                    | (None,_) -> ro2
                                                    | (_, None) -> ro1
                                                    | (Some r1,Some r2) -> Some (SeqR (r1,r2))
                                                   ) bdd acc) mapping ROMap.empty


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

let folding_epsilon_k (man:man) (nkom:(MLBDD.t)NKOMap.t):MLBDD.t =
  match (NKOMap.find_opt None nkom) with
    | None -> (bdd_false man)
    | Some bdd -> bdd

let filtering_epsilon_k (nkom:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t =
  NKOMap.remove None nkom

let folding_epsilon_r (man:man) (rom:(MLBDD.t)ROMap.t):MLBDD.t =
  match (ROMap.find_opt None rom) with
    | None -> (bdd_false man)
    | Some bdd -> bdd

let filtering_epsilon_r (rom:(MLBDD.t)ROMap.t):(MLBDD.t)ROMap.t =
  ROMap.remove None rom

let unionize_nko (nko1:NK.t option) (nko2:NK.t option):(NK.t option) =
  match (nko1,nko2) with
    | (None,_) | (_, None) -> raise (Invalid_argument "unionize_nko: one of the nko is None")
    | (Some (Union nks1), Some (Union nks2)) -> Some (Union (SNK.union nks1 nks2)) 
    | (Some (Union nks1), Some nk2) -> Some (Union (SNK.add nk2 nks1))
    | (Some nk1, Some (Union nks2)) -> Some (Union (SNK.add nk1 nks2))
    | (Some nk1, Some nk2) -> Some (Union (SNK.add nk1 (SNK.singleton nk2)))

let determinize_nko_transition (nexts:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
  let add_transition (nko:NK.t option) (bdd:MLBDD.t) (acc:(MLBDD.t)NKOMap.t):(MLBDD.t)NKOMap.t=
      if MLBDD.is_false bdd then
        acc
      else
        let new_bdd = NKOMap.fold (fun _ bddh acc -> MLBDD.dand (MLBDD.dnot bddh) acc) acc bdd in
        let next_map =
          NKOMap.fold (fun nko2 bddh acc -> 
            let ibdd = MLBDD.dand bdd bddh in
              let dbdd = MLBDD.dand (MLBDD.dnot bdd) bddh in
               add_nko_mapping nko2 dbdd (add_nko_mapping (unionize_nko nko2 nko) ibdd acc)) acc NKOMap.empty in
        add_nko_mapping nko new_bdd next_map
  in NKOMap.fold (fun nko bdd acc -> add_transition nko bdd acc) nexts NKOMap.empty
 

(* For simplicity, we combine the epsilon_k and delta_k in the paper into one function *)                            
(* Where for all nk_1,nk_2, delta_k (Some nk1) (Some nk2) is the delta_k in the paper *)                            
(* And for all nk, delta_k (Some nk) None is the epsilon_k in the paper *)                            
let rec delta_k (man:man)(pk1:pk)(pk2:pk)(nko:NK.t option): (MLBDD.t)NKOMap.t=
    match nko with
      | None -> NKOMap.empty
      | Some (Pred pred) -> add_nko_mapping None (MLBDD.dand (compile_pred_bdd man pk1 pred) (produce_id man pk1 pk2)) NKOMap.empty  
      | Some (Pkr pkr) -> add_nko_mapping None (compile_pkr_bdd man pk1 pk2 pkr) NKOMap.empty
      | Some (Asgn (field, b)) -> add_nko_mapping None (produce_assign man pk1 pk2 field b false) NKOMap.empty
      | Some (Union nks) -> SNK.fold (fun nk acc -> union_nko_mapping (delta_k man pk1 pk2 (Some nk)) acc) nks NKOMap.empty
      | Some (Seq(nk1,nk2)) -> let nko_map1 = delta_k man pk1 pk2 (Some nk1) in
                                  let nko_map2 = delta_k man pk1 pk2 (Some nk2) in
                                    union_nko_mapping (concatenate_nko_mapping (filtering_epsilon_k nko_map1) (Some nk2))
                                      (let epsilon = folding_epsilon_k man nko_map1 in
                                        apply_nko_mapping (comp_bdd_2 man pk1 pk2 epsilon) nko_map2)
      | Some (Inter(nk1,nk2)) -> let nko_map1 = delta_k man pk1 pk2 (Some nk1) in
                                   let nko_map2 = delta_k man pk1 pk2 (Some nk2) in
                                     NKOMap.fold (fun nko1 bdd1 acc -> NKOMap.fold 
                                      (fun nko2 bdd2 acc -> 
                                        match (nko1,nko2) with
                                          | (None,None) -> add_nko_mapping None (MLBDD.dand bdd1 bdd2) acc
                                          | (Some nk1,Some nk2) -> add_nko_mapping (Some (Inter (nk1,nk2))) (MLBDD.dand bdd1 bdd2) acc 
                                          | _ -> acc
                                        ) nko_map2 acc) nko_map1 NKOMap.empty                             
      | Some (Diff(nk1,nk2)) -> let nko_map1 = delta_k man pk1 pk2 (Some nk1) in
                                  let nko_map2 = delta_k man pk1 pk2 (Some nk2) in
                                    let epsilon_bdd = MLBDD.dand (folding_epsilon_k man nko_map1) (MLBDD.dnot (folding_epsilon_k man nko_map2)) in
                                      let coverage_bdd = NKOMap.fold (fun _ bdd acc -> MLBDD.dor bdd acc) (filtering_epsilon_k nko_map2) (bdd_false man) in   
                                        let nko_dmap2 = determinize_nko_transition (filtering_epsilon_k nko_map2) in
                                            NKOMap.fold (fun nko1 bdd1 acc -> NKOMap.fold 
                                            (fun nko2 bdd2 acc -> 
                                               match (nko1,nko2) with
                                                 | (Some nk1,Some nk2) -> add_nko_mapping (Some (Diff (nk1,nk2))) (MLBDD.dand bdd1 bdd2) acc 
                                                 | _ -> acc
                                              ) nko_dmap2 (add_nko_mapping nko1 (MLBDD.dand bdd1 (MLBDD.dnot coverage_bdd)) acc)) (filtering_epsilon_k nko_map1) (add_nko_mapping None epsilon_bdd NKOMap.empty)                            
      | Some (Star nk) -> let epsilon = closure_bdd man pk1 pk2 (folding_epsilon_k man (delta_k man pk1 pk2 (Some nk))) in                         
                                          apply_nko_mapping (comp_bdd_2 man pk1 pk2 epsilon) 
                                            (add_nko_mapping None (produce_id man pk1 pk2)
                                              (concatenate_nko_mapping (filtering_epsilon_k (delta_k man pk1 pk2 (Some nk))) (Some (Star nk)))) 
      | Some Dup -> add_nko_mapping (Some (Pred True)) (produce_id man pk1 pk2) NKOMap.empty
          
let right_nko_lifting (nko:NK.t option):(Rel.t option) =
  match nko with
    | None -> None
    | Some nk -> Some (Right nk)

let left_nko_lifting (nko:NK.t option):(Rel.t option) =
  match nko with
    | None -> None
    | Some nk -> Some (Left nk)

let id_nko_lifting (nko:NK.t option):(Rel.t option) =
  match nko with
    | None -> None
    | Some nk -> Some (Id nk)

let produce_double_id (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk):MLBDD.t =
  MLBDD.dand (produce_id man pk1 pk2) (produce_id man pk3 pk4)

let closure_bdd_r (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd:MLBDD.t):MLBDD.t =
  (* input cur is of pk1 and pk2 *)
  let rec closure_bdd_aux (cur:MLBDD.t):MLBDD.t =
      let next = MLBDD.dor cur (comp_bdd_4 man pk1 pk2 pk3 pk4 cur bdd) in
        if MLBDD.equal cur next then
          cur
        else 
          closure_bdd_aux next
  in closure_bdd_aux (produce_double_id man pk1 pk2 pk3 pk4) 	 

(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(* This is the tranisiton that indicate if the next step is of E/X/Y/XY *) 
(* Note that for E, we directly calculate the transitive closure of it *)                 
(* But for X/Y/XY, we calculate only one step *)                 
let rec delta_r (man:man)(pk1:pk)(pk2:pk)(pk3:pk)(pk4:pk)(ro:Rel.t option)(ns:next_step): (MLBDD.t)ROMap.t=
  let id1234 = produce_double_id man pk1 pk2 pk3 pk4 in
    match ro with
      | None -> (match ns with
                    | E -> add_ro_mapping ro id1234 ROMap.empty
                    | _ -> ROMap.empty)
      | Some (Nil pkr) ->  (match ns with
                            | E -> add_ro_mapping None (MLBDD.dand (compile_pkr_bdd man pk1 pk3 pkr) id1234) ROMap.empty
                            | _ -> ROMap.empty)
      | Some (Right nk) -> let id12 = produce_id man pk1 pk2 in
                            (match ns with
                              | Y -> NKOMap.fold (fun nko bdd acc -> add_ro_mapping (right_nko_lifting nko) (MLBDD.dand bdd id12) acc) (delta_k man pk3 pk4 (Some nk)) ROMap.empty
                              | E -> add_ro_mapping ro id1234 ROMap.empty
                              | _ -> ROMap.empty)
      | Some (Id nk) -> let id1324 = produce_double_id man pk1 pk3 pk2 pk4 in
                            (match ns with
                            | XY -> NKOMap.fold (fun nko bdd acc -> add_ro_mapping (id_nko_lifting nko) (MLBDD.dand bdd id1324) acc) (delta_k man pk3 pk4 (Some nk)) ROMap.empty
                            | E -> add_ro_mapping ro id1234 ROMap.empty
                            | _ ->  ROMap.empty)
      | Some (Left nk) -> let id34 = produce_id man pk3 pk4 in
                            (match ns with
                            | X -> NKOMap.fold (fun nko bdd acc -> add_ro_mapping (left_nko_lifting nko) (MLBDD.dand bdd id34) acc) (delta_k man pk1 pk2 (Some nk)) ROMap.empty
                            | E -> add_ro_mapping ro id1234 ROMap.empty
                            | _ -> ROMap.empty)
      | Some (Binary (nk1,nk2))-> delta_r man pk1 pk2 pk3 pk4 (Some (SeqR (Left nk1,Right nk2))) ns
      | Some (App (pkr1,pkr2)) -> delta_r man pk1 pk2 pk3 pk4 (Some (SeqR (Nil pkr1, SeqR (SeqR (Left (Pkr (Binary (True,True))), Right (Pkr (Binary (True,True)))), Nil pkr2)))) ns
      | Some (OrR rs) -> SR.fold (fun r acc -> union_ro_mapping (delta_r man pk1 pk2 pk3 pk4 (Some r) ns) acc) rs ROMap.empty                                       
      | Some (SeqR (r1,r2)) ->   let ro_map1 = delta_r man pk1 pk2 pk3 pk4 (Some r1) ns in
                                  (match ns with
                                    | E ->  let ro_map2 = delta_r man pk1 pk2 pk3 pk4 (Some r2) ns in
                                            union_ro_mapping (concatenate_ro_mapping (filtering_epsilon_r ro_map1) (Some r2))
                                              (apply_ro_mapping (comp_bdd_4 man pk1 pk2 pk3 pk4 (folding_epsilon_r man ro_map1)) ro_map2) 
                                    | _ ->  concatenate_ro_mapping ro_map1 (Some r2))
      | Some (StarR r) -> let ro_map = delta_r man pk1 pk2 pk3 pk4 (Some r) ns in
                          (match ns with
                            | E -> let epsilon = closure_bdd_r man pk1 pk2 pk3 pk4 (folding_epsilon_r man ro_map) in
                                     add_ro_mapping None epsilon (concatenate_ro_mapping 
                                     (apply_ro_mapping (comp_bdd_4 man pk1 pk2 pk3 pk4 epsilon) (filtering_epsilon_r ro_map)) (Some (StarR r)))
                            | _ ->  concatenate_ro_mapping ro_map (Some (StarR r)))
      | Some (IdComp (nko,r)) -> let ro_map = delta_r man pk1 pk2 pk3 pk4 (Some r) ns in
                                  (match ns with
                                    | Y 
                                    | E -> ROMap.fold (fun ro bdd acc -> match (nko,ro) with
                                        | (None,None) -> add_ro_mapping None bdd acc
                                        | (Some _ ,None) -> acc
                                        | (_, Some r) -> add_ro_mapping (Some (IdComp (nko,r))) bdd acc) ro_map ROMap.empty  
                                    | X
                                    | XY -> let nko_map = delta_k man pk1 pk2 nko in
                                        NKOMap.fold (fun nko bdd acc -> ROMap.fold (fun ro rbdd acc -> match (nko,ro) with
                                            | (None,None) -> add_ro_mapping None (MLBDD.dand bdd rbdd) acc
                                            | (Some _,None) -> acc
                                            | (_, Some r) -> add_ro_mapping (Some (IdComp (nko,r))) (MLBDD.dand bdd rbdd) acc) ro_map acc) nko_map ROMap.empty                                              
                                  )
                                                                      
                                              
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(* Correspond to delta_re1^* transistion in the paper *)
let delta_krx (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkro:(NK.t option*Rel.t option)):(MLBDD.t)NKROMap.t =
 let worklist = Queue.create() in
 let rec delta_krx_aux (cur:(MLBDD.t)NKROMap.t) :(MLBDD.t)NKROMap.t =
  match Queue.take_opt worklist with
    | None -> cur
    (* transition_bdd is in order of pk1 pk2 pk3 pk4*)
    | Some (nkro,transition_bdd) -> let (nko,ro) = nkro in 
                          let nko_map = delta_k man pk1 pk2 nko in
                          let ro_map = delta_r man pk1 pk2 pk3 pk4 ro X in
                          (* The right epsilon closure on the result *)
                          let epsilon_closure_ro_map_right = ROMap.fold (fun ro bdd acc -> union_ro_mapping (apply_ro_mapping
                             (comp_bdd_4 man pk1 pk2 pk3 pk4 bdd) (delta_r man pk1 pk2 pk3 pk4 ro E)) acc) ro_map ROMap.empty in
                              delta_krx_aux (NKOMap.fold (fun nko kbdd acc -> ROMap.fold (fun ro rbdd acc -> 
                                  let transition_bdd' = comp_bdd_4 man pk1 pk2 pk3 pk4 transition_bdd (MLBDD.dand kbdd rbdd)
                                    in match add_nkro_mapping_updated (nko,ro) transition_bdd' acc with
                                        | (mapping',true) -> Queue.add ((nko,ro),transition_bdd') worklist; mapping'
                                        | (mapping',false) -> mapping' ) epsilon_closure_ro_map_right acc) nko_map cur)
 in let (nko,ro) = nkro in
      let epsilon_closure_ro_map_left = delta_r man pk1 pk2 pk3 pk4 ro E in
        delta_krx_aux (ROMap.fold (fun ro bdd acc -> Queue.add ((nko,ro),bdd) worklist;
                        add_nkro_mapping (nko,ro) bdd acc) epsilon_closure_ro_map_left NKROMap.empty)
 
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(* Each computation starts from the epsilon closure of the the nkro, which means we first do the delta_re1^* transition, and then
  do the delta_re transition.
*)
let delta_kr (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkro:NK.t option*Rel.t option) (start_flag:bool): (MLBDD.t)NKROMap.t=
  let delta_kr_aux (nkro:NK.t option*Rel.t option) :(MLBDD.t)NKROMap.t =
    let (nko,ro)= nkro in
      let nko_map = delta_k man pk1 pk2 nko in
      let ro_y_map = delta_r man pk1 pk2 pk3 pk4 ro Y in
      let ro_xy_map = delta_r man pk1 pk2 pk3 pk4 ro XY in
        let next_y_map = ROMap.fold (fun ro rbdd acc -> add_nkro_mapping (nko,ro) rbdd acc) ro_y_map NKROMap.empty in
        let next_xy_map = NKOMap.fold (fun nko kbdd acc -> ROMap.fold (fun ro rbdd acc -> add_nkro_mapping (nko,ro) (MLBDD.dand kbdd rbdd) acc) ro_xy_map acc) nko_map NKROMap.empty in
        let next_map = union_nkro_mapping next_y_map next_xy_map in
            NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (comp_bdd_4 man pk1 pk2 pk3 pk4 bdd) (delta_krx man pk1 pk2 pk3 pk4 nkro)) acc) next_map NKROMap.empty
    in let start_closure =
        if start_flag then delta_krx man pk1 pk2 pk3 pk4 nkro
        else (add_nkro_mapping nkro (produce_double_id man pk1 pk2 pk3 pk4) NKROMap.empty) in
         NKROMap.fold (fun nkro bdd acc -> union_nkro_mapping (apply_nkro_mapping (comp_bdd_4 man pk1 pk2 pk3 pk4 bdd) (delta_kr_aux nkro)) acc) start_closure NKROMap.empty

(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(* The reachable set is the x y pair on each state, thus the pk1 pk3 pair on each state*)            
let calculate_reachable_set (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (start:NK.t option*Rel.t option):(MLBDD.t)NKROMap.t =
  let support13 = generate_double_support man pk1 pk3 in
  let worklist = Queue.create() in
      let rec calculate_reachable_set_aux (cur:(MLBDD.t)NKROMap.t): (MLBDD.t)NKROMap.t=
        match Queue.take_opt worklist with
          | None -> cur
          | Some (nkro,bdd) -> 
            calculate_reachable_set_aux (NKROMap.fold (fun nkro bdd acc-> match (add_nkro_mapping_updated nkro bdd acc) with
                                                | (next,true) -> Queue.add (nkro,bdd) worklist; next
                                                | (next,false) -> next) 
                                                (apply_nkro_mapping 
                  (fun nbdd -> (rename_bdd pk2 pk1 (rename_bdd pk4 pk3 (MLBDD.exists support13 (MLBDD.dand nbdd bdd)))))
                    (delta_kr man pk1 pk2 pk3 pk4 nkro (nkro_compare start nkro = 0))) cur)
     in Queue.add (start,(bdd_true man)) worklist;
       calculate_reachable_set_aux (add_nkro_mapping start (bdd_true man) NKROMap.empty) 
    
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
(*But should be re-ordered to 0:y, 1:x, 2:y', 3:x'*)
let re_ordering (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd:MLBDD.t):MLBDD.t=
let permute var = if var mod 6 = pk1 then
                      var - pk1 + 1
                    else if var mod 6 = pk2 then
                      var - pk2 + 3
                    else if var mod 6 = pk3 then
                      var - pk3 + 0
                    else if var mod 6 = pk4 then
                      var - pk4 + 2
                    else failwith "Unexpected variable"
                    in MLBDD.permutef permute bdd

let back_ordering (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (bdd:MLBDD.t):MLBDD.t=
  let permute var = if var mod 6 = 0 then
                      var - 0 + pk3
                    else if var mod 6 = 1 then
                      var - 1 + pk1
                    else if var mod 6 = 2 then
                      var - 2 + pk4
                    else if var mod 6 = 3 then
                      var - 3 + pk2
                    else failwith "Unexpected variable"
                    in MLBDD.permutef permute bdd

let var_low_branch (man:man) (var:int) (bdd:MLBDD.t):MLBDD.t=
 (MLBDD.dand (MLBDD.dnot (MLBDD.ithvar man.bman var)) bdd)

let var_high_branch (man:man) (var:int) (bdd:MLBDD.t):MLBDD.t=
 (MLBDD.dand (MLBDD.ithvar man.bman var) bdd)

let var_if (man:man) (var:int) (lbdd:MLBDD.t) (hbdd:MLBDD.t):MLBDD.t=
 (MLBDD.dor (var_low_branch man var lbdd) (var_high_branch man var hbdd))

let splitting_bdd (man:man)(pk1:pk)(pk2:pk)(pk3:pk)(pk4:pk) (bdd:MLBDD.t): BSet.t =
  (* Function used for folding *)
  let splitting_bdd_aux (b:MLBDD.t MLBDD.b): MLBDD.t =  
    match b with
      | MLBDD.BFalse -> bdd_false man
      | MLBDD.BTrue -> bdd_true man
      | MLBDD.BIf (low,var,high) -> if var mod 6 != 1 then
                                       var_if man var low high
                                    else if MLBDD.is_false low then
                                        var_high_branch man var high
                                    else var_low_branch man var low
     in 
  let rec loop (cur:BSet.t) (bdd:MLBDD.t):BSet.t = 
      if MLBDD.is_false bdd then cur
      else let low = MLBDD.foldb_cont man.split_hist splitting_bdd_aux bdd in
            loop (BSet.add low cur) (MLBDD.dand bdd (MLBDD.dnot low)) in
    BSet.map (fun bdd -> back_ordering pk1 pk2 pk3 pk4 bdd) (loop BSet.empty (re_ordering pk1 pk2 pk3 pk4 bdd))                         

let is_final_nkro (nkro:NK.t option*Rel.t option):bool =
  Option.is_none (fst nkro)&& Option.is_none (snd nkro)

let is_final_nkrob (nkrob:(NK.t option*Rel.t option)*MLBDD.t):bool =
  is_final_nkro (fst nkrob)
  
let is_final_nkrobs (nkrobs:NKROBSet.t):bool =
  NKROBSet.exists (fun nkrob -> is_final_nkrob nkrob) nkrobs

let nkr_to_nkro (nkr:NK.t*Rel.t):NK.t option*Rel.t option=
  (Some (fst nkr),Some (snd nkr))   
(* pk1: x, pk2:x', pk3:y, pk4:y'*)
let generate_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (start:NK.t option*Rel.t option):(BSet.t*(BSet.t)NKROMap.t)NKROMap.t=
  let support24 = generate_double_support man pk2 pk4 in
  NKROMap.mapi (fun nkro bdd -> let new_delta = NKROMap.map (fun bdd -> splitting_bdd man pk1 pk2 pk3 pk4 bdd) 
                                    (apply_nkro_mapping (fun tbdd -> (MLBDD.dand tbdd bdd)) (delta_kr man pk1 pk2 pk3 pk4 nkro (nkro_compare start nkro = 0))) in
                                  let hidden_state_set = 
                                        if is_final_nkro nkro 
                                          then BSet.singleton (bdd_true man)
                                        else (NKROMap.fold (fun _ bset acc -> BSet.union (BSet.map (fun bdd -> MLBDD.exists support24 bdd) bset) acc) new_delta BSet.empty) in
                                      (hidden_state_set,new_delta)) (calculate_reachable_set man pk1 pk2 pk3 pk4 start)

let find_bdds (nkro:NK.t option*Rel.t option)(transition:(BSet.t*(BSet.t)NKROMap.t)NKROMap.t):BSet.t=
  match NKROMap.find_opt nkro transition with
    | None -> failwith "Transition not found"
    | Some (bdds,_) -> bdds                           

let simplify_all_transition(man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk)(all_transition:(BSet.t*(BSet.t)NKROMap.t)NKROMap.t):((MLBDD.t)NKROBMap.t)NKROBMap.t=
  let support12 = generate_double_support man pk1 pk2 in
  let support24 = generate_double_support man pk2 pk4 in
    NKROMap.fold (fun nkro1 (_,nkrom) acc -> NKROMap.fold (fun nkro2 hbdds1 acc ->
                                        let hbdds2 = find_bdds nkro2 all_transition
                                          in BSet.fold (fun hbdd1 acc -> 
                                            BSet.fold (fun hbdd2 acc -> 
                                              let tbddf = MLBDD.dand hbdd1 (rename_bdd pk1 pk2 (rename_bdd pk3 pk4 hbdd2)) in
                                              if MLBDD.is_false tbddf then
                                                acc
                                              else
                                                let hbdd1 = (MLBDD.exists support24 hbdd1) in  
                                                NKROBMap.update (nkro1, hbdd1) 
                                                (fun mapo -> match mapo with
                                                  | None -> Some (NKROBMap.singleton (nkro2,hbdd2) (MLBDD.exists support12 tbddf))
                                                  | Some map -> Some (NKROBMap.add (nkro2,hbdd2) (MLBDD.exists support12 tbddf) map))
                                                 acc)
                                          hbdds2 acc) hbdds1 acc) nkrom acc) all_transition NKROBMap.empty
                                        
let is_final_state (nkrob:(NK.t option*Rel.t option)*MLBDD.t):bool =
  Option.is_none (fst (fst nkrob)) && Option.is_none (snd (fst nkrob))
 
let determinize_transition (nexts:(MLBDD.t)NKROBMap.t):(MLBDD.t)NKROBSMap.t=
    let add_transition (nkrob:(NK.t option*Rel.t option)*MLBDD.t) (bdd:MLBDD.t) (acc:(MLBDD.t)NKROBSMap.t):(MLBDD.t)NKROBSMap.t=
        if MLBDD.is_false bdd then
          acc
        else
          let new_bdd = NKROBSMap.fold (fun _ bddh acc -> MLBDD.dand (MLBDD.dnot bddh) acc) acc bdd in
          let next_map =
          NKROBSMap.fold (fun nkrobs bddh acc -> 
            let ibdd = MLBDD.dand bdd bddh in
            let dbdd = MLBDD.dand (MLBDD.dnot bdd) bddh in
             add_nkrobs_mapping (NKROBSet.add nkrob nkrobs) ibdd
              (add_nkrobs_mapping nkrobs dbdd acc)) acc NKROBSMap.empty in
                add_nkrobs_mapping (NKROBSet.singleton nkrob) new_bdd next_map
    in NKROBMap.fold (fun nkrob bdd acc -> add_transition nkrob bdd acc) nexts NKROBSMap.empty
    
let determinization (start:NK.t option*Rel.t option) (transition:((MLBDD.t)NKROBMap.t)NKROBMap.t):((MLBDD.t)NKROBSMap.t)NKROBSMap.t*NKROBSet.t=
   let worklist = Queue.create() in
     let set_of_start = NKROBMap.fold (fun nkrob _ acc -> if nkro_compare (fst nkrob) start = 0 then NKROBSet.add nkrob acc else acc) transition NKROBSet.empty in
       let rec determinization_aux (acc:((MLBDD.t)NKROBSMap.t)NKROBSMap.t):((MLBDD.t)NKROBSMap.t)NKROBSMap.t=
        match Queue.take_opt worklist with
          | None -> acc
          | Some nkrobs -> 
                    if NKROBSMap.mem nkrobs acc then
                      determinization_aux acc
                    else
                      let nexts = NKROBSet.fold (fun nkrob acc -> union_nkrob_mapping 
                      (* Merge the bdd when they reach the same destination *)
                      (match (NKROBMap.find_opt nkrob transition) with
                        | None -> NKROBMap.empty
                        | Some nexts -> nexts)
                      acc) nkrobs NKROBMap.empty in
                    let dnexts = determinize_transition nexts in
                    NKROBSMap.iter (fun nkrobs_next _ -> Queue.add nkrobs_next worklist) dnexts;
                    determinization_aux (NKROBSMap.add nkrobs dnexts acc)
       in Queue.add set_of_start worklist;
         (determinization_aux NKROBSMap.empty,set_of_start)      

let projection_compiler (man:man) (pk1:pk) (pk2:pk) (pk3:pk) (pk4:pk) (nkro:(NK.t option*Rel.t option)):((MLBDD.t)NKROBSMap.t)NKROBSMap.t*NKROBSet.t =
  determinization nkro (simplify_all_transition man pk1 pk2 pk3 pk4 (generate_all_transition man pk1 pk2 pk3 pk4 nkro))    

let bisim (man:man)(pk1:pk)(pk2:pk)(start1:NKROBSet.t)(start2:NKROBSet.t)(aut1:((MLBDD.t)NKROBSMap.t)NKROBSMap.t) (aut2:((MLBDD.t)NKROBSMap.t)NKROBSMap.t):bool =
  let worklist = Queue.create() in
  let support1 = generate_support man pk1 in
  let rec bisim_aux (donelist:(MLBDD.t)NKROBSSMap.t):bool =
    match Queue.take_opt worklist with
      | None -> true
      | Some ((nkros1,nkros2),bdd) -> let (newdonelist,bdd) = match NKROBSSMap.find_opt (nkros1,nkros2) donelist with 
                                  | None -> (NKROBSSMap.add (nkros1,nkros2) bdd donelist,bdd)
                                  | Some dbdd -> (NKROBSSMap.add (nkros1,nkros2) (MLBDD.dor bdd dbdd) donelist,(MLBDD.dand bdd (MLBDD.dnot dbdd))) in
                                if MLBDD.is_false bdd then
                                  bisim_aux newdonelist
                                else
                                  if is_final_nkrobs nkros1 <> is_final_nkrobs nkros2 then
                                    false
                                  else
                                    let next1 = 
                                      (match (NKROBSMap.find_opt nkros1 aut1) with
                                      | None -> NKROBSMap.empty
                                      | Some next1 -> next1) in   
                                    let next2 = 
                                      (match (NKROBSMap.find_opt nkros2 aut2) with
                                      | None -> NKROBSMap.empty
                                      | Some next2 -> next2) in
                                      NKROBSMap.iter (fun nkros1 bdd1 -> 
                                        NKROBSMap.iter (fun nkros2 bdd2 -> 
                                          Queue.add ((nkros1,nkros2),(rename_bdd pk2 pk1 (MLBDD.exists support1 (MLBDD.dand bdd (MLBDD.dand bdd1 bdd2))))) worklist) next2) next1;
                                          (let reachable_bdd = (NKROBSMap.fold (fun _ bdd2 acc -> MLBDD.dor acc bdd2) next2 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros1 bdd1 -> 
                                              Queue.add ((nkros1,NKROBSet.empty),(rename_bdd pk2 pk1 (MLBDD.exists support1 (MLBDD.dand bdd (MLBDD.dand bdd1 (MLBDD.dnot reachable_bdd)))))) worklist) next1);
                                          (let reachable_bdd = (NKROBSMap.fold (fun _ bdd1 acc -> MLBDD.dor acc bdd1) next1 (bdd_false man)) in
                                            NKROBSMap.iter (fun nkros2 bdd2 -> 
                                              Queue.add ((NKROBSet.empty,nkros2),(rename_bdd pk2 pk1 (MLBDD.exists support1 (MLBDD.dand bdd (MLBDD.dand (MLBDD.dnot reachable_bdd) bdd2))))) worklist) next2);    
                                          bisim_aux newdonelist
  in
   Queue.add ((start1,start2),bdd_true man) worklist;
     bisim_aux NKROBSSMap.empty 
  