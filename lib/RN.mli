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
  | Havoc
  | Test of field * bool
  | LeftAsgn of field * bool
  | RightAsgn of field * bool
  | Comp of pkr * pkr
  | OrP of pkr * pkr
  | AndP of pkr * pkr
  | NegP of pkr
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

  val compare : t -> t -> int
end
and SNK : Set.S with type elt = NK.t

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
    | Apply of pkr * NK.t
  val compare : t -> t -> int
end
and SR : Set.S with type elt = Rel.t

module NKOMap : Map.S with type key = NK.t option
module ROMap : Map.S with type key = Rel.t option
module BMap : Map.S with type key = MLBDD.t
module NKROMap : Map.S with type key = NK.t option * Rel.t option
module NKROBMap : Map.S with type key = (NK.t option * Rel.t option) * MLBDD.t
module BSet : Set.S with type elt = MLBDD.t
module NKROBSet : Set.S with type elt = (NK.t option * Rel.t option) * MLBDD.t
module NKROBSMap : Map.S with type key = NKROBSet.t
module NKROBSSMap : Map.S with type key = NKROBSet.t * NKROBSet.t

type man

val pred_to_string : pred -> string
val pkr_to_string : pkr -> string
val nk_to_string : NK.t -> string
val rel_to_string : Rel.t -> string
val nkro_to_string : NK.t option * Rel.t option -> string
val nko_map_to_string : MLBDD.t NKOMap.t -> string
val ro_map_to_string : MLBDD.t ROMap.t -> string
val bset_to_string : BSet.t -> string
val nkro_map_to_string : MLBDD.t NKROMap.t -> string
val nkrob_map_to_string : MLBDD.t NKROBMap.t -> string
val nkrobs_to_string : NKROBSet.t -> string
val nkrobs_map_to_string : MLBDD.t NKROBSMap.t -> string
val nkros_map_to_string : BSet.t NKROMap.t -> string
val transition_set_map_to_string : (BSet.t * BSet.t NKROMap.t) NKROMap.t -> string
val transition_map_to_string : MLBDD.t NKROBMap.t NKROBMap.t -> string
val determinized_transition_map_to_string : MLBDD.t NKROBSMap.t NKROBSMap.t -> string

val init_man : field -> int -> man
val bddvar : pk -> field -> int
val generate_single_var : man -> pk -> field -> MLBDD.t
val bdd_true : man -> MLBDD.t
val bdd_false : man -> MLBDD.t
val compile_pred_bdd : man -> pk -> pred -> MLBDD.t
val produce_id : man -> pk -> pk -> MLBDD.t
val produce_assign : man -> pk -> pk -> field -> bool -> bool -> MLBDD.t
val generate_unused_pk : pk -> pk -> pk
val generate_support : man -> pk -> MLBDD.support
val generate_double_support : man -> pk -> pk -> MLBDD.support
val compile_pkr_bdd : man -> pk -> pk -> pkr -> MLBDD.t
val rename_bdd : pk -> pk -> MLBDD.t -> MLBDD.t
val closure_bdd : man -> pk -> pk -> MLBDD.t -> MLBDD.t
val add_nko_mapping : NK.t option -> MLBDD.t -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val add_ro_mapping : Rel.t option -> MLBDD.t -> MLBDD.t ROMap.t -> MLBDD.t ROMap.t
val add_nkro_mapping : NK.t option * Rel.t option -> MLBDD.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val add_nkrobs_mapping : NKROBSet.t -> MLBDD.t -> MLBDD.t NKROBSMap.t -> MLBDD.t NKROBSMap.t
val add_nkro_mapping_updated : NK.t option * Rel.t option -> MLBDD.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t * bool
val union_nko_mapping : MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val union_ro_mapping : MLBDD.t ROMap.t -> MLBDD.t ROMap.t -> MLBDD.t ROMap.t
val union_nkro_mapping : MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val union_nkrob_mapping : MLBDD.t NKROBMap.t -> MLBDD.t NKROBMap.t -> MLBDD.t NKROBMap.t
val apply_nko_mapping : (MLBDD.t -> MLBDD.t) -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val apply_ro_mapping : (MLBDD.t -> MLBDD.t) -> MLBDD.t ROMap.t -> MLBDD.t ROMap.t
val apply_nkro_mapping : (MLBDD.t -> MLBDD.t) -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val concatenate_nko_mapping : MLBDD.t NKOMap.t -> NK.t option -> MLBDD.t NKOMap.t
val concatenate_ro_mapping : MLBDD.t ROMap.t -> Rel.t option -> MLBDD.t ROMap.t
val concatenate_nkro_mapping : MLBDD.t NKROMap.t -> NK.t option * Rel.t option -> MLBDD.t NKROMap.t
val folding_epsilon_k : man -> MLBDD.t NKOMap.t -> MLBDD.t
val filtering_epsilon_k : MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val folding_epsilon_r : man -> MLBDD.t ROMap.t -> MLBDD.t
val filtering_epsilon_r : MLBDD.t ROMap.t -> MLBDD.t ROMap.t
val unionize_nko : NK.t option -> NK.t option -> NK.t option
val determinize_nko_transition : MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val delta_k : man -> pk -> pk -> NK.t option -> MLBDD.t NKOMap.t
val delta_r : man -> pk -> pk -> pk -> pk -> Rel.t option -> next_step -> MLBDD.t ROMap.t
val delta_krx : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> MLBDD.t NKROMap.t
val delta_kr : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> bool -> MLBDD.t NKROMap.t
val calculate_reachable_set : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> bool -> MLBDD.t NKROMap.t
val re_ordering : pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val back_ordering : pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val var_low_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_high_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_if : man -> int -> MLBDD.t -> MLBDD.t -> MLBDD.t
val splitting_bdd : man -> pk -> pk -> pk -> pk -> MLBDD.t -> BSet.t
val is_final_nkro : NK.t option * Rel.t option -> bool
val is_final_nkrob : (NK.t option * Rel.t option) * MLBDD.t -> bool
val is_final_nkrobs : NKROBSet.t -> bool
val generate_all_transition : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> bool -> (BSet.t * BSet.t NKROMap.t) NKROMap.t
val find_bdds : NK.t option * Rel.t option -> (BSet.t * BSet.t NKROMap.t) NKROMap.t -> BSet.t
val simplify_all_transition : man -> pk -> pk -> pk -> pk -> (BSet.t * BSet.t NKROMap.t) NKROMap.t -> MLBDD.t NKROBMap.t NKROBMap.t
val is_final_state : (NK.t option * Rel.t option) * MLBDD.t -> bool
val determinize_transition : MLBDD.t NKROBMap.t -> MLBDD.t NKROBSMap.t
val determinization : NK.t option * Rel.t option -> MLBDD.t NKROBMap.t NKROBMap.t -> MLBDD.t NKROBSMap.t NKROBSMap.t * NKROBSet.t
val projection_compiler : man -> pk -> pk -> pk ->  pk -> (NK.t option * Rel.t option) -> bool -> MLBDD.t NKROBSMap.t NKROBSMap.t * NKROBSet.t
val bisim : man -> pk -> pk -> NKROBSet.t -> NKROBSet.t -> MLBDD.t NKROBSMap.t NKROBSMap.t -> MLBDD.t NKROBSMap.t NKROBSMap.t -> bool
