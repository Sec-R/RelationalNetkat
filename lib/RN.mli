(* Types *)
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

(* Modules *)
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
and SNK : Set.S with type elt = NK.t

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
and SR : Set.S with type elt = Rel.t

module NKOMap : Map.S with type key = NK.t option
module BMap : Map.S with type key = MLBDD.t
module NKROMap : Map.S with type key = (NK.t option * Rel.t option)
module NKROBMap : Map.S with type key = ((NK.t option * Rel.t option) * MLBDD.t)
module BSet : Set.S with type elt = MLBDD.t
module NKROBSet : Set.S with type elt = ((NK.t option * Rel.t option) * MLBDD.t)
module NKROBSMap : Map.S with type key = NKROBSet.t * bool
module NKROBSSMap : Map.S with type key = (NKROBSet.t * bool) * (NKROBSet.t * bool)

type man = {
  field_max: field;
  bman: MLBDD.man;
}

val pred_to_string : pred -> string
val pkr_to_string : pkr -> string
val nk_to_string : NK.t -> string
val rel_to_string : Rel.t -> string
val nkro_to_string : (NK.t option * Rel.t option) -> string
val nko_map_to_string : MLBDD.t NKOMap.t -> string
val nkro_map_to_string : MLBDD.t NKROMap.t -> string
val nkrob_map_to_string : MLBDD.t NKROBMap.t -> string
val nkrobs_to_string : NKROBSet.t -> string
val nkrobs_map_to_string : MLBDD.t NKROBSMap.t -> string
val nkros_map_to_string : BSet.t NKROMap.t -> string
val transition_set_map_to_string : (BSet.t * (BSet.t) NKROMap.t) NKROMap.t -> string
val transition_map_to_string : MLBDD.t NKROBMap.t NKROBMap.t -> string
val determinized_transition_map_to_string : MLBDD.t NKROBSMap.t NKROBSMap.t -> string

val init_man : field -> int -> man
val bddvar : man -> pk -> field -> int
val generate_single_var : man -> pk -> field -> MLBDD.t
val bdd_true : man -> MLBDD.t
val bdd_false : man -> MLBDD.t
val compile_pred_bdd : man -> pk -> pred -> MLBDD.t
val produce_id : man -> pk -> pk -> MLBDD.t
val produce_assign : man -> pk -> pk -> field -> bool -> bool -> MLBDD.t
val generate_unused_pk : pk -> pk -> pk
val generate_support : man -> pk -> MLBDD.support
val generate_double_support : man -> pk -> pk -> MLBDD.support
val comp_bdd : man -> pk -> pk -> (man -> pk -> pk -> 'a -> MLBDD.t) -> 'a -> 'a -> MLBDD.t
val compile_pkr_bdd : man -> pk -> pk -> pkr -> MLBDD.t
val rename_bdd : pk -> pk -> MLBDD.t -> MLBDD.t
val closure_bdd : man -> pk -> pk -> (man -> pk -> pk -> 'a -> MLBDD.t) -> 'a -> MLBDD.t
val add_nko_mapping : NK.t option -> MLBDD.t -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val add_nkro_mapping : (NK.t option * Rel.t option) -> MLBDD.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val add_nkro_mapping_updated : (NK.t option * Rel.t option) -> MLBDD.t -> MLBDD.t NKROMap.t -> (MLBDD.t NKROMap.t * bool)
val union_nko_mapping : MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val union_nkro_mapping : MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val union_nkro_mapping_updated : MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t -> (MLBDD.t NKROMap.t * bool)
val apply_nko_mapping : (MLBDD.t -> MLBDD.t) -> MLBDD.t NKOMap.t -> MLBDD.t NKOMap.t
val apply_nkro_mapping : (MLBDD.t -> MLBDD.t) -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t
val concatenate_nko_mapping : MLBDD.t NKOMap.t -> NK.t option -> MLBDD.t NKOMap.t
val concatenate_nkro_mapping : MLBDD.t NKROMap.t -> (NK.t option * Rel.t option) -> MLBDD.t NKROMap.t
val folding_epsilon : man -> MLBDD.t NKOMap.t -> MLBDD.t
val delta_k : man -> pk -> pk -> NK.t option -> MLBDD.t NKOMap.t
val comp_nkro_map : man -> pk -> pk -> (man -> pk -> pk -> (NK.t option * Rel.t option) -> MLBDD.t NKROMap.t) -> NK.t option -> Rel.t -> Rel.t -> MLBDD.t NKROMap.t
val closure_nkro_map : man -> pk -> pk -> (man -> pk -> pk -> (NK.t option * Rel.t option) -> MLBDD.t NKROMap.t) -> NK.t option -> Rel.t -> MLBDD.t NKROMap.t
val epsilon_kr : man -> pk -> pk -> (NK.t option * Rel.t option) -> MLBDD.t NKROMap.t
val generate_unused_pk5 : pk -> pk -> pk -> pk -> pk
val delta_kr : man -> pk -> pk -> pk -> pk -> (NK.t option * Rel.t option) -> MLBDD.t NKROMap.t
val calculate_reachable_set : man -> pk -> pk -> pk -> pk -> (NK.t * Rel.t) -> MLBDD.t NKROMap.t
val re_ordering : man -> pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val back_ordering : man -> pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val var_low_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_high_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_if : man -> int -> MLBDD.t -> MLBDD.t -> MLBDD.t
val splitting_bdd : man -> pk -> pk -> pk -> pk -> MLBDD.t -> BSet.t
val generate_all_transition : man -> pk -> pk -> pk -> pk -> (NK.t * Rel.t) -> (BSet.t * (BSet.t) NKROMap.t) NKROMap.t
val find_bdds : (NK.t option * Rel.t option) -> (BSet.t * (BSet.t) NKROMap.t) NKROMap.t -> BSet.t
val simplify_all_transition : man -> pk -> pk -> pk -> pk -> (BSet.t * (BSet.t) NKROMap.t) NKROMap.t -> (MLBDD.t) NKROBMap.t NKROBMap.t
val is_final_state : (NK.t option * Rel.t option) * MLBDD.t -> bool
val determinize_transition : MLBDD.t NKROBMap.t -> MLBDD.t NKROBSMap.t
val generate_start : man -> pk -> pk -> (NK.t * Rel.t) -> NKROBSet.t * bool
val determinization : man -> pk -> pk -> (NKROBSet.t*bool) -> (MLBDD.t NKROBMap.t) NKROBMap.t -> (MLBDD.t NKROBSMap.t) NKROBSMap.t
val bisim : man -> pk -> pk -> (NKROBSet.t*bool) -> (NKROBSet.t*bool) -> (MLBDD.t NKROBSMap.t) NKROBSMap.t -> (MLBDD.t NKROBSMap.t) NKROBSMap.t -> bool