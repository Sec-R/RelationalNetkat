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

type man = {
  field_max : field;
  bman : MLBDD.man;
  split_hist : MLBDD.t MLBDD.hist;
}

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
val comp_bdd : man -> pk -> pk -> (man -> pk -> pk -> 'a -> MLBDD.t) -> 'a -> 'a -> MLBDD.t
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
val union_nkro_mapping_updated : MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t -> MLBDD.t NKROMap.t * bool
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
val calculate_reachable_set : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> MLBDD.t NKROMap.t
val re_ordering : pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val back_ordering : pk -> pk -> pk -> pk -> MLBDD.t -> MLBDD.t
val var_low_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_high_branch : man -> int -> MLBDD.t -> MLBDD.t
val var_if : man -> int -> MLBDD.t -> MLBDD.t -> MLBDD.t
val splitting_bdd : man -> pk -> pk -> pk -> pk -> MLBDD.t -> BSet.t
val is_final_nkro : NK.t option * Rel.t option -> bool
val is_final_nkrob : (NK.t option * Rel.t option) * MLBDD.t -> bool
val is_final_nkrobs : NKROBSet.t -> bool
val nkr_to_nkro : NK.t * Rel.t -> NK.t option * Rel.t option
val generate_all_transition : man -> pk -> pk -> pk -> pk -> NK.t option * Rel.t option -> (BSet.t * BSet.t NKROMap.t) NKROMap.t
val find_bdds : NK.t option * Rel.t option -> (BSet.t * BSet.t NKROMap.t) NKROMap.t -> BSet.t
val simplify_all_transition : man -> pk -> pk -> pk -> pk -> (BSet.t * BSet.t NKROMap.t) NKROMap.t -> MLBDD.t NKROBMap.t NKROBMap.t
val is_final_state : (NK.t option * Rel.t option) * MLBDD.t -> bool
val determinize_transition : MLBDD.t NKROBMap.t -> MLBDD.t NKROBSMap.t
val determinization : NK.t option * Rel.t option -> MLBDD.t NKROBMap.t NKROBMap.t -> MLBDD.t NKROBSMap.t NKROBSMap.t * NKROBSet.t
val projection_compiler : man -> pk -> pk -> pk ->  pk -> (NK.t option * Rel.t option) -> MLBDD.t NKROBSMap.t NKROBSMap.t * NKROBSet.t
val bisim : man -> pk -> pk -> NKROBSet.t -> NKROBSet.t -> MLBDD.t NKROBSMap.t NKROBSMap.t -> MLBDD.t NKROBSMap.t NKROBSMap.t -> bool