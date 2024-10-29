type field
type pk

type pred
type pkr 
type netkat
type rel


(* Function signatures *)
val pk_max : int
val bddvar : pk -> field -> int
val generate_single_var : MLBDD.man -> pk -> field -> MLBDD.t
val compile_pred_bdd : MLBDD.man -> pk -> pred -> MLBDD.t
val produce_id : MLBDD.man -> pk -> pk -> MLBDD.t
val produce_assign : MLBDD.man -> pk -> pk -> int -> bool -> bool -> MLBDD.t
val generate_unused_pk : pk -> pk -> pk
val generate_support : pk -> MLBDD.support
val comp_bdd : MLBDD.man -> pk -> pk -> (MLBDD.man -> pk -> pk -> 'a -> MLBDD.t) -> 'a -> 'a -> MLBDD.t
val compile_pkr_bdd : MLBDD.man -> pk -> pk -> pkr -> MLBDD.t
val closure_bdd : MLBDD.man -> pk -> pk -> (MLBDD.man -> pk -> pk -> 'a -> MLBDD.t) -> 'a -> MLBDD.t
val nk_included : netkat -> netkat -> bool
val canoicalize_nk : netkat -> netkat
val nk_equivalent : netkat -> netkat -> bool
val r_included : rel -> rel -> bool
val canoicalize_r : rel -> rel
val r_equivalent : rel -> rel -> bool
val nkr_equivalent : netkat * rel -> netkat * rel -> bool
val canoicalize_nkr : netkat * rel -> netkat * rel
val add_mapping : 'a -> MLBDD.t -> ('a -> 'a -> bool) -> ('a -> 'a) -> ('a * MLBDD.t) list -> ('a * MLBDD.t) list
val add_nk_mapping : netkat -> MLBDD.t -> (netkat * MLBDD.t) list -> (netkat * MLBDD.t) list
val add_nko_mapping : netkat option -> MLBDD.t -> (netkat option * MLBDD.t) list -> (netkat option * MLBDD.t) list
val add_r_mapping : rel -> MLBDD.t -> (rel * MLBDD.t) list -> (rel * MLBDD.t) list
val add_ro_mapping : rel option -> MLBDD.t -> (rel option * MLBDD.t) list -> (rel option * MLBDD.t) list
val add_nkro_mapping : (netkat * rel) option -> MLBDD.t -> ((netkat * rel) option * MLBDD.t) list -> ((netkat * rel) option * MLBDD.t) list
val union_mapping : ('a -> 'a -> bool) -> ('a -> 'a) -> ('a * MLBDD.t) list -> ('a * MLBDD.t) list -> ('a * MLBDD.t) list
val union_nk_mapping : (netkat * MLBDD.t) list -> (netkat * MLBDD.t) list -> (netkat * MLBDD.t) list
val union_nko_mapping : (netkat option * MLBDD.t) list -> (netkat option * MLBDD.t) list -> (netkat option * MLBDD.t) list
val union_r_mapping : (rel * MLBDD.t) list -> (rel * MLBDD.t) list -> (rel * MLBDD.t) list
val union_ro_mapping : (rel option * MLBDD.t) list -> (rel option * MLBDD.t) list -> (rel option * MLBDD.t) list
val union_nkro_mapping : ((netkat * rel) option * MLBDD.t) list -> ((netkat * rel) option * MLBDD.t) list -> ((netkat * rel) option * MLBDD.t) list
val canonicalize : ('a -> 'a -> bool) -> ('a -> 'a) -> ('a * MLBDD.t) list -> ('a * MLBDD.t) list
val canonicalize_nk_mapping : (netkat * MLBDD.t) list -> (netkat * MLBDD.t) list
val canonicalize_nko_mapping : (netkat option * MLBDD.t) list -> (netkat option * MLBDD.t) list
val canonicalize_r_mapping : (rel * MLBDD.t) list -> (rel * MLBDD.t) list
val canonicalize_ro_mapping : (rel option * MLBDD.t) list -> (rel option * MLBDD.t) list
val canonicalize_nkro_mapping : ((netkat * rel) option * MLBDD.t) list -> ((netkat * rel) option * MLBDD.t) list
val apply_mapping : (MLBDD.t -> MLBDD.t) -> ('a * MLBDD.t) list -> ('a * MLBDD.t) list
val concatenate_mapping : ('a * MLBDD.t) list -> ('a * 'a -> 'a) -> 'a -> ('a * MLBDD.t) list
val concatenate_nk_mapping : (netkat * MLBDD.t) list -> netkat -> (netkat * MLBDD.t) list
val concatenate_nko_mapping : (netkat option * MLBDD.t) list -> netkat option -> (netkat option * MLBDD.t) list
val concatenate_r_mapping : (rel * MLBDD.t) list -> rel -> (rel * MLBDD.t) list
val concatenate_ro_mapping : (rel option * MLBDD.t) list -> rel option -> (rel option * MLBDD.t) list
val concatenate_nkro_mapping : ((netkat * rel) option * MLBDD.t) list -> (netkat * rel) option -> ((netkat * rel) option * MLBDD.t) list
val folding_epsilon : MLBDD.man -> (netkat option * MLBDD.t) list -> MLBDD.t
val delta_k : MLBDD.man -> pk -> pk -> netkat option -> (netkat option * MLBDD.t) list
val empty_r : rel -> bool