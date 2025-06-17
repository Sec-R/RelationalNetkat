open RN

module DStringMap : Map.S with type key = string*string
module StringMap : Map.S with type key = string
module StringSet : Set.S with type elt = string

type header =
  | Loc
  | Vrf
  | Protocol
  | SrcIp
  | SrcPorts
  | DstIp
  | DstPorts

type man = {
  nodes: int StringMap.t;
  edges: (string*string)DStringMap.t;
  protocols: int StringMap.t;
  interface: (pred*pred)DStringMap.t;
  vrf: (int StringMap.t) StringMap.t;
  interface_to_vrf: int DStringMap.t;
  nodes_length: int;
  vrf_length: int;
  protocols_length: int;
  length: int;
}

val insert_edge : (string * string) -> (string * string) -> (string * string) DStringMap.t -> (string * string) DStringMap.t
val insert_node : string -> int StringMap.t -> int StringMap.t
val insert_protocol : string -> int StringMap.t -> int StringMap.t

val edgesMap_to_string : (string * string) DStringMap.t -> string
val nodesMap_to_string : int StringMap.t -> string
val protocol_map_to_string : int StringMap.t -> string
val vrf_map_to_string : (int StringMap.t) StringMap.t -> string
val interfaces_to_vrf_to_string : int DStringMap.t -> string

val parse_edges_to_map : Yojson.Basic.t -> (string * string) DStringMap.t
val parse_nodes_to_map : Yojson.Basic.t -> int StringMap.t
val parse_protocols_to_map : Yojson.Basic.t -> int StringMap.t
val parse_interfaces_to_map : Yojson.Basic.t -> (string * string) DStringMap.t
val parse_vrf_to_map : Yojson.Basic.t -> (int StringMap.t) StringMap.t

val init_man : Yojson.Basic.t -> Yojson.Basic.t -> Yojson.Basic.t -> Yojson.Basic.t -> man
val get_field_length : man -> int

val binary_to_pred : int -> int -> int -> int -> pred
val binary_to_pkr : int -> int -> int -> int -> pkr
val length_of_int : int -> int

val get_ge_pred : int -> int -> int -> pred
val get_le_pred : int -> int -> int -> pred

val header_placement : header -> man -> int
val parse_protocols_to_pred : string list -> man -> pred
val parse_location_to_pred : string -> bool -> man -> pred
val parse_location_to_pkr : string -> bool -> man -> pkr
val parse_vrf_to_pred : int -> man -> pred
val parse_vrf_to_pkr : int -> man -> pkr
val parse_ip_entry_string : string -> int * int
val parse_ip_string : string -> int
val find_next_loc : string -> string -> man -> string
val match_ip_string : int -> int -> int -> bool
val compare_data : Yojson.Basic.t -> Yojson.Basic.t -> int
val parse_ip_wildcard : string -> int * int
val parse_protocol_filter : string -> string -> Yojson.Basic.t -> int StringMap.t -> int -> int StringMap.t -> pred
val parse_local_routing_table : string -> Yojson.Basic.t list -> man -> pkr
val parse_global_routing_table : Yojson.Basic.t -> man -> pkr
val json_to_network : Yojson.Basic.t -> man -> bool -> string list -> string list -> NK.t
val find_next_loc_filter: string -> string -> man -> pred
val string_of_ip : int -> string

val parse_start_loc_to_pred : man -> string list -> pred
val parse_end_loc_to_pred : man -> string list -> pred
val parse_tcp_filter: string -> man -> pred
val parse_src_ip_filter: string -> man -> pred
val parse_dst_ip_filter: string -> man -> pred
val parse_dstports_filter: int -> bool -> man -> pred

val parse_rela_nodes: Yojson.Basic.t -> int StringMap.t
val init_rela_man: Yojson.Basic.t -> man
val rela_header_placement : header -> man -> int
val parse_rela_location_to_pred : string -> man -> pred
val parse_rela_location_to_pkr : string -> man -> pkr
val parse_rela_local_routing_table : Yojson.Basic.t -> man -> pkr * pkr
val parse_rela_global_routing_table : Yojson.Basic.t -> man -> pkr * pkr
val parse_rela_src_ip_filter : string -> man -> pred
val parse_rela_dst_ip_filter : string -> man -> pred
val rela_to_network : Yojson.Basic.t -> man -> NK.t * NK.t

val parse_rela_local_k_automata: Yojson.Basic.t -> man -> (pkr NKOMap.t NKOMap.t) * (pkr NKOMap.t NKOMap.t)
val parse_rela_global_k_automata: Yojson.Basic.t -> man -> (pkr NKOMap.t NKOMap.t) * (pkr NKOMap.t NKOMap.t)
val generate_start_nk: man -> NK.t option