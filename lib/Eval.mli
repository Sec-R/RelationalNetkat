open RN

module DStringMap : Map.S with type key = string*string
module StringMap : Map.S with type key = string
type header =
  | Loc
  | SrcIp
  | DstIp
  | Protocol

type man = {
  nodes: int StringMap.t;
  edges: (string*string)DStringMap.t;
  protocols: int StringMap.t;
  interface: (pred*pred)DStringMap.t;
}

val insert_edge : (string * string) -> (string * string) -> (string * string) DStringMap.t -> (string * string) DStringMap.t
val insert_node : string -> int StringMap.t -> int StringMap.t
val insert_protocol : string -> int StringMap.t -> int StringMap.t

val edgesMap_to_string : (string * string) DStringMap.t -> string
val nodesMap_to_string : int StringMap.t -> string
val protocol_map_to_string : int StringMap.t -> string

val parse_edges_to_map : Yojson.Basic.t -> (string * string) DStringMap.t
val parse_nodes_to_map : Yojson.Basic.t -> int StringMap.t
val parse_protocols_to_map : Yojson.Basic.t -> int StringMap.t
val parse_interfaces_to_map : Yojson.Basic.t -> (string * string) DStringMap.t

val init_man : Yojson.Basic.t -> Yojson.Basic.t -> Yojson.Basic.t -> Yojson.Basic.t -> man
val get_field_length : man -> int

val binary_to_pred : int -> int -> int -> int -> pred
val binary_to_pkr : int -> int -> int -> int -> pkr
val length_of_int : int -> int

val header_placement : header -> man -> int
val parse_protocols_to_pred : string list -> man -> pred
val parse_location_to_pred : string -> int -> bool -> man -> pred
val parse_location_to_pkr : string -> int -> bool -> man -> pkr
val parse_ip_entry_string : string -> int * int
val parse_ip_string : string -> int
val find_next_loc : string -> string -> man -> string
val match_ip_string : int -> int -> int -> bool
val compare_data : Yojson.Basic.t -> Yojson.Basic.t -> int
val parse_ip_wildcard : string -> int * int
val parse_protocol_filter : string -> string -> Yojson.Basic.t -> int StringMap.t -> pred
val parse_local_routing_table : string -> Yojson.Basic.t list -> man -> pkr
val parse_global_routing_table : Yojson.Basic.t -> man -> pkr
val json_to_network : Yojson.Basic.t -> man -> bool -> string list -> string list -> NK.t