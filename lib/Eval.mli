open RN

module EdgesMap : Map.S with type key = string*string
module NodesMap : Map.S with type key = string

val edgesMap_to_string : (string*string)EdgesMap.t -> string
val nodesMap_to_string : int NodesMap.t -> string
val parse_edges_to_map : Yojson.Basic.t -> (string*string)EdgesMap.t
val parse_nodes_to_map : Yojson.Basic.t -> int NodesMap.t
val binary_to_pred: int -> int -> int -> int -> pred
val binary_to_pkr: int -> int -> int -> int -> pkr
val parse_location_to_pred : string -> int -> bool -> int NodesMap.t -> pred
val parse_location_to_pkr : string -> int -> bool -> int NodesMap.t -> pkr
val parse_ip_string : string -> int * int
val length_of_int : int -> int
val parse_routing_table : Yojson.Basic.t -> int NodesMap.t -> (string * string) EdgesMap.t -> pkr
val compare_data : (string * Yojson.Basic.t) -> (string * Yojson.Basic.t) -> int
val json_to_network : Yojson.Basic.t -> int NodesMap.t -> (string * string) EdgesMap.t -> (string list) -> (string list) -> NK.t