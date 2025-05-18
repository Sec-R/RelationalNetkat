open RN

module EdgesMap : Map.S with type key = string*string
module NodesMap : Map.S with type key = string
type header =
  | Loc
  | Ip


val edgesMap_to_string : (string*string)EdgesMap.t -> string
val nodesMap_to_string : int NodesMap.t -> string
val parse_edges_to_map : Yojson.Basic.t -> (string*string)EdgesMap.t
val parse_nodes_to_map : Yojson.Basic.t -> int NodesMap.t
val binary_to_pred: int -> int -> int -> int -> pred
val binary_to_pkr: int -> int -> int -> int -> pkr
val parse_location_to_pred : string -> int -> bool -> int NodesMap.t -> pred
val parse_location_to_pkr : string -> int -> bool -> int NodesMap.t -> pkr
val parse_ip_entry_string : string -> int * int
val parse_ip_string : string -> int
val match_ip_string : int -> int -> int -> bool
val length_of_int : int -> int
val header_placement: header -> int NodesMap.t -> int
val parse_local_routing_table : string -> Yojson.Basic.t list -> int NodesMap.t -> (string * string) EdgesMap.t -> pkr
val parse_global_routing_table : Yojson.Basic.t -> int NodesMap.t -> (string * string) EdgesMap.t -> pkr
val json_to_network : Yojson.Basic.t -> int NodesMap.t -> (string * string) EdgesMap.t -> bool -> (string list) -> (string list) -> NK.t
val network_compiler : Yojson.Basic.t -> Yojson.Basic.t -> bool -> (string list) -> (string list) -> NK.t