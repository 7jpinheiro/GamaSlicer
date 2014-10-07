open Cil_types
open Why3
open Towhy3
open Vcgen
open Provers
open Slicing
open Graph


module Node = struct
	type t = stmt
	let compare n1 n2 = compare n1.sid n2.sid
	let hash n = Hashtbl.hash n.sid
	let equal n1 n2 = n1.sid = n2.sid 
end

module Edge = struct
  type t = int
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = 1
end

module G = Graph.Imperative.Digraph.AbstractLabeled(Node)(Edge)
open G

module W = struct
  type label = G.E.label
  type t = int
  let weight x = x
  let zero = 0
  let add = (+)
  let compare = compare
end
module Dij = Path.Dijkstra(G)(W)

let create_stmt_vertex stmt = G.V.create stmt

let rec create_edges vertex_list =
  match vertex_list with
  |[] -> []
  |[q] -> []
  | x :: y :: tail -> let edge = E.create x 1 y in 
                      edge :: (create_edges tail) 

let createSliceGraph vcgen_list =
  let g = G.create () in
  let vertex_list = List.fold_right(fun x acc -> create_stmt_vertex x.statement :: acc ) vcgen_list [] in
  let edge_list = create_edges vertex_list in
  List.iter(fun vert -> G.add_vertex g vert) vertex_list;
  List.iter(fun edge -> G.add_edge_e g edge) edge_list;
  g




