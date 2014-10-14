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


let is_empty l =
  match l with
  |[] -> true
  |x::y -> false


let first_vertex = ref (G.V.create Cil.dummyStmt)

let last_vertex = ref (G.V.create Cil.dummyStmt)


let vertex_hash = Hashtbl.create 257

let getKey v =
  let stament = G.V.label v in
  let key = stament.sid in
  key

let add_vertex v =
  let key = getKey v in 
  Hashtbl.add vertex_hash key v;
  v

let get_vertex key =
  try
    Hashtbl.find vertex_hash key
  with Not_found ->
    Gs_options.Self.fatal "Vertex not found"

let create_stmt_vertex stmt = add_vertex (G.V.create stmt)

let rec create_edges v vertex_list =
  match vertex_list with
  |[] -> []
  | x :: tail -> let edge = E.create v 1 x in 
                      edge :: (create_edges x tail) 


let add_block g vcgen_list =
  match vcgen_list with
  | [] -> ([],[])
  | x  -> let vertex_list = List.fold_left(fun acc x -> create_stmt_vertex x.statement :: acc ) [] vcgen_list  in
          let edge_list = create_edges (List.hd vertex_list) (my_tail (vertex_list)) in
          List.iter(fun vert -> G.add_vertex g vert) vertex_list;
          List.iter(fun edge -> G.add_edge_e g edge) edge_list;
          (vertex_list,edge_list)


let add_complex_graph elem g =
  match elem.stype with
  | SimpleS -> ()
  | IfS (vcl1,vcl2) -> let b1 = add_block g vcl1 in
                       let b2 = add_block g vcl2 in
                       if(is_empty (fst b1)) then () else G.add_edge g (get_vertex elem.statement.sid) (List.hd (fst b1));
                       if(is_empty (fst b2)) then () else G.add_edge g (get_vertex elem.statement.sid) (List.hd (fst b2))
  | BlockS vclb ->     let b = add_block g vclb in
                       if(is_empty (fst b)) then () else G.add_edge g (get_vertex elem.statement.sid) (List.hd (fst b))
  | LoopS vcll ->      let bl = add_block g vcll in
                       if(is_empty (fst bl)) then () else G.add_edge g (get_vertex elem.statement.sid) (List.hd (fst bl))



let create_slice_graph vcgen_list =
  let g = G.create () in
  let b = add_block g vcgen_list in 
  (* G.add_edge g !first_vertex (List.hd vertex_list); *)
  List.iter(fun elem -> add_complex_graph elem g) vcgen_list;
  g

let create_sliced_edge slice_result =
  let vertex_1 = get_vertex slice_result.stmt_1.sid in
  let vertex_2 = get_vertex slice_result.stmt_2.sid in 
  let edge = E.create vertex_1 1 vertex_2 in
  edge


let add_sliced_edges slices_results g =
  let valid_results = List.filter (fun x -> (isValid x.prover_result)) slices_results in
(*  let valid_edges = List.map (fun x -> create_sliced_edge ) *)
  List.iter(fun x -> G.add_edge_e g (create_sliced_edge x)) valid_results;
  g


let rec build_path edges_list  =
  match edges_list with
  | [] -> []
  | [e] -> [(G.E.src e)]@[(G.E.dst e)]
  | x::tail -> (G.E.src x)::(build_path tail)   

let slice g vcgen_list = 
  let first_stmt = (List.hd vcgen_list).statement in
  let last_stmt = (List.hd (List.rev vcgen_list)).statement in
  let first_vertex = get_vertex first_stmt.sid in 
  let last_vertex = get_vertex last_stmt.sid in
  let (p,tw) = Dij.shortest_path g first_vertex last_vertex in 
  build_path p 



