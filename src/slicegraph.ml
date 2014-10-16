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

let create_stmt_vertex stmt = add_vertex (G.V.create stmt)

let get_vertex key =
    Hashtbl.find vertex_hash key

let get_stmt_vertex x = (G.V.label x)

let cond_vertex = ref []

let get_or_create x = 
  try 
   let x_vertex = get_vertex x.sid in
   x_vertex
  with
  | Not_found -> create_stmt_vertex x

let isCondtional vcgen =
  match vcgen.stype with
  | SimpleS -> false
  | IfS (vcl1,vcl2) -> true
  | BlockS vclb -> false
  | LoopS vcll -> false

let add_vertex_and_edges x g =
    let x_vertex = get_or_create x.statement in
    if (isCondtional x) then cond_vertex := x_vertex :: !cond_vertex;
    let stmt_succs = x.statement.succs in
    let x_edges =  List.map (
                             fun succ -> 
                                        let succ_vertex = get_or_create succ in 
                                        let edge = E.create x_vertex 1 succ_vertex in 
                                        edge
                            ) stmt_succs in
    G.add_vertex g x_vertex;
    List.iter(fun edge -> G.add_edge_e g edge) x_edges

let create_slice_graph vcgen_list =
  let g = G.create () in
  List.iter(fun x -> add_vertex_and_edges x g) vcgen_list;
  g

let create_sliced_edge slice_result =
  let vertex_1 = get_vertex slice_result.stmt_1.sid in
  let vertex_2 = get_vertex slice_result.stmt_2.sid in 
  let edge = E.create vertex_1 1 vertex_2 in
  edge


let add_sliced_edges slices_results g =
  let valid_results = List.filter (fun x -> (isValid x.prover_result)) slices_results in
  List.iter(fun x -> G.add_edge_e g (create_sliced_edge x)) valid_results;
  g


let rec build_path edges_list  =
  match edges_list with
  | [] -> []
  | [e] -> [(G.E.src e)]@[(G.E.dst e)]
  | x::tail -> (G.E.src x)::(build_path tail)   



let get_w elem b g = 
  match b with
  | [] -> 0 
  | x -> let v_b = List.map(fun x -> get_vertex x.sid) b in
         let b_last_v = List.hd (List.rev v_b) in
         let (p,tw) = Dij.shortest_path g elem b_last_v in
         tw 

let get_fi_vertex b1 b2 =
  match b1,b2 with 
  |x,[] -> let last_stmt = List.hd (List.rev x) in 
           let fi = List.hd (last_stmt.succs) in
           get_vertex fi.sid
  |x,y  -> let last_stmt = List.hd (List.rev x) in 
           let fi = List.hd (last_stmt.succs) in
           get_vertex fi.sid
  |[],y -> let last_stmt = List.hd (List.rev y) in 
           let fi = List.hd (last_stmt.succs) in
           get_vertex fi.sid
  |[],[] -> raise (Invalid_argument "Empty if statement with no then or else ")


let add_conditional_edges g elem = 
  let stmt = get_stmt_vertex elem in
  begin
    match stmt.skind with
    | If (e,b1,b2,loc) -> let tw1 = get_w elem b1.bstmts g in
                          let tw2 = get_w elem b2.bstmts g in 
                          let total_w = 1 + tw1 + tw2 in
                          let fi = get_fi_vertex b1.bstmts b2.bstmts in 
                          let edge = E.create elem total_w fi in
                          G.add_edge_e g edge
    | _ -> raise (Invalid_argument "Vertex not a conditional vertex in cond_vertex_list")
  end

let slice g vcgen_list = 
  let first_stmt = (List.hd vcgen_list).statement in
  let last_stmt = (List.hd (List.rev vcgen_list)).statement in
  let first_vertex = get_vertex first_stmt.sid in 
  let last_vertex = get_vertex last_stmt.sid in
  List.iter(fun x -> add_conditional_edges g x ) !cond_vertex;
  let (p,tw) = Dij.shortest_path g first_vertex last_vertex in 
  build_path p 



