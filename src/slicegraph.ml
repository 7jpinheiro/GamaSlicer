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
  | IfS (vcl1,vcl2) -> true
  | _ -> false

let isnotStart vcgen =
  match vcgen.stype with
  | StartS -> false
  | _ -> true

let isnotEnd vcgen =
  match vcgen.stype with
  | EndS -> false
  | _ -> true


let add_start_stmt g vertex start_stmt flag =
  match flag with
  | true -> 
    let edge2 = E.create (get_or_create start_stmt) 1 vertex in
    G.add_edge_e g edge2
  | false -> ()

let add_vertex_and_edges x g start_stmt end_stmt =
    let x_vertex = get_or_create x.statement in
    if (isCondtional x) then cond_vertex := x_vertex :: !cond_vertex;
    let stmt_succs = x.statement.succs in
    let stmt_preds = x.statement.preds in
    G.add_vertex g x_vertex;
    add_start_stmt g x_vertex start_stmt (is_empty stmt_preds);
    let succs_edges = 
                  List.map(
                           fun succ ->
                                     let succ_vertex = 
                                     begin
                                        if (isReturnStmt succ.skind) 
                                                       then get_or_create end_stmt
                                                       else get_or_create succ 
                                     end
                                     in 
                                     let edge = E.create x_vertex 1 succ_vertex in 
                                     edge
                         ) stmt_succs 
    in                  
    List.iter(fun edge -> G.add_edge_e g edge) succs_edges

let create_slice_graph start_stmt end_stmt vcgen_list =
  let g = G.create () in
  let l  = List.filter isnotStart vcgen_list in
  let fl = List.filter isnotEnd l in 
  G.add_vertex g (get_or_create start_stmt);
  G.add_vertex g (get_or_create end_stmt);
  List.iter(fun x -> add_vertex_and_edges x g start_stmt end_stmt) fl;
  g

let create_edges_prec g vertex slice_result end_stmt =
  let edges =  
     if (slice_result.stmt_2.sid <> !end_stmt_sid ) then
       List.fold_right
              ( 
                fun stmt acc -> let vertex_succ =
                                begin
                                    if (isReturnStmt stmt.skind) 
                                                       then get_or_create end_stmt
                                                       else get_or_create stmt 
                                end
                                in
                                (E.create vertex 1 vertex_succ) :: acc  
              ) slice_result.stmt_2.succs []             
    else 
       let end_vertex = get_or_create end_stmt in
       [E.create vertex 1 end_vertex]
in
List.iter(fun x -> G.add_edge_e g x) edges

let create_edges_post g vertex slice_result end_stmt =
  let edges =  
     if (slice_result.stmt_2.sid <> !end_stmt_sid ) then
          let vertex_succ = get_or_create slice_result.stmt_2 in 
          [E.create vertex 1 vertex_succ]        
    else 
       let end_vertex = get_or_create end_stmt in
       [E.create vertex 1 end_vertex]
in
List.iter(fun x -> G.add_edge_e g x) edges

let create_sliced_edge_post g slice_result start_stmt end_stmt =
  let vertex_list = 
    if (is_empty (slice_result.stmt_1.preds)) then
       [get_or_create start_stmt]
     else 
       (List.fold_right (fun x acc -> get_or_create x :: acc) slice_result.stmt_1.preds [])
  in
  List.iter (fun x -> create_edges_post g x slice_result end_stmt ) vertex_list   

let create_sliced_edge_prec g slice_result start_stmt end_stmt = 
 let vertex = get_or_create slice_result.stmt_1 in
 create_edges_prec g vertex slice_result end_stmt

let create_sliced_edge g slice_result start_stmt end_stmt =
  match slice_result.slicing_type with
  | Post_slicing -> create_sliced_edge_post g slice_result start_stmt end_stmt
  | Prec_slicing -> create_sliced_edge_prec g slice_result start_stmt end_stmt
  | Spec_slicing -> raise (Invalid_argument "Not yet implemented Spec_slicing in create_sliced_edge")

let add_sliced_edges start_stmt end_stmt slices_results g =
  let valid_results = List.filter (fun x -> (isValid x.prover_result)) slices_results in
  List.iter(fun x -> create_sliced_edge g x start_stmt end_stmt) valid_results;
  g

let rec build_path edges_list  =
  match edges_list with
  | [] -> []
  | [e] -> [(G.E.src e)]@[(G.E.dst e)]
  | x::tail -> (G.E.src x)::(build_path tail)   

let get_w elem b g = 
  match b with
  | [] -> 0 
  | x -> let v_b = List.map(fun x -> get_or_create x) b in
         let b_last_v = List.hd (List.rev v_b) in
         let (p,tw) = Dij.shortest_path g elem b_last_v in
         tw 

let get_fi_vertex b1 b2 =
  match b1,b2 with 
  |x,[] -> let last_stmt = List.hd (List.rev x) in 
           let fi = List.hd (last_stmt.succs) in
           get_or_create fi
  |x,y  -> let last_stmt = List.hd (List.rev x) in 
           let fi = List.hd (last_stmt.succs) in
           get_or_create fi
  |[],y -> let last_stmt = List.hd (List.rev y) in 
           let fi = List.hd (last_stmt.succs) in
           get_or_create fi
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

let slice g first_stmt last_stmt vcgen_list = 
  let first_vertex = get_or_create first_stmt in 
  let last_vertex = get_or_create last_stmt in
  List.iter(fun x -> add_conditional_edges g x ) !cond_vertex;
  Gs_options.Self.result "Calculating shortest slice path!";
  try
   let (p,tw) = Dij.shortest_path g first_vertex last_vertex in
   build_path p 
  with
  | Not_found -> Gs_options.Self.fatal "Shortest slice path not found!"






