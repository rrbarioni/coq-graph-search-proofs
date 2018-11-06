(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

Section SEARCH.

(* Vertex functions *)

(*
  A Vertex contains a natural value,
  representing which Vertex it is.
*)
Inductive Vertex : Type :=
  | v : nat -> Vertex.

Compute (v 3).

(*
beq_vertex:
  Given two Vertices 'a' and 'b',
  calculates if they have the same value.
*)
Fixpoint beq_vertex
 (a b : Vertex)
 : bool :=
  match a with v an =>
    match b with v bn => beq_nat an bn
    end
  end.

(* VertexList functions *)

(*
  A VertexList is a list of Vertices.
*)
Definition VertexList := list Vertex.

Compute ([v 3; v 5; v 10]).

(*
b_vl_contains_vertex:
  Given a Vertex 'v' and a VertexList 'vl',
  checks if 'vl' has a Vertex 'v'.
*)
Fixpoint b_vl_contains_vertex
 (v : Vertex)
 (vl : VertexList)
 : bool :=
  match vl with
  | [] => false
  | vh :: vt =>
    if beq_vertex v vh
    then true
    else b_vl_contains_vertex v vt
  end.

Example b_vl_contains_vertex_test_1:
  b_vl_contains_vertex (v 1) [v 2; v 3; v 4] = false.
Proof. simpl. reflexivity. Qed.
Example b_vl_contains_vertex_test_2:
  b_vl_contains_vertex (v 4) [v 2; v 3; v 4] = true.
Proof. simpl. reflexivity. Qed.

(*
vl_contains_vertex:
  Same as 'b_vl_contains_vertex', but
  returns a 'Prop'.
*)

Fixpoint vl_contains_vertex
 (v : Vertex)
 (vl : VertexList)
 : Prop :=
  if b_vl_contains_vertex v vl
  then True
  else False.

(*
remove_vertex:
  Given a Vertex 'v' and a VertexList 'vl',
  removes 'v' from 'vl', if 'v' exists in
  'vl'.
*)
Fixpoint remove_vertex
 (v : Vertex)
 (vl : VertexList)
 : VertexList :=
  match vl with
    | nil => nil
    | y :: tl =>
        if beq_vertex v y
        then remove_vertex v tl
        else y :: (remove_vertex v tl)
  end.

(*
diff_vertex_lists:
  Given two VertexList 'a' and 'b', removes
  all Vertices from 'a' which exists in 'b'.
*)
Fixpoint diff_vertex_lists
 (a b : VertexList)
 : VertexList :=
  match b with
  | [] => a
  | bh :: bt =>
      diff_vertex_lists (remove_vertex bh a) bt
  end.

Example diff_vertex_lists_test_1:
  diff_vertex_lists
    [v 2; v 3; v 1; v 1] [v 1; v 4]
    = [v 2; v 3].
Proof. simpl. reflexivity. Qed.

(*
sort_vertex_list:
  Given a VertexList 'vl', returns 'vl' with its
  values sorted.
*)

Fixpoint insert_sort_vertex_list
 (v' : Vertex)
 (vl : VertexList) :=
  match v' with v v'' =>
    match vl with
    | nil => (v v'') :: nil
    | (v vlh) :: vlt =>
        if v'' <=? vlh
        then (v v'')
          :: (v vlh) :: vlt
        else (v vlh)
          :: insert_sort_vertex_list (v v'') vlt
    end
  end.

Fixpoint sort_vertex_list
 (vl: VertexList)
 : VertexList :=
  match vl with
  | [] => []
  | vlh :: vlt =>
      insert_sort_vertex_list
        vlh (sort_vertex_list vlt)
  end.

Example sort_vertex_list_test_1:
  sort_vertex_list
    [v 3; v 5; v 1] = [v 1; v 3; v 5].
Proof. simpl. reflexivity. Qed.

(* NeighborsList functions *)

(*
  A NeighborsList represents all the vertices
  (VertexList) that are pointed by an specific
  Vertex.
*)
Inductive NeighborsList : Type :=
  | nl : Vertex -> VertexList -> NeighborsList.

Compute (nl (v 1) [v 3; v 5; v 10]).

(*
is_a_valid_nl:
  Given an NeighborList 'nl', tells if 'nl'
  is a valid NeighborList.
  What is a valid NeighborList?
  - It must not have duplicated Vertices.
*)(*
Fixpoint is_a_valid_nl
 (nl' : NeighborsList)
 : Prop :=
  match nl' with nl v' l' =>
    match l' with
    | [] => True
    | h' :: t' =>
        if b_vl_contains_vertex h' t'
        then False
        else is_a_valid_nl (nl v' t')
    end
  end.*)

(*
  Syntactic sugar for representing a
  NeighborsList.
*)
Notation "a -> [ b ; .. ; c ]" :=
  (nl (v a) (cons (v b) .. (cons (v c) nil) ..))
  (at level 60, right associativity).
Notation "a -> [ ]" :=
  (nl (v a) nil)
  (at level 60, right associativity).

(* AdjacencyList functions *)

(*
  An AdjacencyList is the representation of a
  graph; it is a list of NeighborsList.
*)
Definition AdjacencyList := list NeighborsList.

Compute ([1 -> [2; 3; 4]; 2 -> [1; 3; 5]]).

(*
is_a_valid_al:
  Given an AdjacencyList 'al', tells if 'al'
  is a valid graph.
  What is a valid graph?
  - All NeighborLists must not have
    duplicated Vertices;
  - If a Vertex 'v' appears in any NeighborList,
    then 'v' must has its own NeighborList in
    the AdjacencyList.
*)(*
Fixpoint is_a_valid_al
 (al : AdjacencyList)
 : Prop := *)

(*
get_neighbors_list:
  Given an AdjacencyList 'al' and a Vertex 'v',
  returns the NeighborList of 'v' in 'al'.
*)
Fixpoint get_neighbors_list
 (v : Vertex)
 (al : AdjacencyList)
 : VertexList :=
  match al with
  | [] => []
  | (nl v' l') :: alt =>
      if beq_vertex v v'
      then l'
      else get_neighbors_list v alt
  end.

Example get_neighbors_list_test_1:
  get_neighbors_list
    (v 2)
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]]
    = [v 1; v 3; v 5].
Proof. simpl. reflexivity. Qed.

(*
b_al_contains_vertex:
  Given a Vertex 'v' and an AdjacencyList
  'al', checks if 'al' has a Vertex 'v'.
*)

Fixpoint b_al_contains_vertex
 (v : Vertex)
 (al : AdjacencyList)
 : bool :=
  match al with
  | [] => false
  | (nl v' l') :: alt =>
      if beq_vertex v v'
      then true
      else b_al_contains_vertex v alt
  end.


(*
al_contains_vertex:
  Same as 'b_al_contains_vertex', but
  returns a 'Prop'.
*)

Fixpoint al_contains_vertex
 (v : Vertex)
 (al : AdjacencyList)
 : Prop :=
  if b_al_contains_vertex v al
  then True
  else False.

(*
n_vertices:
  Given an AdjacencyList 'al', returns the
  number of vertices in 'al'.
*)
Fixpoint n_vertices
 (al : AdjacencyList)
 : nat := length al.

Example n_vertices_test_1:
  n_vertices
   [1 -> [2; 3; 4]; 2 -> [1; 3; 5]] = 2.
Proof. simpl. reflexivity. Qed.

(*
n_vertices:
  Given an AdjacencyList 'al', returns the
  number of edges in 'al'.
*)
Fixpoint n_edges
 (al : AdjacencyList)
 : nat :=
  match al with
  | [] => 0
  | (nl v' l') :: alt =>
      (length l') + (n_edges alt)
  end.

Example n_edges_test_1:
  n_edges
   [1 -> [2; 3; 4]; 2 -> [1; 3; 5]] = 6.
Proof. simpl. reflexivity. Qed.

(*
DFS:
*)

(*
# DFS definition in python:
# https://eddmann.com/posts/depth-first-search-and-breadth-first-search-in-python/

def dfs(graph, start):
  visited, stack = set(), [start]
  while stack:
    vertex = stack.pop()
    if vertex not in visited:
      visited.add(vertex)
      stack.extend(
        graph[vertex] - visited
      )
  return visited
*)

Fixpoint dfs_stack
 (al : AdjacencyList)
 (visited stack : VertexList)
 (calls : nat)
 : VertexList :=
  match calls with
  | 0 => rev visited
  | S calls' =>
      match stack with
      | [] => rev visited
      | vertex :: stack_pop =>
          if b_vl_contains_vertex
            vertex visited
          then dfs_stack al
            visited stack_pop calls'
          else dfs_stack al
            ([vertex] ++ visited)
            ((diff_vertex_lists (get_neighbors_list vertex al) visited) ++ stack_pop)
            calls'
      end
  end.

Fixpoint dfs
 (al : AdjacencyList)
 (start : Vertex)
 : VertexList :=
  dfs_stack al [] [start]
    ((n_vertices al) + (n_edges al)).

Example dfs_test_1:
  dfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 2)
    = [v 2; v 0; v 1; v 3].
Proof. simpl. reflexivity. Qed.

(*
BFS:
*)

(*
# BFS definition in python:
# https://eddmann.com/posts/depth-first-search-and-breadth-first-search-in-python/

def bfs(graph, start):
  visited, queue = set(), [start]
  while queue:
    vertex = queue.pop(0)
    if vertex not in visited:
      visited.add(vertex)
      queue.extend(
        graph[vertex] - visited
      )
  return visited
*)

Fixpoint bfs_queue
 (al : AdjacencyList)
 (visited queue : VertexList)
 (calls : nat)
 : VertexList :=
  match calls with
  | 0 => rev visited
  | S calls' =>
      match queue with
      | [] => rev visited
      | vertex :: queue_pop =>
          if b_vl_contains_vertex
            vertex visited
          then bfs_queue al
            visited queue_pop calls'
          else bfs_queue al
            ([vertex] ++ visited)
            (queue_pop ++ (diff_vertex_lists (get_neighbors_list vertex al) visited))
            calls'
      end
  end.

Fixpoint bfs
 (al : AdjacencyList)
 (start : Vertex)
 : VertexList :=
  bfs_queue al [] [start]
    ((n_vertices al) + (n_edges al)).

Example bfs_test_1:
  bfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 2)
    = [v 2; v 0; v 3; v 1].
Proof. simpl. reflexivity. Qed.

(*
  If a Vertex does not belong to the graph,
  searches returns a list with only this
  Vertex.
*)
Example bfs_test_2:
  bfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 5)
    = [v 5].
Proof. simpl. reflexivity. Qed.

(*
DFS == BFS:
*)

(*
dfs_bfs_equal:
  For every Graph 'al' and Vertex 'v',
  the DFS of 'al' starting from 'v'
  returns the same list of Vertices from
  the BFS of 'al' starting from 'v'.
*)
Theorem dfs_bfs_equal :
  forall (al : AdjacencyList) (v : Vertex),
  sort_vertex_list (dfs al v) = sort_vertex_list (bfs al v).
Proof. Admitted.

End SEARCH.
