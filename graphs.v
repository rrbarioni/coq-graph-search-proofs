(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.

Section SEARCH.

(*
Vertex:
  A Vertex contains a natural value,
  representing which Vertex it is.
*)
Inductive Vertex : Type :=
  v : nat -> Vertex.

Compute (v 3).

(*
vertex_eq_dec:
  Given two Vertices 'v1' and 'v2', they
  must have the same value or have
  different values.
*)
Lemma vertex_eq_dec :
  forall (v1 v2 : Vertex),
  v1 = v2 \/ v1 <> v2.
Proof.
  intros v1 v2.
  destruct v1 as [n1].
  destruct v2 as [n2].
  case (eq_nat_dec n1 n2).
  - intros H1. left.
    rewrite H1. reflexivity.
  - intros H1. right.
    injection as H2. contradiction.
Qed.

(*
beq_vertex:
  Given two Vertices 'a' and 'b',
  calculates if they have the same value.
*)
Fixpoint beq_vertex
 (v1 v2 : Vertex)
 : bool :=
  match v1 with v n1 =>
    match v2 with v n2 => beq_nat n1 n2
    end
  end.

(*
VertexList:
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
  | vlh :: vlt =>
    if beq_vertex v vlh
    then true
    else b_vl_contains_vertex v vlt
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
(*
Fixpoint vl_contains_vertex
 (v : Vertex)
 (vl : VertexList)
 : Prop :=
  if b_vl_contains_vertex v vl
  then True
  else False.
*)

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
  | [] => []
  | vlh :: vlt =>
      if beq_vertex v vlh
      then remove_vertex v vlt
      else vlh :: (remove_vertex v vlt)
  end.

(*
diff_vertex_lists:
  Given two VertexList 'a' and 'b', removes
  all Vertices from 'a' which exists in 'b'.
*)
Fixpoint diff_vertex_lists
 (vl1 vl2 : VertexList)
 : VertexList :=
  match vl2 with
  | [] => vl1
  | vl2h :: vl2t =>
      diff_vertex_lists
        (remove_vertex vl2h vl1) vl2t
  end.

Example diff_vertex_lists_test_1:
  diff_vertex_lists
    [v 2; v 3; v 1; v 1] [v 1; v 4]
    = [v 2; v 3].
Proof. simpl. reflexivity. Qed.

(*
  A NeighborsList represents all the vertices
  (VertexList) that are pointed by an specific
  Vertex.
*)
Inductive NeighborsList : Type :=
  nl : Vertex -> VertexList -> NeighborsList.

Compute (nl (v 1) [v 3; v 5; v 10]).

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

(*
  An AdjacencyList is the representation of a
  graph; it is a list of NeighborsList.
*)
Definition AdjacencyList := list NeighborsList.

Compute ([1 -> [2; 3; 4]; 2 -> [1; 3; 5]]).

(*
get_vertex_list:
  Given an AdjacencyList 'al', returns a
  VertexList containing the Vertex of all
  NeighborsList in 'al'.
*)
Fixpoint get_vertex_list
 (al : AdjacencyList)
 : VertexList :=
  match al with
  | [] => []
  | (nl v' vl) :: alt =>
      v' :: get_vertex_list alt
  end.

Example get_vertex_list_test_1:
  get_vertex_list
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]]
    = [v 1; v 2].
Proof. simpl. reflexivity. Qed.

(*
get_neighbors_list:
  Given an AdjacencyList 'al' and a Vertex 'v',
  returns the NeighborsList of 'v' in 'al'.
*)
Fixpoint get_neighbors_list
 (v : Vertex)
 (al : AdjacencyList)
 : VertexList :=
  match al with
  | [] => []
  | (nl v' vl) :: alt =>
      if beq_vertex v v'
      then vl
      else get_neighbors_list v alt
  end.

Example get_neighbors_list_test_1:
  get_neighbors_list
    (v 2)
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]]
    = [v 1; v 3; v 5].
Proof. simpl. reflexivity. Qed.

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
  | (nl v' vl) :: alt =>
      (length vl) + (n_edges alt)
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
          if b_vl_contains_vertex vertex visited
          then dfs_stack al visited stack_pop calls'
          else dfs_stack al ([vertex] ++ visited)
            ((diff_vertex_lists (get_neighbors_list vertex al) visited) ++ stack_pop)
            calls'
      end
  end.

Fixpoint dfs
 (al : AdjacencyList)
 (start : Vertex)
 : VertexList :=
  if b_vl_contains_vertex start (get_vertex_list al)
  then dfs_stack al [] [start] ((n_vertices al) + (n_edges al))
  else [].

Example dfs_test_1:
  dfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 2)
    = [v 2; v 0; v 1; v 3].
Proof. simpl. reflexivity. Qed.
Example dfs_test_2:
  dfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 6)
    = [].
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
          if b_vl_contains_vertex vertex visited
          then bfs_queue al visited queue_pop calls'
          else bfs_queue al ([vertex] ++ visited)
            (queue_pop ++ (diff_vertex_lists (get_neighbors_list vertex al) visited))
            calls'
      end
  end.

Fixpoint bfs
 (al : AdjacencyList)
 (start : Vertex)
 : VertexList :=
  if b_vl_contains_vertex start (get_vertex_list al)
  then bfs_queue al [] [start] ((n_vertices al) + (n_edges al))
  else [].

Example bfs_test_1:
  bfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 2)
    = [v 2; v 0; v 3; v 1].
Proof. simpl. reflexivity. Qed.
Example bfs_test_2:
  bfs
    ([0 -> [1; 2]; 1 -> [2]; 2 -> [0; 3]; 3 -> []]) (v 5)
    = [].
Proof. simpl. reflexivity. Qed.

Example bfs_test_3:
  bfs
    ([0 -> [1; 2]]) (v 0)
    = [v 0; v 1; v 2].
Proof. simpl. reflexivity. Qed.

(*
DFS = BFS:
*)

(*
dfs_one_v_same:
  For a AdjacencyList with only one Vertex 'v1'
  (and its connections), the 'dfs' result of this
  AdjacencyList (starting from 'v1') is a VertexList
  containing 'v1' and its Vertex connections.
*)
Lemma dfs_one_v_same :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  v1 = v2 -> In v3 (dfs [(nl v1 vl)] v2) = In v3 (v1 :: vl).
Proof. Admitted.

(*
dfs_one_v_diff:
  For a AdjacencyList with only one Vertex 'v1'
  (and its connections), the 'dfs' result of this
  AdjacencyList (starting from a different Vertex
  'v2') is an empty VertexList.
*)
Lemma dfs_one_v_diff :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  ~ v1 = v2 -> In v3 (dfs [(nl v1 vl)] v2) = False.
Proof. Admitted.

(*
bfs_one_v_same:
  For a AdjacencyList with only one Vertex 'v1'
  (and its connections), the 'bfs' result of this
  AdjacencyList (starting from 'v1') is a VertexList
  containing 'v1' and its Vertex connections.
*)
Lemma bfs_one_v_same :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  v1 = v2 -> In v3 (bfs [(nl v1 vl)] v2) = In v3 (v1 :: vl).
Proof. Admitted.

(*
bfs_one_v_diff:
  For a AdjacencyList with only one Vertex 'v1'
  (and its connections), the 'bfs' result of this
  AdjacencyList (starting from a different Vertex
  'v2') is an empty VertexList.
*)
Lemma bfs_one_v_diff :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  ~ v1 = v2 -> In v3 (bfs [(nl v1 vl)] v2) = False.
Proof. Admitted.

(*
dfs_bfs_equal_in_a_nl:
  For a AdjacencyList with only one NeighborsList
  'nl', the 'dfs' result of this AdjacencyList (
  starting from a Vertex 'v1') is the same as the
  'bfs' result of ths AdjacencyList (starting
  from a Vertex 'v1').
*)
Lemma dfs_bfs_one_v_equal :
  forall (nl : NeighborsList) (v1 v2 : Vertex),
  In v2 (dfs [nl] v1) <-> In v2 (bfs [nl] v1).
Proof.
  (* intros nl v1 v2. split.
  - intros H1. destruct nl as [v3 vl].
    case (vertex_eq_dec v1 v2).
    + intros H2.
      assert (H3 := H2).
      apply (bfs_one_v_same v2 v3 v1 vl) in H2.
      rewrite H2.
      apply (dfs_one_v_same v0 v1 v2 v3) in H1.
      rewrite H1 in H.
      assumption.
    + intros.
      apply (dfs_one_v_diff v0 v1 v2 v3) in H0.
      rewrite H0 in H.
      contradiction.
  - intros. destruct nl0.
    case (vertex_eq_dec v0 v1).
    + intros.
      assert (H1 := H0).
      apply (dfs_one_v_same v0 v1 v2 v3) in H0.
      rewrite H0.
      apply (bfs_one_v_same v0 v1 v2 v3) in H1.
      rewrite H1 in H.
      assumption.
    + intros.
      apply (bfs_one_v_diff v0 v1 v2 v3) in H0.
      rewrite H0 in H.
      contradiction. *)
  split.
  - intros. destruct nl0.
    case (vertex_eq_dec v0 v1).
    + intros.
      assert (H1 := H0).
      apply (bfs_one_v_same v0 v1 v2 v3) in H0.
      rewrite H0.
      apply (dfs_one_v_same v0 v1 v2 v3) in H1.
      rewrite H1 in H.
      assumption.
    + intros.
      apply (dfs_one_v_diff v0 v1 v2 v3) in H0.
      rewrite H0 in H.
      contradiction.
  - intros. destruct nl0.
    case (vertex_eq_dec v0 v1).
    + intros.
      assert (H1 := H0).
      apply (dfs_one_v_same v0 v1 v2 v3) in H0.
      rewrite H0.
      apply (bfs_one_v_same v0 v1 v2 v3) in H1.
      rewrite H1 in H.
      assumption.
    + intros.
      apply (bfs_one_v_diff v0 v1 v2 v3) in H0.
      rewrite H0 in H.
      contradiction.
Qed.

Lemma bfs_extend :
  forall (al : AdjacencyList) (nl : NeighborsList) (v1 v2 : Vertex),
  In v2 (bfs [nl] v1) \/ In v2 (bfs al v1) <-> In v2 (bfs (nl :: al) v1).
Proof. Admitted.

Lemma dfs_extend :
  forall (al : AdjacencyList) (nl : NeighborsList) (v1 v2 : Vertex),
  In v2 (dfs [nl] v1) \/ In v2 (dfs al v1) <-> In v2 (dfs (nl :: al) v1).
Proof. Admitted.

(*
dfs_bfs_equal:
  For every Graph 'al' and Vertex 'v',
  the DFS of 'al' starting from 'v'
  returns the same list of Vertices from
  the BFS of 'al' starting from 'v'.
*)
Theorem dfs_bfs_equal :
  forall (al : AdjacencyList) (v1 v2 : Vertex),
  In v2 (dfs al v1) <-> In v2 (bfs al v1).
Proof.
  intros. split.
  - induction al.
    + intros. simpl in H. contradiction.
    + intros. apply (bfs_extend al a v1 v2).
      apply (dfs_extend al a v1 v2) in H.
      destruct H.
      * left. apply dfs_bfs_one_v_equal in H. assumption.
      * right. apply IHal in H. assumption.
  - induction al.
    + intros. simpl in H. contradiction.
    + intros. apply (dfs_extend al a v1 v2).
      apply (bfs_extend al a v1 v2) in H.
      destruct H.
      * left. apply dfs_bfs_one_v_equal in H. assumption.
      * right. apply IHal in H. assumption.
Qed.

End SEARCH.
