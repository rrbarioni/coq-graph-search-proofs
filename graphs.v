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
vertex_eq_bool:
  Identity for all Vertex 'v'.
*)
Lemma vertex_eq_bool :
  forall (v : Vertex),
  beq_vertex v v = true.
Proof. Admitted.

Lemma vertex_noteq_implies_bool :
  forall (v1 v2 : Vertex),
  v1 <> v2 -> beq_vertex v1 v2 = false.
Proof. Admitted.

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
  A AdjacencyList represents all the vertices
  (VertexList) that are pointed by an specific
  Vertex.
*)
Inductive AdjacencyList : Type :=
  al : Vertex -> VertexList -> AdjacencyList.

Compute (al (v 1) [v 3; v 5; v 10]).

(*
  Syntactic sugar for representing a
  NeighborsList.
*)
Notation "a -> [ b ; .. ; c ]" :=
  (al (v a) (cons (v b) .. (cons (v c) nil) ..))
  (at level 60, right associativity).
Notation "a -> [ ]" :=
  (al (v a) nil)
  (at level 60, right associativity).

(*
  A Graph is a list of AdjacencyList.
*)
Definition Graph := list AdjacencyList.

Compute ([1 -> [2; 3; 4]; 2 -> [1; 3; 5]]).

(*
get_vertex_list:
  Given an Graph 'g', returns a
  VertexList containing the Vertex of all
  AdjacencyList in 'g'.
*)
Fixpoint get_vertex_list
 (g : Graph)
 : VertexList :=
  match g with
  | [] => []
  | (al v' vl) :: gt =>
      v' :: get_vertex_list gt
  end.

Example get_vertex_list_test_1:
  get_vertex_list
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]]
    = [v 1; v 2].
Proof. simpl. reflexivity. Qed.

(*
get_adjacency_list:
  Given a Graph 'g' and a Vertex 'v',
  returns the AdjacencyList of 'v' in 'g'.
*)
Fixpoint get_adjacency_list
 (v : Vertex)
 (g : Graph)
 : VertexList :=
  match g with
  | [] => []
  | (al v' vl) :: gt =>
      if beq_vertex v v'
      then vl
      else get_adjacency_list v gt
  end.

Example get_adjacency_list_test_1:
  get_adjacency_list
    (v 2)
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]]
    = [v 1; v 3; v 5].
Proof. simpl. reflexivity. Qed.

(*
n_vertices:
  Given a Graph 'g', returns the
  number of vertices in 'g'.
*)
Fixpoint n_vertices
 (g : Graph)
 : nat :=
  length g.

Example n_vertices_test_1:
  n_vertices
   [1 -> [2; 3; 4]; 2 -> [1; 3; 5]] = 2.
Proof. simpl. reflexivity. Qed.

(*
n_vertices:
  Given a Graph 'g', returns the
  number of edges in 'g'.
*)
Fixpoint n_edges
 (g : Graph)
 : nat :=
  match g with
  | [] => 0
  | (al v' vl) :: gt =>
      (length vl) + (n_edges gt)
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
 (g : Graph)
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
          then dfs_stack g visited stack_pop calls'
          else dfs_stack g ([vertex] ++ visited)
            ((diff_vertex_lists (get_adjacency_list vertex g) visited) ++ stack_pop)
            calls'
      end
  end.

Fixpoint dfs
 (g : Graph)
 (start : Vertex)
 : VertexList :=
  if b_vl_contains_vertex start (get_vertex_list g)
  then dfs_stack g [] [start] ((n_vertices g) + (n_edges g))
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
 (g : Graph)
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
          then bfs_queue g visited queue_pop calls'
          else bfs_queue g ([vertex] ++ visited)
            (queue_pop ++ (diff_vertex_lists (get_adjacency_list vertex g) visited))
            calls'
      end
  end.

Fixpoint bfs
 (g : Graph)
 (start : Vertex)
 : VertexList :=
  if b_vl_contains_vertex start (get_vertex_list g)
  then bfs_queue g [] [start] ((n_vertices g) + (n_edges g))
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

Lemma dfs_stack_vl_with_v :
  forall (v : Vertex) (vl : VertexList),
  (dfs_stack [al v (v :: vl)] [v] (vl ++ []) (length vl + 0)) =
  (dfs_stack [al v vl] [v] (vl ++ []) (length vl + 0)).
Proof. Admitted.

Lemma bfs_queue_vl_with_v :
  forall (v : Vertex) (vl : VertexList),
  (bfs_queue [al v (v :: vl)] [v] (vl ++ []) (length vl + 0)) =
  (bfs_queue [al v vl] [v] (vl ++ []) (length vl + 0)).
Proof. Admitted.

Lemma redundant_prop :
  forall (a b : Prop),
  (a \/ b) = (a \/ a \/ b).
Proof. Admitted.

(*
dfs_one_v_same:
  For a Graph with only one Vertex 'v1'
  (and its connections), the 'dfs' result of this
  Graph (starting from 'v1') is a VertexList
  containing 'v1' and its Vertex connections.
*)
Lemma dfs_one_v_same :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  v1 = v2 -> In v3 (dfs [(al v1 vl)] v2) = In v3 (v1 :: vl).
Proof.
  intros.
  rewrite H.
  clear H.
  simpl.
  assert (H := vertex_eq_bool v2).
  rewrite H.
  induction vl.
  - simpl. reflexivity.
  - case (vertex_eq_dec a v2).
    + intros.
      rewrite H0.
      simpl.
      rewrite H.
      assert (H1 := (dfs_stack_vl_with_v v2 vl)).
      rewrite H1.
      rewrite IHvl.
      case (vertex_eq_dec v2 v3).
      * intros.
        assert (H4 := redundant_prop (v2 = v3) (In v3 vl)).
        apply H4.
      * intros.
        assert (H4 := redundant_prop (v2 = v3) (In v3 vl)).
        apply H4.
    + intros.
      simpl.
      assert (H1 := vertex_noteq_implies_bool a v2).
      rewrite H1.
Admitted.

(*
dfs_one_v_diff:
  For a Graph with only one Vertex 'v1'
  (and its connections), the 'dfs' result of this
  Graph (starting from a different Vertex
  'v2') is an empty VertexList.
*)
Lemma dfs_one_v_diff :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  ~ v1 = v2 -> In v3 (dfs [(al v1 vl)] v2) = False.
Proof. Admitted.

(*
bfs_one_v_same:
  For a Graph with only one Vertex 'v1'
  (and its connections), the 'bfs' result of this
  Graph (starting from 'v1') is a VertexList
  containing 'v1' and its Vertex connections.
*)
Lemma bfs_one_v_same :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  v1 = v2 -> In v3 (bfs [(al v1 vl)] v2) = In v3 (v1 :: vl).
Proof. Admitted.

(*
bfs_one_v_diff:
  For a Graph with only one Vertex 'v1'
  (and its connections), the 'bfs' result of this
  Graph (starting from a different Vertex
  'v2') is an empty VertexList.
*)
Lemma bfs_one_v_diff :
  forall (v1 v2 v3 : Vertex) (vl : VertexList),
  ~ v1 = v2 -> In v3 (bfs [(al v1 vl)] v2) = False.
Proof. Admitted.

(*
dfs_bfs_one_v_equal:
  For a Graph with only one AdjacencyList
  'al', the 'dfs' result of this Graph (
  starting from a Vertex 'v1') is the same as the
  'bfs' result of ths Graph (starting
  from a Vertex 'v1').
*)
Lemma dfs_bfs_one_v_equal :
  forall (al : AdjacencyList) (v1 v2 : Vertex),
  In v2 (dfs [al] v1) <-> In v2 (bfs [al] v1).
Proof.
  split.
  - intros.
    destruct al0.
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
  - intros.
    destruct al0.
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

Lemma dfs_extend :
  forall (g : Graph) (al : AdjacencyList) (v1 v2 : Vertex),
  In v2 (dfs [al] v1) \/ In v2 (dfs g v1) <-> In v2 (dfs (al :: g) v1).
Proof. Admitted.

Lemma bfs_extend :
  forall (g : Graph) (al : AdjacencyList) (v1 v2 : Vertex),
  In v2 (bfs [al] v1) \/ In v2 (bfs g v1) <-> In v2 (bfs (al :: g) v1).
Proof. Admitted.

(*
dfs_bfs_equal:
  For every Graph 'g' and Vertex 'v',
  the DFS of 'g' starting from 'v'
  returns the same list of Vertices from
  the BFS of 'g' starting from 'v'.
*)
Theorem dfs_bfs_equal :
  forall (g : Graph) (v1 v2 : Vertex),
  In v2 (dfs g v1) <-> In v2 (bfs g v1).
Proof.
  intros.
  split.
  - induction g.
    + intros.
      simpl in H.
      contradiction.
    + intros.
      apply (bfs_extend g a v1 v2).
      apply (dfs_extend g a v1 v2) in H.
      destruct H.
      * left.
        apply dfs_bfs_one_v_equal in H.
        assumption.
      * right.
        apply IHg in H.
        assumption.
  - induction g.
    + intros.
      simpl in H.
      contradiction.
    + intros.
      apply (dfs_extend g a v1 v2).
      apply (bfs_extend g a v1 v2) in H.
      destruct H.
      * left.
        apply dfs_bfs_one_v_equal in H.
        assumption.
      * right.
        apply IHg in H.
        assumption.
Qed.

End SEARCH.
