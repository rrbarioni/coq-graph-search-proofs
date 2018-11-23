(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export Coq.Classes.RelationClasses.

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
b_vl_contains_repetition:
  Given a VertexList 'vl', checks if
  'vl' has a repeated Vertex.
*)
Fixpoint b_vl_contains_repetition
 (vl : VertexList)
 : bool :=
  match vl with
  | [] => false
  | v' :: vlt =>
      if b_vl_contains_vertex v' vlt
      then true
      else b_vl_contains_repetition vlt
  end.

Example b_vl_contains_repetition_test_1:
  b_vl_contains_repetition [v 1; v 3; v 5] = false.
Proof. simpl. reflexivity. Qed.
Example b_vl_contains_repetition_test_2:
  b_vl_contains_repetition [v 1; v 3; v 3] = true.
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
Notation Graph := (list AdjacencyList).

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
b_well_formed:
  Given a Graph 'g', checks if:
  - 'g' does not contain repeated
    Vertices in its Vertex list;
  - each AdjacencyList of 'g' does
    not contain repeated Vertices
    in its Vertex list.
*)
Fixpoint b_well_formed
 (g : Graph)
 : bool :=
  if b_vl_contains_repetition (get_vertex_list g)
  then false
  else
    match g with
    | [] => true
    | (al v' vl) :: gt =>
        if b_vl_contains_repetition vl
        then false
        else b_well_formed gt
  end.

Example b_well_formed_test_1:
  b_well_formed
    [1 -> [2; 3; 4]; 2 -> [1; 3; 5]] = true.
Proof. simpl. reflexivity. Qed.
Example b_well_formed_test_2:
  b_well_formed
    [1 -> [2; 3; 4]; 1 -> [1; 3; 5]] = false.
Proof. simpl. reflexivity. Qed.
Example b_well_formed_test_3:
  b_well_formed
    [1 -> [2; 3; 4]; 2 -> [1; 3; 3]] = false.
Proof. simpl. reflexivity. Qed.

(*
well_formed:
  Same as b_well_formed, but returns
  a Prop.
*)
Fixpoint well_formed
 (g : Graph)
 : Prop :=
  if b_well_formed g
  then True
  else False.

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

(*
vg: start vertex in g
val : start vertex in al
vt: target vertex
*)

(*
g_well_formed_add:
  For all Graph 'g', if 'g' plus an
  AdjacencyList with Vertex 'v' and
  its adjacenct vertices in 'vl' is
  a well formed Graph, then 'g' is
  also a well formed Graph.
*)
Lemma g_well_formed_add :
  forall (g : Graph) (vl : VertexList) (v : Vertex),
  well_formed ((al v vl) :: g) -> well_formed g.
Proof. Admitted.

Lemma dfs_extend :
  forall (g : Graph) (vl : VertexList) (v1 v2 v3 : Vertex),
  In v3 (dfs g v1) -> In v3 (dfs (al v2 vl :: g) v1).
Proof. Admitted.

Lemma bfs_extend :
  forall (g : Graph) (vl : VertexList) (v1 v2 v3 : Vertex),
  In v3 (bfs g v1) -> In v3 (bfs (al v2 vl :: g) v1).
Proof. Admitted.

Lemma dfs_al_has_v :
  forall (g : Graph) (vl : VertexList) (v : Vertex),
  well_formed (al v vl :: g) ->
  In v (dfs (al v vl :: g) v).
Proof. Admitted.

Lemma bfs_al_has_v :
  forall (g : Graph) (vl : VertexList) (v : Vertex),
  well_formed (al v vl :: g) ->
  In v (bfs (al v vl :: g) v).
Proof. Admitted.

Lemma dfs_diff_al_has_v2_from_v1 :
  forall (g : Graph) (vl : VertexList) (v1 v2 : Vertex),
  well_formed (al v2 vl :: g) ->
  (v1 <> v2 ->
  In v2 (dfs (al v2 vl :: g) v1) -> In v2 (dfs g v1)).
Proof. Admitted.

Lemma bfs_diff_al_has_v2_from_v1 :
  forall (g : Graph) (vl : VertexList) (v1 v2 : Vertex),
  well_formed (al v2 vl :: g) ->
  (v1 <> v2 ->
  In v2 (bfs (al v2 vl :: g) v1) -> In v2 (bfs g v1)).
Proof. Admitted.

Lemma dfs_diff_al_has_v2_from_v2 :
  forall (g : Graph) (vl : VertexList) (v1 v2 : Vertex),
  well_formed (al v1 vl :: g) ->
  (v1 <> v2 ->
  In v2 (dfs (al v1 vl :: g) v2) -> In v2 (dfs g v2)).
Proof. Admitted.

Lemma bfs_diff_al_has_v2_from_v2 :
  forall (g : Graph) (vl : VertexList) (v1 v2 : Vertex),
  well_formed (al v1 vl :: g) ->
  (v1 <> v2 ->
  In v2 (bfs (al v1 vl :: g) v2) -> In v2 (bfs g v2)).
Proof. Admitted.
 
Lemma dfs_bridge :
  forall (g : Graph) (vl : VertexList) (v1 v2 v3 : Vertex),
  well_formed ((al v2 vl) :: g) ->
  (v1 <> v3 -> v2 <> v3 ->
  In v3 (dfs (al v2 vl :: g) v1) -> In v3 (dfs g v1)).
Proof. Admitted.

Lemma bfs_bridge :
  forall (g : Graph) (vl : VertexList) (v1 v2 v3 : Vertex),
  well_formed ((al v2 vl) :: g) ->
  (v1 <> v3 -> v2 <> v3 ->
  In v3 (bfs (al v2 vl :: g) v1) -> In v3 (bfs g v1)).
Proof. Admitted.

(*
dfs_bfs_equal:
  For all well formed Graph 'g', if a Vertex
  'vt' is found at the 'dfs' of 'g' (starting
  from Vertex 'vg'), then 'vt' is also found
  at the bfs of 'g' (also starting from Vertex
  'vg'), and vice versa.
*)
Theorem dfs_bfs_equal :
  forall (g : Graph) (vg vt : Vertex),
  well_formed g -> (In vt (dfs g vg) <-> In vt (bfs g vg)).
Proof.
  intros g vg vt wf.
  split.
  - intros.
    induction g as [| al g].
    + simpl in H.
      contradiction.
    + destruct al as [val vl].
      assert (wf2 := wf).
      apply g_well_formed_add in wf2.
      assert (IHg := IHg wf2).
      destruct (vertex_eq_dec val vt).
      * rewrite H0.
        rewrite H0 in wf.
        rewrite H0 in H.
        destruct (vertex_eq_dec vg vt).
        {
          rewrite H1.
          assert (H2 := bfs_al_has_v g vl vt).
          assert (H2 := H2 wf).
          assumption.
        }
        {
          assert (H2 := dfs_diff_al_has_v2_from_v1 g vl vg vt).
          assert (H2 := H2 wf H1 H).
          assert (IHg := IHg H2).
          apply (bfs_extend g vl vg vt vt) in IHg.
          assumption.
        }
      * destruct (vertex_eq_dec vg vt).
        {
          rewrite H1.
          rewrite H1 in H.
          rewrite H1 in IHg.
          apply (dfs_diff_al_has_v2_from_v2 g vl val vt) in H.
          assert (IHg := IHg H).
          {
            apply (bfs_extend g vl vt val vt) in IHg.
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
        }
        {
          apply dfs_bridge in H.
          assert (IHg := IHg H).
          {
            apply (bfs_extend g vl vg val vt) in IHg.
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
        }
  - intros.
    induction g as [| al g].
    + simpl in H.
      contradiction.
    + destruct al as [val vl].
      assert (wf2 := wf).
      apply g_well_formed_add in wf2.
      assert (IHg := IHg wf2).
      destruct (vertex_eq_dec val vt).
      * rewrite H0.
        rewrite H0 in wf.
        rewrite H0 in H.
        destruct (vertex_eq_dec vg vt).
        {
          rewrite H1.
          assert (H2 := dfs_al_has_v g vl vt).
          assert (H2 := H2 wf).
          assumption.
        }
        {
          assert (H2 := bfs_diff_al_has_v2_from_v1 g vl vg vt).
          assert (H2 := H2 wf H1 H).
          assert (IHg := IHg H2).
          apply (dfs_extend g vl vg vt vt) in IHg.
          assumption.
        }
      * destruct (vertex_eq_dec vg vt).
        {
          rewrite H1.
          rewrite H1 in H.
          rewrite H1 in IHg.
          apply (bfs_diff_al_has_v2_from_v2 g vl val vt) in H.
          assert (IHg := IHg H).
          {
            apply (dfs_extend g vl vt val vt) in IHg.
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
        }
        {
          apply bfs_bridge in H.
          assert (IHg := IHg H).
          {
            apply (dfs_extend g vl vg val vt) in IHg.
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
          {
            assumption.
          }
        }
Qed.

End SEARCH.
