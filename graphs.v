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
b_vertex_eq:
  For all Vertex 'v', it is always
  equal to itself.
*)
Lemma b_vertex_eq :
  forall (v : Vertex),
  beq_vertex v v = true.
Proof. Admitted.

Lemma vertex_noteq :
  forall (v1 v2 : Vertex),
  v1 <> v2 -> beq_vertex v1 v2 = false.
Proof. Admitted.

Lemma vertex_noteq_symmetry :
  forall (v1 v2 : Vertex),
  v1 <> v2 -> v2 <> v1.
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
dfs_add_al_val:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'dfs' of 'g' plus an
  AdjacencyList with Vertex 'v' and its
  adjacenct vertices in 'vl' (starting from
  Vertex 'val'), then 'v' is equal to 'val'
  or 'val' is found at the 'dfs' of 'g'
  (also starting from Vertex 'val').
*)
Lemma dfs_add_al_val :
  forall (g : Graph) (vl : VertexList) (v val : Vertex),
  well_formed g ->
  (In val (dfs ((al v vl) :: g) val) <->
  (v = val) \/ In val (dfs g val)).
Proof. Admitted.

(*
bfs_add_al_val:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'bfs' of 'g' plus an
  AdjacencyList with Vertex 'v' and its
  adjacenct vertices in 'vl' (starting from
  Vertex 'val'), then 'v' is equal to 'val'
  or 'val' is found at the 'bfs' of 'g'
  (also starting from Vertex 'val').
*)
Lemma bfs_add_al_val :
  forall (g : Graph) (vl : VertexList) (v val : Vertex),
  well_formed g ->
  (In val (bfs ((al v vl) :: g) val) <->
  (v = val) \/ In val (bfs g val)).
Proof. Admitted.

(*
dfs_stack_val:
  For all Vertex 'val', if it already
  exists inside VertexList 'visited', then
  'val' will continue existing inside
  'visited' while 'dfs_stack' is computed',
  once there are only insertions in
  'visited' inside 'dfs_stack' computation.
*)
Lemma dfs_stack_val :
  forall (g : Graph) (visited stack : VertexList) (calls : nat) (val : Vertex),
  In val visited -> In val (dfs_stack g visited stack calls).
Proof. Admitted.

(*
bfs_queue_val:
  For all Vertex 'val', if it already
  exists inside VertexList 'visited', then
  'val' will continue existing inside
  'visited' while 'bfs_queue' is computed',
  once there are only insertions in
  'visited' inside 'bfs_queue' computation.
*)
Lemma bfs_queue_val :
  forall (g : Graph) (visited queue : VertexList) (calls : nat) (val : Vertex),
  In val visited -> In val (bfs_queue g visited queue calls).
Proof. Admitted.

(*
dfs_val_al_val_true:
  Forall well formed Graph 'g' plus an
  AdjacencyList with Vertex 'val' and its
  adjacenct vertices in 'vl', 'val' is
  always found at the 'dfs' of 'g' with
  this AdjacencyList (once the 'dfs' would
  start from 'val' shortly).
*)
Lemma dfs_val_al_val_true :
  forall (g : Graph) (vl : VertexList) (val : Vertex),
  well_formed (al val vl :: g) ->
  In val (dfs (al val vl :: g) val).
Proof.
  intros.
  unfold dfs.
  simpl.
  rewrite (b_vertex_eq val).
  apply (
    dfs_stack_val
      (al val vl :: g)
      [val]
      (vl ++ [])
      (length g + (length vl + n_edges g))
      val
  ).
  simpl.
  left.
  reflexivity.
Qed.

(*
bfs_val_al_val_true:
  Forall well formed Graph 'g' plus an
  AdjacencyList with Vertex 'val' and its
  adjacenct vertices in 'vl', 'val' is
  always found at the 'bfs' of 'g' with
  this AdjacencyList (once the 'bfs' would
  start from 'val' shortly).
*)
Lemma bfs_val_al_val_true :
  forall (g : Graph) (vl : VertexList) (val : Vertex),
  well_formed (al val vl :: g) ->
  In val (bfs (al val vl :: g) val).
Proof.
  intros.
  unfold bfs.
  simpl.
  rewrite (b_vertex_eq val).
  apply (
    bfs_queue_val
      (al val vl :: g)
      [val]
      vl
      (length g + (length vl + n_edges g))
      val
  ).
  simpl.
  left.
  reflexivity.
Qed.

(*
dfs_extend_val_val:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'dfs' of 'g'
  (starting from 'val'), then 'val' is still
  found by the 'dfs' when we add a
  AdjacencyList into 'g'.
*)
Lemma dfs_extend_val_val :
  forall (g : Graph) (vl : VertexList) (v val : Vertex),
  well_formed g ->
  (In val (dfs g val) -> In val (dfs (al v vl :: g) val)).
Proof.
  intros.
  apply (dfs_add_al_val g vl v0 val).
  - assumption.
  - right.
    assumption.
Qed.
(*
bfs_extend_val_val:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'bfs' of 'g'
  (starting from the same Vertex 'val'),
  then 'val' is still found by the 'bfs'
  when we add a AdjacencyList into 'g'.
*)
Lemma bfs_extend_val_val :
  forall (g : Graph) (vl : VertexList) (v val : Vertex),
  well_formed g ->
  (In val (bfs g val) -> In val (bfs (al v vl :: g) val)).
Proof.
  intros.
  apply (bfs_add_al_val g vl v0 val).
  - assumption.
  - right.
    assumption.
Qed.

(*
dfs_bfs_equal_val_val:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'dfs' of 'g' (starting
  from the same Vertex 'val'), then 'val' is
  also found at the bfs of 'g' (also starting
  from Vertex 'val'), and vice versa.
*)
Lemma dfs_bfs_equal_val_val :
  forall (g : Graph) (val : Vertex),
  well_formed g ->
  (In val (dfs g val) <-> In val (bfs g val)).
Proof.
  intros.
  split.
  - intros.
    induction g.
    + simpl in H0.
      contradiction.
    + destruct a.
      assert (H1 := H).
      apply g_well_formed_add in H.
      assert (H2 := IHg H).
      clear IHg.
      apply dfs_add_al_val in H0.
      * destruct H0.
        {
          rewrite H0.
          rewrite H0 in H1.
          clear H0.
          apply bfs_val_al_val_true.
          assumption.
        }
        {
          assert (H3 := H2 H0).
          clear H2.
          apply bfs_extend_val_val.
          {
            assumption.
          }
          {
            assumption.
          }
        }
      * assumption.
  - intros.
    induction g.
    + simpl in H0.
      contradiction.
    + destruct a.
      assert (H1 := H).
      apply g_well_formed_add in H.
      assert (H2 := IHg H).
      clear IHg.
      apply bfs_add_al_val in H0.
      * destruct H0.
        {
          rewrite H0.
          rewrite H0 in H1.
          clear H0.
          apply dfs_val_al_val_true.
          assumption.
        }
        {
          assert (H3 := H2 H0).
          clear H2.
          apply dfs_extend_val_val.
          {
            assumption.
          }
          {
            assumption.
          }
        }
      * assumption.
Qed.

Lemma dfs_stack_not_started_from_al :
  forall (g : Graph) (stack : VertexList) (calls : nat) (vl : VertexList) (v0 v1 : Vertex),
  v1 <> v0 ->
  In v0 (dfs_stack (al v1 vl :: g) [v0] stack calls) ->
  In v0 (dfs g v0).
Proof. Admitted.

Lemma bfs_queue_not_started_from_al :
  forall (g : Graph) (queue : VertexList) (calls : nat) (vl : VertexList) (v0 v1 : Vertex),
  v1 <> v0 ->
  In v0 (bfs_queue (al v1 vl :: g) [v0] queue calls) ->
  In v0 (bfs g v0).
Proof. Admitted.

(*
dfs_v_in_g:
  For all well formed Graph 'g', if a Vertex
  'v' is found at the 'dfs' of 'g' (starting
  from the same Vertex 'v'), then 'v' belongs
  to the list of Vertices of 'g', and vice
  versa.
*)
Lemma dfs_v_in_g :
  forall (g : Graph) (v : Vertex),
  well_formed g ->
  (In v (dfs g v) -> In v (get_vertex_list g)).
Proof.
  intros.
  induction g.
  - simpl in H0.
    contradiction.
  - destruct a.
    assert (H1 := H).
    apply g_well_formed_add in H1.
    assert (IHg := IHg H1).
    case (vertex_eq_dec v1 v0).
    + intros.
      simpl.
      left.
      assumption.
    + intros.
      simpl.
      right.
      simpl in H0.
      rewrite vertex_noteq in H0.
      * induction b_vl_contains_vertex in H0.
        {
          assert (H3 :=
            dfs_stack_not_started_from_al
              g
              (get_adjacency_list v0 g ++ [])
              (length g + (length v2 + n_edges g))
              v2 v0 v1).
          assert (H4 := H3 H2 H0).
          assert (H5 := IHg H4).
          assumption.
        }
        {
          simpl in H0.
          contradiction.
        }
      * apply vertex_noteq_symmetry.
        assumption.
Qed.

(*
bfs_v_in_g:
  For all well formed Graph 'g', if a Vertex
  'v' is found at the 'bfs' of 'g' (starting
  from the same Vertex 'v'), then 'v' belongs
  to the list of Vertices of 'g', and vice
  versa.
*)
Lemma bfs_v_in_g :
  forall (g : Graph) (v : Vertex),
  well_formed g ->
  (In v (bfs g v) -> In v (get_vertex_list g)).
Proof.
  intros.
  induction g.
  - simpl in H0.
    contradiction.
  - destruct a.
    assert (H1 := H).
    apply g_well_formed_add in H1.
    assert (IHg := IHg H1).
    case (vertex_eq_dec v1 v0).
    + intros.
      simpl.
      left.
      assumption.
    + intros.
      simpl.
      right.
      simpl in H0.
      rewrite vertex_noteq in H0.
      * induction b_vl_contains_vertex in H0.
        {
          assert (H3 :=
            bfs_queue_not_started_from_al
              g
              (get_adjacency_list v0 g)
              (length g + (length v2 + n_edges g))
              v2 v0 v1).
          assert (H4 := H3 H2 H0).
          assert (H5 := IHg H4).
          assumption.
        }
        {
          simpl in H0.
          contradiction.
        }
      * apply vertex_noteq_symmetry.
        assumption.
Qed.

(*
g_not_contains_val:
  For all well formed Graph 'g' plus an
  AdjacencyList with Vertex 'val' and its
  adjacenct vertices in 'vl', Vertex 'v'
  does not belong to the list of Vertices
  of 'g'.
*)
Lemma g_not_contains_v :
  forall (g : Graph) (vl : VertexList) (v : Vertex),
  well_formed (al v vl :: g) -> ~ In v (get_vertex_list g).
Proof.
  intros.
  assert (H0 := H).
  apply g_well_formed_add in H0.
  unfold well_formed in H.
  unfold b_well_formed in H.
  destruct (b_vl_contains_repetition (get_vertex_list (al v0 vl :: g))).
  - contradiction.
  - destruct (b_vl_contains_repetition vl).
    + contradiction.
    + 
Admitted.

(*
dfs_transitivity:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'dfs' of 'g' (starting
  from a Vertex 'vg') and a Vertex 'vt' is
  found at the 'dfs' of 'g' plus an
  AdjacencyList with Vertex 'val' and its
  adjacenct vertices in 'vl' (starting from
  Vertex 'vl'), then Vertex 'vt' is found at
  the 'dfs' of 'g' plus an AdjacencyList with
  Vertex 'val' and its adjacenct vertices in
  'vl' (starting from Vertex 'vg'), and vice
  versa.
*)
Lemma dfs_transitivity :
  forall (g : Graph) (vl : VertexList) (vg val vt : Vertex),
  well_formed g ->
  (In val (dfs g vg) /\ In vt (dfs ((al val vl) :: g) val)  <->
  In vt (dfs ((al val vl) :: g) vg)).
Proof. Admitted.

(*
bfs_transitivity:
  For all well formed Graph 'g', if a Vertex
  'val' is found at the 'dfs' of 'g' (starting
  from a Vertex 'vg') and a Vertex 'vt' is
  found at the 'dfs' of 'g' plus an
  AdjacencyList with Vertex 'val' and its
  adjacenct vertices in 'vl' (starting from
  Vertex 'vl'), then Vertex 'vt' is found at
  the 'dfs' of 'g' plus an AdjacencyList with
  Vertex 'val' and its adjacenct vertices in
  'vl' (starting from Vertex 'vg'), and vice
  versa.
*)
Lemma bfs_transitivity :
  forall (g : Graph) (vl : VertexList) (vg val vt : Vertex),
  well_formed g ->
  (In val (bfs g vg) /\ In vt (bfs ((al val vl) :: g) val)  <->
  In vt (bfs ((al val vl) :: g) vg)).
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
  - induction g as [| al g].
    + intros.
      simpl in H.
      contradiction.
    + intros.
      destruct al as [val vl].
      apply (bfs_transitivity g vl vg val vt).
      * apply g_well_formed_add in wf.
        assumption.
      * apply (dfs_transitivity g vl vg val vt) in H.
        {
          destruct H.
          apply (dfs_transitivity g vl val val vt) in H0.
          {
            destruct H0.
            apply dfs_v_in_g in H0.
            {
              apply g_not_contains_v in wf.
              contradiction.
            }
            {
              apply g_well_formed_add in wf.
              assumption.
            }
          }
          {
            apply g_well_formed_add in wf.
            assumption.
          }
        }
        {
          apply g_well_formed_add in wf.
          assumption.
        }
  - induction g as [| al g].
    + intros.
      simpl in H.
      contradiction.
    + intros.
      destruct al as [val vl].
      apply (dfs_transitivity g vl vg val vt).
      * apply g_well_formed_add in wf.
        assumption.
      * apply (bfs_transitivity g vl vg val vt) in H.
        {
          destruct H.
          apply (bfs_transitivity g vl val val vt) in H0.
          {
            destruct H0.
            apply bfs_v_in_g in H0.
            {
              apply g_not_contains_v in wf.
              contradiction.
            }
            {
              apply g_well_formed_add in wf.
              assumption.
            }
          }
          {
            apply g_well_formed_add in wf.
            assumption.
          }
        }
        {
          apply g_well_formed_add in wf.
          assumption.
        }
Qed.

End SEARCH.
