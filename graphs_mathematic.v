(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export Peano_dec.

(* Por enquanto, tô só rascunhando aqui. *)

Definition Vertex : Type := nat.
Definition Edge : Type := Vertex -> Vertex.

Inductive VertexList : list Vertex -> Prop :=
  | vl_empty : VertexList []
  | vl_insert :
      forall (vl : list Vertex) (v : Vertex),
      ~ In v vl -> VertexList (v :: vl).

Inductive EdgeList : list Edge -> Prop :=
  | el_empty : EdgeList []
  | el_insert :
      forall (el : list Edge) (e : Edge),
      ~ In e el -> EdgeList (e :: el).

Inductive Graph : list Vertex -> list Edge -> Prop :=
  | g_empty : Graph [] []
  | g_vertex :
      forall (vl : list Vertex) (el : list Edge) (g : Graph vl el) (v : Vertex),
      ~ In v vl -> Graph (v :: vl) el
  | g_edge :
      forall (vl : list Vertex) (el : list Edge) (g : Graph vl el) (e : Edge),
      ~ In e el -> Graph vl (e :: el).



Inductive Vertex : Type := v : nat -> Vertex.
Inductive Edge : Type := e : Vertex -> Vertex -> Edge.

Compute (v 3).
Compute (e (v 3) (v 2)).

Definition V_set := list Vertex.
Definition E_set := list Edge.

Inductive NeighborList : Vertex -> E_set -> Type :=
  | nl_empty : forall (v : Vertex), NeighborList v []
  | nl_add_e :
      forall (v : Vertex) (e : E_set)
        (nl : NeighborList v e) (x : Edge),
      ~ In x e -> NeighborList v (x :: e).

Compute (nl_empty (v 3)).
Compute (nl_add_e (nl_empty (v 3)) e (v 3) (v 2)).

Definition NL_set := list NeighborList.

Inductive Graph : Type :=
  | g_empty : Graph []
  | g_add_v : forall