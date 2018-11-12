(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export Peano_dec.

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