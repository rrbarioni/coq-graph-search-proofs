(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export Peano_dec.

(* Por enquanto, tô só rascunhando aqui. *)

Inductive nat_pair : Type := | p : nat -> nat -> nat_pair.

Definition nat_in_pair (n : nat) (np : nat_pair) : Prop :=
  match np with p n1 n2 => n = n1 \/ n = n2 end.

Inductive Graph : list nat -> list nat_pair -> Prop :=
  | g_empty : Graph [] []
  | g_vertex :
      forall (vl : list nat) (el : list nat_pair) (g : Graph vl el) (v : nat),
      ~ In v vl -> Graph (v :: vl) el
  | g_edge :
      forall (vl : list nat) (el : list nat_pair) (g : Graph vl el)
             (v1 : nat) (v2 : nat) (e : nat_pair),
      nat_in_pair v1 e -> nat_in_pair v2 e -> ~ In e el -> Graph vl (e :: el).
