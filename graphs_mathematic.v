(* Dependencies *)
Require Export Coq.Bool.Bool.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.
Require Export Peano_dec.

(* Por enquanto, tô só rascunhando aqui. *)

Inductive Vertex : Type := v : nat -> Vertex.
Inductive Edge : Type := e : Vertex -> Vertex -> Edge.

Definition v_in_e (v : Vertex) (e : Edge) : Prop :=
  match e with e v1 v2 => v = v1 \/ v = v2 end.

Inductive Graph : list Vertex -> list Edge -> Prop :=
  | g_empty : Graph [] []
  | g_vertex :
      forall (vl : list Vertex) (el : list Edge) (g : Graph vl el) (v : Vertex),
      ~ In v vl -> Graph (v :: vl) el
  | g_edge :
      forall (vl : list Vertex) (el : list Edge) (g : Graph vl el)
             (v1 : Vertex) (v2 : Vertex) (e : Edge),
      v_in_e v1 e -> v_in_e v2 e -> ~ In e el -> Graph vl (e :: el).

Compute (Graph [v 3] [(e (v 3) (v 4)); (e (v 4) (v 2))]).

Inductive Adjacency : Type := a : Vertex -> list Edge -> Adjacency.

Inductive AdjacencyList : list Adjacency -> Prop :=
  | adjl_empty : AdjacencyList []
  | adjl_vertex :
      forall 

Fixpoint AdjacencyList_add_entry
 (al : list Adjacency) (v1 v2 : Vertex)
 : list Adjacency :=
  match al with
  | a 

Fixpoint AdjacencyList_aux
 (vl : list Vertex) (el : list Edge) (g : Graph vl el) (al : list Adjacency)
 : list Adjacency :=
  match g with
  | g_empty => al
  | g_vertex vl el g v => AdjacencyList_aux vl el g al
  | g_edge vl el g v1 v2 e => 


Fixpoint AdjacencyList
 (vl : list Vertex) (el : list Edge) (g : Graph vl el)
 : list Adjacency := AdjacencyList_aux vl el g [].

Inductive DFS : 
