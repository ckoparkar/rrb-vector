(* An implementation of vectors backed by a Radix-Balanced Tree. *)

Require Import Nat.
Require Import List.
Import ListNotations.
From Coq Require Import Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Wf.
From Coq Require Import Bool.Bool.

From RRB Require Import Prelude.
From RRB Require Import Crush.


(* -------------------------------------------------------------------------- *)

(* Branching factor *)
Definition M := 4.

Definition log2M := log2 M.

Definition mask := M - 1.

(* Useful type synonyms *)
Definition height := nat.
Definition size := nat.

(* The main datatype.
   Invariant: only rightmost node is allowed to be partially full. *)
Inductive tree {A : Type} : Type :=
| E    : tree
| Leaf : list size -> list A -> tree
| Node : height -> list size -> list tree -> tree.

(* The type exported out of this module *)
Definition vector1 {A : Type} := tree (A := A).

(* Upper bound on the #elems in a tree of height h *)
Definition vec_capacity {A : Type} (ht : height) : nat := M ^ (ht + 1).

Definition get_height {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | E           => 0
  | Leaf _ _    => 0
  | Node ht _ _ => ht
  end.

Axiom leaf_elems_M :
  forall {A : Type} (szs : list size) (ns : list A) (tr : @vector1 A),
    tr = Leaf szs ns -> length ns <= M.

Axiom leaf_elems_not_nil :
  forall {A : Type} (szs : list size) (ns : list A) (tr : @vector1 A),
    tr = Leaf szs ns -> ns <> [] /\ szs <> [].

(*

Axiom leaf_sizes_elems :
  forall {A : Set} (szs : list size) (ns : list A) (tr : @vector A),
  tr = Leaf szs ns -> length szs = length ns.

Axiom node_sizes_elems : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
   tr = Node ht szs trs -> length szs = length trs.

Axiom node_sizes_elems_m : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
tr = Node ht szs trs -> length trs <= m.

*)


(* ---------------------------------- *)
(* -- Length                          *)
(* ---------------------------------- *)


Definition vec_length {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | E => 0
  | Leaf szs ns  => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_nil a rst)
                    end
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_nil a rst)
                    end
  end.


(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : height) (i : nat) : nat := (i / (M ^ ht)) mod M.

Lemma mod_lt : forall n, n mod M < M.
Proof. intros. unfold modulo, M. omega. Qed.

Lemma index_of_lt_M : forall ht i, index_of ht i < M.
Proof. intros. unfold index_of, M. apply mod_lt. Qed.

Fixpoint get {A : Type} (idx : nat) (tr : @vector1 A) (default : A) : A :=
  match tr with
  | E => default
  | Leaf _ ns =>
    (* Need to prove: (slot' < length ns) *)
    let slot' := index_of 0 idx in
    nth slot' ns default
  | Node ht szs trs =>
    let slot' := index_of ht idx in
    (* Need to prove: (slot' < length trs) *)
    match (slot' , trs) with
    | (0 , t0 :: ts)                   => get idx t0 default
    | (1 , t0 :: t1 :: ts)             => get idx t1 default
    | (2 , t0 :: t1 :: t2 :: ts)       => get idx t2 default
    | (3 , t0 :: t1 :: t2 :: t3 :: ts) => get idx t3 default
    | _                                => default
    end
  end.

(* Axiom get_and_default : *)
(*   forall {A : Type} (idx : nat) (tr : @vector1 A) (default : A), *)
(*     idx < vec_length tr -> get idx tr default <> default. *)

Definition last_vec {A : Type} (tr : vector1) (default : A) : A :=
  get (vec_length tr) tr default.


(* ---------------------------------- *)
(* -- Snoc                            *)
(* ---------------------------------- *)

Fixpoint mkLeafAtHeight {A : Type} (ht : height) (v1 : A) : (vector1) :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.


Definition join {A : Type} (a : @vector1 A) (b : @vector1 A) : (@vector1 A) :=
  Node (get_height a + 1) [ vec_length a ; (vec_length a + vec_length b) ] [a ; b].


Definition vec_has_space_p {A : Type} (tr : @vector1 A) : bool :=
  match tr with
  | E             => true
  | Leaf _ ns     => length ns <? M
  | Node ht szs _ =>
    match szs with
    | [] => true
    | sz :: rst =>
      let last_sz := strong_last (sz :: rst) (cons_not_nil sz rst) in
      last_sz <? @vec_capacity A ht
    end
  end.


(* Assume that vector has space at the end, and snoc. *)
Fixpoint snoc_Bottom
  {A : Type} (fuel : nat) (tr : @vector1 A) (v1 : A) : option (@vector1 A) :=
  match tr with
  | E => Some (Node 1 [1] [Leaf [1] [v1]])

  | Leaf szs ns =>
    (* We don't check if (length ns) < M here, but do it before recurring
       in the Node case. *)
    match szs with
      | [] => Some (Leaf [1] [v1])
      | sz :: rst =>
        let last_sz := strong_last (sz :: rst) (cons_not_nil sz rst) in
        Some (Leaf (szs ++ [last_sz + 1]) (ns ++ [v1]))
    end

  | Node ht szs trs =>
    match fuel with
    (* This value will never be None. Should I try to prove it to Coq? *)
    | 0   => None
    | S n =>
      match (szs, trs) with
      | (sz :: ss, tr :: ts) =>
        let last_sz := strong_last (sz :: ss) (cons_not_nil sz ss) in
        let szs'    := removelast szs in
        let last_tr := strong_last (tr :: ts) (cons_not_nil tr ts) in
        let trs'    := removelast trs in
        if vec_has_space_p last_tr
        then match snoc_Bottom n last_tr v1 with
             | Some snocd => Some (Node ht (szs' ++ [last_sz + 1]) (trs' ++ [snocd]))
             (* This value will never be None. Should I try to prove it to Coq? *)
             | None => None
             end
        else
          let branch  := mkLeafAtHeight (ht - 1) v1 in
          let last_sz := last ss sz in
          let szs'    := szs ++ [1 + last_sz] in
          let trs'    := trs ++ [branch]
          in Some (Node ht szs' trs')

      | _ => None
      end
    end
  end.

Program Fixpoint snoc {A : Type} (tr : vector1) (v : A) : vector1 :=
  if vec_has_space_p tr
  then  match snoc_Bottom (vec_length tr) tr v with
        | Some tr2 => tr2
        | None => _
        end
  else join tr (mkLeafAtHeight (get_height tr) v).

(*

Axiom snoc_Bottom_Some :
  forall {A : Type} (idx : nat) (tr : @vector1 A) (v : A),
    rightmost_has_space_p tr = true ->
    (exists fuel tr2, snoc_Bottom fuel tr v = Some tr2).

*)


(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Type} (tr : @vector1 A) (acc : list A) : list A :=
  match tr with
  | E => []
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Type} (tr : @vector1 A) : list A :=
  go_toList tr [].

Fixpoint fromList {A : Type} (xs : list A) : (@vector1 A) :=
  fold_left (fun acc x => snoc acc x) xs E.

Compute (fromList (seq 1 18)).

(* ---------------------------------- *)
(* -- Theorems                        *)
(* ---------------------------------- *)

Lemma get_and_default :
  forall {A : Type} (idx : nat) (tr : @vector1 A) (default : A),
    tr <> E -> idx < vec_length tr -> get idx tr default <> default.
Proof.
  intros. unfold get. induction tr.
  + contradiction.
  + Admitted.
