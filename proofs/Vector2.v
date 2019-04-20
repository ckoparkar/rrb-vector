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
Inductive tree (A : Type) : Type :=
| E    : tree A
| Leaf : list size -> list A -> tree A
| Node : height -> list size -> list (tree A) -> tree A.

Arguments E    {A}.
Arguments Leaf {A}.
Arguments Node {A}.

(* The type exported out of this module *)
Definition vector1 (A : Type) := tree A.

(* Upper bound on the #elems in a tree of height h *)
Definition vec_capacity {A : Type} (tr : tree A) : nat :=
  match tr with
  | E           => 0
  | Leaf _ _    => M
  | Node ht _ _ => M ^ (ht + 1)
  end.

Definition get_height {A : Type} (tr : tree A) : nat :=
  match tr with
  | E           => 0
  | Leaf _ _    => 0
  | Node ht _ _ => ht
  end.

Axiom node_elems_not_nil :
  forall {A : Type} (ht : height) (szs : list size) (ns : list (tree A)) (tr : tree A),
    tr = Node ht szs ns -> ns <> [] /\ szs <> [].

(*

Axiom leaf_elems_M :
  forall {A : Type} (szs : list size) (ns : list A) (tr : tree A),
    tr = Leaf szs ns -> length ns <= M.

Axiom leaf_elems_not_nil :
  forall {A : Type} (szs : list size) (ns : list A) (tr : tree A),
    tr = Leaf szs ns -> ns <> [] /\ szs <> [].

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


Definition vec_length {A : Type} (tr : tree A) : nat :=
  match tr with
  | E => 0
  | Leaf szs ns  => match szs with
                    | [] => 0
                    | a :: rst => last rst a
                    end
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => last rst a
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

Fixpoint get {A : Type} (idx : nat) (tr : tree A) (default : A) : A :=
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
    | (0 , t0 :: [])                   => get idx t0 default
    | (1 , t0 :: t1 :: [])             => get idx t1 default
    | (2 , t0 :: t1 :: t2 :: [])       => get idx t2 default
    | (3 , t0 :: t1 :: t2 :: t3 :: []) => get idx t3 default
    | _                                => default
    end
  end.

(* Axiom get_and_default : *)
(*   forall {A : Type} (idx : nat) (tr : tree A) (default : A), *)
(*     idx < vec_length tr -> get idx tr default <> default. *)

Definition last_vec {A : Type} (tr : tree A) (default : A) : A :=
  get (vec_length tr) tr default.


(* ---------------------------------- *)
(* -- Snoc                            *)
(* ---------------------------------- *)

Fixpoint mkLeafAtHeight {A : Type} (ht : height) (v1 : A) : tree A :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.


Definition join {A : Type} (a : tree A) (b : tree A) : (tree A) :=
  Node (get_height a + 1) [ vec_length a ; (vec_length a + vec_length b) ] [a ; b].


Definition vec_has_space_p {A : Type} (tr : tree A) : bool :=
  match tr with
  | E             => true
  | Leaf _ ns     => length ns <? M
  | Node ht szs _ =>
    match szs with
    | [] => true
    | sz :: rst =>
      let last_sz := last rst sz in
      last_sz <? vec_capacity tr
    end
  end.


(* Assume that vector has space at the end, and snoc. *)
Fixpoint snoc_Bottom
  {A : Type} (fuel : nat) (tr : tree A) (v1 : A) : option (tree A) :=
  match tr with
  | E => Some (Node 1 [1] [Leaf [1] [v1]])

  | Leaf szs ns =>
    (* We don't check if (length ns) < M here, but do it before recurring
       in the Node case. *)
    match szs with
      | [] => Some (Leaf [1] [v1])
      | sz :: rst =>
        let last_sz := last rst sz in
        Some (Leaf (szs ++ [last_sz + 1]) (ns ++ [v1]))
    end

  | Node ht szs trs =>
    match fuel with
    (* This value will never be None. Should I try to prove it to Coq? *)
    | 0   => None
    | S n =>
      match (szs, trs) with
      | (sz :: ss, tr :: ts) =>
        let last_tr := strong_last (tr :: ts) (cons_not_nil tr ts) in
        if vec_has_space_p last_tr
        then let last_sz := strong_last (sz :: ss) (cons_not_nil sz ss) in
             let szs'    := removelast szs in
             let trs'    := removelast trs in
             match snoc_Bottom n last_tr v1 with
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

Fixpoint snoc {A : Type} (tr : tree A) (v : A) : tree A :=
  if vec_has_space_p tr
  then  match snoc_Bottom (vec_length tr) tr v with
        | Some tr2 => tr2
        | None => E
        end
  else join tr (mkLeafAtHeight (get_height tr) v).

Axiom snoc_Bottom_Some :
  forall {A : Type} (idx : nat) (tr : tree A) (v : A),
    (* vec_has_space_p tr = true -> *)
    (exists fuel tr2, snoc_Bottom fuel tr v = Some tr2).


(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Type} (tr : tree A) (acc : list A) : list A :=
  match tr with
  | E => []
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Type} (tr : tree A) : list A :=
  go_toList tr [].

Fixpoint fromList {A : Type} (xs : list A) : (tree A) :=
  fold_left (fun acc x => snoc acc x) xs E.

Compute (fromList (seq 1 18)).

(* ---------------------------------- *)
(* -- Theorems                        *)
(* ---------------------------------- *)

Fixpoint In_Vec {A : Type} (a : A) (tr : tree A) : Prop :=
  match tr with
  | E            => False
  | Leaf _ ns    => In a ns
  | Node _ _ trs =>
    match trs with
    | t0 :: []                   => In_Vec a t0
    | t0 :: t1 :: []             => In_Vec a t1
    | t0 :: t1 :: t2 :: []       => In_Vec a t2
    | t0 :: t1 :: t2 :: t3 :: [] => In_Vec a t3
    | _ => False
    end
  end.

Lemma mkLeafAtHeight_in_vec :
  forall A ht a, @In_Vec A a (mkLeafAtHeight ht a).
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight, In_Vec. apply in_eq.
  + apply IHht.
Qed.

Lemma snoc_In_Vec : forall A a vec, @In_Vec A a (snoc vec a).
Proof.
  intros. induction vec.
  (* tr = E *)
  + unfold snoc, vec_has_space_p, snoc_Bottom.
    cbv. left. reflexivity.

  (* tr = Leaf *)
  + unfold snoc, vec_has_space_p. destruct (length l0 <? M).

    (* snoc_Bottom ... *)
    - unfold vec_length. destruct l.
      (* Leaf [] [] *)
      * unfold snoc_Bottom. unfold In_Vec. apply in_eq.

      (* Leaf (s :: ss) (n :: ns) *)
      * unfold snoc_Bottom.
        (* why doesn't Coq eliminate irrelevant cases. *)
        admit.

    (* join ... *)
    - unfold join, get_height, mkLeafAtHeight.
      unfold In_Vec. apply in_eq.

  (* tr = Node *)
  + unfold snoc, vec_has_space_p. destruct l eqn:l'.
    - apply (node_elems_not_nil h l l0 (Node h l l0)). reflexivity. apply l'.
    - destruct (last l1 s <? vec_capacity (Node h (s :: l1) l0)).
      (* why doesn't Coq eliminate irrelevant cases. *)
      * admit.
      * unfold join, mkLeafAtHeight. simpl. apply (mkLeafAtHeight_in_vec A h a).
Admitted.

(*

Lemma get_and_default :
  forall {A : Type} (idx : nat) (tr : tree A) (default : A),
    idx < vec_length tr -> In (get idx tr default) (toList tr).
Proof.
  intros. induction tr.
  + unfold get. contradiction.
  + Admitted.

*)
