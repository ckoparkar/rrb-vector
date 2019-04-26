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

(* The main datatype. *)
Inductive tree (A : Type) : Type :=
| E    : tree A
| Leaf : list nat -> list A -> tree A
| Node : nat -> list nat -> list (tree A) -> tree A.

Arguments E    {A}.
Arguments Leaf {A}.
Arguments Node {A}.

Print tree_ind.


(* See Nested Induction Types under:
   http://adam.chlipala.net/cpdt/html/InductiveTypes.html *)

Section tree_ind'.
  Variable A : Type.
  Variable P : (tree A) -> Prop.

  Hypothesis E_case : P E.

  Hypothesis Leaf_case : forall (szs : list nat) (ls : list A),
    P (Leaf szs ls).

  Hypothesis Node_case : forall (ht : nat) (szs : list nat) (ls : list (tree A)),
    Forall P ls -> P (Node ht szs ls).

  Fixpoint tree_ind' (tr : tree A) : P tr :=
    match tr with
      | E => E_case
      | Leaf szs ls => Leaf_case szs ls
      | Node ht szs ls => Node_case ht szs ls
        ((fix list_tree_ind (ls : list (tree A)) : Forall P ls :=
          match ls with
            | [] => Forall_nil P
            | tr' :: rest => Forall_cons tr' (tree_ind' tr') (list_tree_ind rest)
          end) ls)
    end.
End tree_ind'.

Print tree_ind'.


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


(* ---------------------------------- *)
(* -- Invariant datatype              *)
(* ---------------------------------- *)

Inductive is_RRB {A : Type} : tree A -> Prop :=
| Inv1 : forall (ht : nat) (szs : list nat) (ns : list (tree A)) (tr : tree A),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns < M -> length szs < M
    -> Forall is_RRB ns -> is_RRB (Node ht szs ns)
| Inv2 : forall (szs : list nat) (ns : list A) (tr : tree A),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns < M -> length szs < M
    -> is_RRB (Leaf szs ns).

Lemma node_elems_not_nil' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> ns <> [].
Proof. intros. inversion H. subst. apply H3. Qed.

Lemma node_szs_not_nil' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> szs <> [].
Proof. intros. inversion H. subst. apply H4. Qed.

Lemma node_zero_not_in_szs' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> ~ (In 0 szs).
Proof. intros. inversion H. subst. apply H5. Qed.

Lemma leaf_elems_not_nil' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> ns <> [].
Proof. intros. inversion H. subst. apply H2. Qed.

Lemma leaf_szs_not_nil' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> szs <> [].
Proof. intros. inversion H. subst. apply H3. Qed.

Lemma leaf_zero_not_in_szs' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> ~ (In 0 szs).
Proof. intros. inversion H. subst. apply H4. Qed.


(* ---------------------------------- *)
(* -- Length                          *)
(* ---------------------------------- *)

Definition vec_length {A : Type} (tr : tree A) : nat :=
  match tr with
  | E => 0
  | Leaf szs ns  => match szs with
                    | [] => 0
                    | a :: rst => a
                    end
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => a
                    end
  end.

Lemma vec_length_0_E : forall A vec,
  is_RRB vec -> @vec_length A vec = 0 <-> vec = E.
Proof.
  intros. split.
  (* -> *)
  + induction vec using tree_ind'.
    - reflexivity.
    - unfold vec_length. intro.
      destruct szs eqn:szs'.
      * inversion H. contradiction.
      * assert(H1: Forall (fun x => x <> 0) (n :: l)).
        { inversion H. apply (not_in_neq 0 (n :: l)). apply H5. }
        assert(H2: n <> 0).
        { inversion H1. apply H4. }
        contradiction.
    - unfold vec_length. intro. destruct szs eqn:szs'.
      * inversion H. contradiction.
      * assert(H2: Forall (fun x => x <> 0) (n :: l)).
        { inversion H. apply (not_in_neq 0 (n :: l)). apply H7. }
        assert(H3: n <> 0).
        { inversion H2. apply H5. }
        contradiction.
  (* <- *)
  + intro. rewrite H0. unfold vec_length. reflexivity.
Qed.

(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : nat) (i : nat) : nat := (i / (M ^ ht)) mod M.

Lemma mod_lt : forall n, n mod M < M.
Proof. intros. unfold modulo, M. omega. Qed.

Lemma index_of_lt_M : forall ht i, index_of ht i < M.
Proof. intros. unfold index_of, M. apply mod_lt. Qed.

Fixpoint get' {A : Type} (idx : nat) (tr : tree A) (default : A) : A :=
  match tr with
  | E => default
  | Leaf _ ns =>
    (* Need to prove: (slot' < length ns) *)
    let slot'  := index_of 0 idx in
    let slot'' := (length ns) - slot' - 1 in
    nth slot'' ns default
  | Node ht szs trs =>
    let slot' := index_of ht idx in
    let slot'' := (length szs) - slot' - 1 in
    (* Need to prove: (slot' < length trs) *)
    match (slot'' , trs) with
    | (0 , t0 :: ts)                   => get' idx t0 default
    | (1 , t0 :: t1 :: ts)             => get' idx t1 default
    | (2 , t0 :: t1 :: t2 :: ts)       => get' idx t2 default
    | (3 , t0 :: t1 :: t2 :: t3 :: ts) => get' idx t3 default
    | _                                => default
    end
  end.

Definition get {A : Type} (idx : nat) (tr : tree A) (default : A) : A :=
  if idx <? vec_length tr
  then get' idx tr default
  else default.


(* ---------------------------------- *)
(* -- Snoc                            *)
(* ---------------------------------- *)

Fixpoint mkLeafAtHeight {A : Type} (ht : nat) (v1 : A) : tree A :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.


Definition join {A : Type} (a : tree A) (b : tree A) : (tree A) :=
  Node (get_height a + 1) [ (vec_length a + vec_length b) ; vec_length b ] [a ; b].


Definition vec_has_space_p {A : Type} (tr : tree A) : bool :=
  match tr with
  | E             => true
  | Leaf _ ns     => length ns <? M
  | Node ht szs _ =>
    match szs with
    | [] => true
    | sz :: rst => sz <? vec_capacity tr
    end
  end.


Fixpoint snoc_Bottom
  {A : Type} (tr : tree A) (v1 : A) : (tree A) :=
  match tr with
  | E => (Node 1 [1] [Leaf [1] [v1]])
  (* We don't check if (length ns) < M here, but do it before recurring
     in the Node case. *)
  | Leaf szs ns =>
    match szs with
    | sz :: rst => (Leaf ([sz + 1] ++ (sz :: rst)) ([v1] ++ ns))
    | _         => E
    end

  | Node ht szs trs =>
      match (szs, trs) with
      | (sz :: ss, tr :: ts) =>
        if vec_has_space_p tr
        then match snoc_Bottom tr v1 with
             | E     => E
             | snocd => (Node ht ([sz + 1] ++ ss) ([snocd] ++ ts))
             end
        else
          let branch  := mkLeafAtHeight (ht - 1) v1 in
          let szs'    := [1 + sz] ++ szs in
          let trs'    := [branch] ++ trs
          in (Node ht szs' trs')
      | _ => E
      end
  end.

Definition snoc {A : Type} (tr : tree A) (v : A) : tree A :=
  if vec_has_space_p tr
  then snoc_Bottom tr v
  else join (mkLeafAtHeight (get_height tr) v) tr.


(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Type} (tr : tree A) (acc : list A) : list A :=
  match tr with
  | E => []
  | Leaf _ ns    => acc ++ (rev ns)
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Type} (tr : tree A) : list A :=
  go_toList tr [].

Fixpoint fromList {A : Type} (xs : list A) : (tree A) :=
  fold_left (fun acc x => snoc acc x) xs E.


(* ---------------------------------- *)
(* -- Theorems                        *)
(* ---------------------------------- *)

Fixpoint In_Vec {A : Type} (a : A) (tr : tree A) : Prop :=
  match tr with
  | E            => False
  | Leaf _ ns    => In a ns
  | Node _ _ trs =>
    ((fix in_vecs (a : A) (ls : list (tree A)) :=
        match ls with
        | [] => False
        | t :: ts => In_Vec a t \/ in_vecs a ts
        end) a trs)
  end.

Lemma In_Vec_mkLeafAtHeight :
  forall {A} ht (a : A), In_Vec a (mkLeafAtHeight ht a).
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight, In_Vec. apply in_eq.
  + simpl. left. apply IHht.
Qed.

Lemma In_Vec_node_append : forall {A} (a : A) ht vec vecs szs,
  In_Vec a vec -> In_Vec a (Node ht szs ([vec] ++ vecs)).
Proof.
  intros. simpl. left. apply H.
Qed.

Lemma snoc_Bottom_In_Vec : forall {A} vec (a : A),
  is_RRB vec -> In_Vec a (snoc_Bottom vec a).
Proof.
  intros. induction vec using tree_ind'.
  (* tr = E *)
  + unfold snoc_Bottom. simpl. left. left. reflexivity.
  (* tr = Leaf *)
  + unfold snoc_Bottom. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - simpl. left. reflexivity.
  (* tr = Node *)
  + unfold snoc_Bottom. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - destruct ls eqn:d_ls.
      * inversion H. contradiction.
      * fold (snoc_Bottom t a). destruct (vec_has_space_p t) eqn:d_vec_has_space.
        ++ assert(H1: In_Vec a (snoc_Bottom t a)).
           { inversion H0. apply H3. inversion H. inversion H13. apply H16. }
           (* ^ would've been impossible to prove without the stronger
              induction principle, tree_ind'. *)
           destruct (snoc_Bottom t a) eqn:snocd.
           ** apply H1.
           ** apply In_Vec_node_append. apply H1.
           ** apply In_Vec_node_append. apply H1.
        ++ apply In_Vec_node_append. apply In_Vec_mkLeafAtHeight.
Qed.


Lemma snoc_In_Vec : forall {A} vec (a : A),
  is_RRB vec -> In_Vec a (snoc vec a).
Proof.
  intros. unfold snoc. destruct (vec_has_space_p vec) eqn:vec_has_space.
  + apply snoc_Bottom_In_Vec. apply H.
  + unfold join. apply In_Vec_node_append. apply In_Vec_mkLeafAtHeight.
Qed.
