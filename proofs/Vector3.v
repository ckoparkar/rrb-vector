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
| Inv1 : forall (ht : nat) (szs : list nat) (ns : list (tree A)),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns <= M -> length szs = length ns
    -> Forall is_RRB ns -> is_RRB (Node ht szs ns)
| Inv2 : forall (szs : list nat) (ns : list A),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns <= M -> length szs = length ns
    -> is_RRB (Leaf szs ns)
| Inv3 : is_RRB E.


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

(* Theorem 1: Only the empty vector has length = 0. *)
Theorem vec_length_0_E : forall A vec,
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
    let slot'' := (length trs) - slot' - 1 in
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

Lemma mkLeafAtHeight_not_E : forall A ht (a : A), mkLeafAtHeight ht a <> E.
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight. intro. inversion H.
  + unfold mkLeafAtHeight. intro. inversion H.
Qed.

Lemma mkLeafAtHeight_not_E_sym : forall A ht (a : A), E <> mkLeafAtHeight ht a.
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight. intro. inversion H.
  + unfold mkLeafAtHeight. intro. inversion H.
Qed.

Definition join {A : Type} (a : tree A) (b : tree A) : (tree A) :=
  Node (get_height a + 1) [ (vec_length a + vec_length b) ; vec_length b ] [a ; b].


Definition vec_has_space_p {A : Type} (tr : tree A) : bool :=
  match tr with
  | E             => true
  | Leaf _ ns     => length ns <? M
  | Node ht szs trs =>
    match szs with
    | [] => true
    | sz :: rst => sz <? vec_capacity tr
    end
  end.


Fixpoint snoc_Bottom {A : Type} (tr : tree A) (v1 : A) : (tree A) :=
  match tr with
  | E => (Node 1 [1] [Leaf [1] [v1]])

  | Leaf szs ns =>
    if vec_has_space_p tr
    then match szs with
         | sz :: rst => (Leaf ([sz + 1] ++ (sz :: rst)) ([v1] ++ ns))
         | _         => E
         end
    else E

  | Node ht szs trs =>
      match (szs, trs) with
      | (sz :: ss, t :: ts) =>
        if vec_has_space_p t
        then match snoc_Bottom t v1 with
             | E     => E
             | snocd => (Node ht ([sz + 1] ++ ss) ([snocd] ++ ts))
             end
        else
          let branch  := mkLeafAtHeight (ht - 1) v1 in
          let szs'    := [sz + 1] ++ szs in
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

(* What does it mean for something to be in a vector --
   like 'In' for lists in the standard library. *)
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
  vec_has_space_p vec = true -> is_RRB vec -> In_Vec a (snoc_Bottom vec a).
Proof.
  intros A vec a vhp H. induction vec using tree_ind'.
  (* tr = E *)
  + unfold snoc_Bottom. simpl. left. left. reflexivity.
  (* tr = Leaf *)
  + unfold snoc_Bottom. destruct (vec_has_space_p (Leaf szs ls)) eqn:d_vec_has_space.
    -  destruct szs eqn:d_szs.
       * inversion H. contradiction.
       * simpl. left. reflexivity.
    - inversion vhp.
  (* tr = Node *)
  + unfold snoc_Bottom. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - destruct ls eqn:d_ls.
      * inversion H. contradiction.
      * fold (snoc_Bottom t a). destruct (vec_has_space_p t) eqn:d_vec_has_space.
        ++ assert(H1: In_Vec a (snoc_Bottom t a)).
           { inversion H0. apply H3. apply d_vec_has_space.
             inversion H. inversion H13. apply H16. }
           (* ^ would've been impossible to prove without the stronger
              induction principle, tree_ind'. *)
           destruct (snoc_Bottom t a) eqn:snocd.
           ** apply H1.
           ** apply In_Vec_node_append. apply H1.
           ** apply In_Vec_node_append. apply H1.
        ++ apply In_Vec_node_append. apply In_Vec_mkLeafAtHeight.
Qed.


(* Theorem 2: If you something into a vector, it should be in the vector! *)
Theorem snoc_In_Vec : forall {A} vec (a : A),
  is_RRB vec -> In_Vec a (snoc vec a).
Proof.
  intros. unfold snoc. destruct (vec_has_space_p vec) eqn:d_vec_has_space.
  + apply snoc_Bottom_In_Vec. apply d_vec_has_space. apply H.
  + unfold join. apply In_Vec_node_append. apply In_Vec_mkLeafAtHeight.
Qed.


(* 3: Snoc maintains the invariant. *)
Lemma is_RRB_mkLeafAtHeight : forall {A} ht (a : A), is_RRB (mkLeafAtHeight ht a).
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight. apply Inv2.
    - intro. inversion H.
    - intro. inversion H.
    - simpl. unfold not. intro. inversion H. inversion H0. apply H0.
    - simpl. unfold M. auto.
    - simpl. unfold M. auto.
  + unfold mkLeafAtHeight. fold (mkLeafAtHeight ht a). apply Inv1.
    - intro. inversion H.
    - intro. inversion H.
    - simpl. unfold not. intro. inversion H. inversion H0. apply H0.
    - simpl. unfold M. auto.
    - simpl. unfold M. auto.
    - apply Forall_cons. apply IHht. apply Forall_nil.
Qed.

Lemma snocBottom_is_RRB : forall {A} vec (a : A),
  is_RRB vec -> is_RRB (snoc_Bottom vec a).
Proof.
  intros. induction vec using tree_ind'.
  (* vec = E *)
  + unfold snoc_Bottom. apply Inv1.
    - intro. inversion H0.
    - intro. inversion H0.
    - unfold not. intro. inversion H0. inversion H1. inversion H1.
    - simpl. unfold M. auto.
    - simpl. unfold M. auto.
    - apply Forall_cons.
      * apply Inv2.
        ++ intro. inversion H0.
        ++ intro. inversion H0.
        ++ unfold not. intro. inversion H0. inversion H1. inversion H1.
        ++ simpl. unfold M. auto.
        ++ simpl. unfold M. auto.
      * apply Forall_nil.
  (* vec = Leaf *)
  + unfold snoc_Bottom.
    - destruct (vec_has_space_p (Leaf szs ls)) eqn:d_vec_has_space.
      * destruct szs eqn:d_szs.
        ++ apply Inv3.
        ++ apply Inv2.
          -- simpl. intro. inversion H0.
          -- simpl. intro. inversion H0.
          -- unfold not. inversion H.
             apply zero_not_in_cons_succ. apply H4.
          -- (* To prove, length ([a] ++ ls) <= M, we show that (length ls < M)
                and adding one element to that should be <= M. *)
            assert(H1: length ls < 4).
            { unfold vec_has_space_p, M in d_vec_has_space.
              simpl. bdestruct (length ls <? 4). apply H0. inversion d_vec_has_space. }
            unfold M. simpl. omega.
          -- rewrite <- d_szs. simpl. inversion H. rewrite <- d_szs in H6.
             rewrite H6. reflexivity.
      * apply Inv3.
  (* vec = Node *)
  + unfold snoc_Bottom.
    - destruct szs eqn:d_szs.
      * inversion H. contradiction.
      * destruct ls eqn:d_ls.
        ++ inversion H. contradiction.
        ++ fold (snoc_Bottom t a). destruct (vec_has_space_p t) eqn:d_vec_has_space.
           -- assert(H1: is_RRB (snoc_Bottom t a)).
              { inversion H0. apply H3. inversion H. inversion H13. apply H16. }
              destruct (snoc_Bottom t a).
              ** apply H1.
              ** apply Inv1.
                 +++ intro. inversion H2.
                 +++ intro. inversion H2.
                 +++ inversion H.
                     apply zero_not_in_succ. apply zero_not_in_sublist with n.
                     apply H7.
                 +++ inversion H. inversion H10. inversion H14.
                     --- simpl. unfold M. auto.
                     --- subst. simpl. rewrite H8. reflexivity.
                 +++ simpl. inversion H. apply H9.
                 +++ apply Forall_cons. apply H1.
                     inversion H. inversion H10. apply H14.
              ** apply Inv1.
                 +++ intro. inversion H2.
                 +++ intro. inversion H2.
                 +++ inversion H. apply zero_not_in_succ.
                     apply (zero_not_in_sublist n l). apply H7.
                 +++ inversion H. apply H8.
                 +++ inversion H. apply H9.
                 +++ apply Forall_cons. apply H1.
                     inversion H. inversion H10. apply H14.
           -- apply Inv1.
              +++ intro. inversion H1.
              +++ intro. inversion H1.
              +++ inversion H. apply zero_not_in_cons_succ.
                 apply H6.
              +++ (* <= M *) admit.
              +++ simpl. inversion H. assert(H10: S (length l) = S (length l0)).
                  { apply H8. }
                  rewrite H10. reflexivity.
              +++ apply Forall_cons. apply is_RRB_mkLeafAtHeight.
                     inversion H. apply H9.
Admitted.

Lemma join_is_RRB : forall {A} vec ht (a : A),
  is_RRB vec -> vec <> E -> is_RRB (join (mkLeafAtHeight ht a) vec).
Proof.
  intros. unfold join. apply Inv1.
    - intro. inversion H1.
    - intro. inversion H1.
    - induction vec using tree_ind'.
      * contradiction.
      * assert(H1: vec_length (mkLeafAtHeight ht a) <> 0).
        { rewrite vec_length_0_E. apply mkLeafAtHeight_not_E.
          apply is_RRB_mkLeafAtHeight. }
        assert(H2: vec_length (Leaf szs ls) <> 0).
        { rewrite vec_length_0_E. intro. inversion H2. apply H. }
        apply not_in_neq.
        apply Forall_cons. apply add_not_0. apply H1. apply H2.
        apply Forall_cons. apply H2.
        apply Forall_nil.
      * assert(H2: vec_length (mkLeafAtHeight ht a) <> 0).
        { rewrite vec_length_0_E. apply mkLeafAtHeight_not_E.
          apply is_RRB_mkLeafAtHeight. }
        assert(H3: vec_length (Node ht0 szs ls) <> 0).
        { rewrite vec_length_0_E. intro. inversion H3. apply H. }
        apply not_in_neq.
        apply Forall_cons. apply add_not_0. apply H2. apply H3.
        apply Forall_cons. apply H3.
        apply Forall_nil.
    - simpl. unfold M. auto.
    - simpl. reflexivity.
    - apply Forall_cons. apply is_RRB_mkLeafAtHeight.
      apply Forall_cons. apply H.
      apply Forall_nil.
Qed.

Theorem snoc_is_RRB : forall {A} vec (a : A),
  is_RRB vec -> is_RRB (snoc vec a).
Proof.
  intros. unfold snoc. destruct (vec_has_space_p vec) eqn:d_vec_has_space.
  + apply snocBottom_is_RRB. apply H.
  + apply join_is_RRB.
    - apply H.
    - induction vec using tree_ind'.
      * unfold vec_has_space_p in d_vec_has_space. inversion d_vec_has_space.
      * intro. inversion H0.
      * intro. inversion H1.
Qed.


(* ---------------------------------- *)
(* -- Abs                             *)
(* ---------------------------------- *)

Inductive Abs  {A : Type} : tree A -> list A -> Prop :=
| Abs_E : Abs E []
| Abs_L : forall szs ns, Abs (Leaf szs ns) ns
| Abs_N : forall ht szs ns ls,
          AbsL ns ls -> Abs (Node ht szs ns) (append_all ls)

with AbsL {A : Type} : list (tree A) -> list (list A) -> Prop :=
| AbsL_Nil  : AbsL [] []
| AbsL_Cons : forall t l ts ls,
              Abs t l -> AbsL ts ls -> AbsL (t :: ts) (l :: ls).

Scheme Abs_mut := Induction for Abs Sort Prop
with AbsL_mut := Induction for AbsL Sort Prop.

Lemma mkLeafAtHeight_relate_ind : forall {A} ht (val : A) ls,
  Abs (mkLeafAtHeight ht val) ls -> Abs (mkLeafAtHeight (S ht) val) ls.
Proof.
  intros. induction ht.
  + simpl. simpl in H. rewrite append_all_rw2.
    apply Abs_N. apply AbsL_Cons. apply H. apply AbsL_Nil.
  + unfold mkLeafAtHeight. fold (mkLeafAtHeight ht val).
    rewrite append_all_rw2.
    apply Abs_N. apply AbsL_Cons. apply H. apply AbsL_Nil.
Qed.

Lemma mkLeafAtHeight_relate : forall {A} ht (val : A),
  Abs (mkLeafAtHeight ht val) [val].
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight. apply Abs_L.
  + apply mkLeafAtHeight_relate_ind. apply IHht.
Qed.

Lemma join_relate : forall {A} vec1 (vec2 : tree A) ls1 ls2,
  Abs vec1 ls1 -> Abs vec2 ls2 -> Abs (join vec1 vec2) (ls1 ++ ls2).
Proof.
  intros. unfold join.
  assert(H1: ls1 ++ ls2 = append_all [ls1 ; ls2]).
  { unfold append_all. simpl. rewrite append_nil. reflexivity. }
  rewrite H1.
  apply (Abs_N (get_height vec1 + 1) [vec_length vec1 + vec_length vec2; vec_length vec2] [vec1; vec2] [ls1 ; ls2]).
  apply AbsL_Cons. apply H. apply AbsL_Cons. apply H0. apply AbsL_Nil.
Qed.

Lemma snoc_Bottom_relate : forall {A} vec ls (val : A),
  is_RRB vec -> vec_has_space_p vec = true ->
  Abs vec ls -> Abs (snoc_Bottom vec val) (val :: ls).
Proof.
  intros. induction H1.
  (* vec = E *)
  + unfold snoc_Bottom. apply (Abs_N 1 [1] [Leaf [1] [val]] [[val]]).
    apply AbsL_Cons. apply Abs_L. apply AbsL_Nil.
  (* vec = Leaf *)
  + unfold snoc_Bottom. destruct (vec_has_space_p (Leaf szs ns)) eqn:d_vec_has_space.
    - destruct szs eqn:d_szs.
      * inversion H. contradiction.
      * apply Abs_L.
    - inversion H0.
  (* vec = Node *)
  + unfold snoc_Bottom. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - destruct ns eqn:d_ns.
      * inversion H. contradiction.
      * fold (snoc_Bottom t val). destruct (vec_has_space_p t) eqn:d_vec_has_space'.
        Focus 2.
        ++ assert (H2: (val :: append_all ls) = append_all [val :: append_all ls]).
           { simpl. rewrite append_nil. reflexivity. }
           rewrite H2.
           apply (Abs_N ht ([n + 1] ++ n :: l) ([mkLeafAtHeight (ht - 1) val] ++ t :: l0) [val :: append_all ls]).
           assert(H3: [mkLeafAtHeight (ht - 1) val] ++ t :: l0 = (mkLeafAtHeight (ht - 1) val) :: (t :: l0)).
           { simpl. reflexivity. }
           rewrite H3.
           assert (H4: ([val] :: ls) = [val :: append_all ls]).
           { apply append_all_rw1. }
           rewrite <- H4.
           apply AbsL_Cons.
           apply mkLeafAtHeight_relate. apply H1.
        ++ Admitted.


Theorem snoc_relate:
 forall {A} vec ls (val : A),
    is_RRB vec -> Abs vec ls -> Abs (snoc vec val) (val :: ls).
Proof.
  intros. unfold snoc. destruct (vec_has_space_p vec) eqn:d_vec_has_space.
  + apply snoc_Bottom_relate. apply H. apply d_vec_has_space. apply H0.
  + apply (join_relate (mkLeafAtHeight (get_height vec) val) vec [val] ls).
    apply mkLeafAtHeight_relate. apply H0.
Qed.

Theorem get_relate:
  forall {A : Type} n vec ls (d : A),
    is_RRB vec ->
    Abs vec ls -> get n vec d = nth n ls d.
Proof.
  intros. induction vec using tree_ind'.
  (* vec = E *)
  + unfold get. destruct (n <? vec_length E) eqn:d_vec_length.
    - unfold get'. inversion H0. rewrite nth_nil. reflexivity.
    - inversion H0. rewrite nth_nil. reflexivity.
  + unfold get. destruct (n <? vec_length (Leaf szs ls0)) eqn:d_vec_length.
    - unfold get'. inversion H0. rewrite <- H1.
