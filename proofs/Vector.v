(* An implementation of vectors backed by a Radix-Balanced Tree. *)

Require Import Nat.
Require Import List.
Import ListNotations.
From Coq Require Import Omega.

From RRB Require Import Prelude.

(* -------------------------------------------------------------------------- *)

(* Branching factor *)
Definition m := 4.

Definition log2m := log2 m.

Definition mask := m - 1.

(* Useful type synonyms *)
Definition height := nat.
Definition size := nat.

(* The main datatype. *)
Inductive tree {A : Set} : Set :=
| Leaf : list size -> list A -> tree
| Node : height    -> list size -> list tree -> tree.

(* The type exported out of this module *)
Definition vector {A : Set} := tree (A := A).

(* Well this is technically not correct (Leaf doesn't have sizes), but OK for now. *)
Definition sizes {A : Set} (tr : @vector A) : list nat :=
  match tr with
  | Leaf szs _   => szs
  | Node _ szs _ => szs
  end.

(* ---------------------------------- *)
(* -- Other common operations         *)
(* ---------------------------------- *)

Definition vec_length {A : Set} (tr : @vector A) : nat :=
  match tr with
  | Leaf szs ns  => length szs
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_empty a rst)
                    end
  end.

Lemma vec_length_sizes {A : Set} :
  forall (tr : vector),  (vec_length tr > 0) -> (@sizes A tr) <> [].
Proof.
  intros. induction tr.
  + unfold vec_length in H. unfold sizes.
    apply length_gt_zero_iff_not_nil. apply H.
  + unfold sizes. unfold vec_length in H.
    induction l.
    - apply zero_gt_zero_false in H. unfold not. intro. apply H.
    - apply cons_not_empty.
Qed.

Axiom leaf_sizes_elems :
  forall {A : Set} (szs : list size) (ns : list A) (tr : @vector A),
    tr = Leaf szs ns -> length szs = length ns.

Lemma vec_length_leaves_sizes {A : Set} :
  forall (tr : vector) (szs : list size) (ns : list A),
    tr = Leaf szs ns -> vec_length tr = length ns.
Proof.
  intros. remember tr as tr'. induction tr.
  + rewrite H. unfold vec_length. apply leaf_sizes_elems with tr'. apply H.
  + congruence.
Qed.

(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : height) (i : nat) : nat :=
  (i / (pow m ht)) mod m.

Fixpoint check_slot_default
  (sz_js : list (nat * nat)) (idx : nat) (default : nat) : nat :=
  match sz_js with
  | [] => default
  | (sz , j) :: rst => if leb sz idx
                       then check_slot_default rst idx default
                       else j
  end.

Definition check_slot' :
  forall (sz_js : list (nat * nat)) (idx : nat), sz_js <> [] -> nat.
  refine (fix f (sz_js : list (nat * nat)) (idx : nat) :=
              match sz_js with
              | []              => fun pf  => _
              | (sz , j) :: rst =>
                  fun _ =>
                    if leb sz idx
                    then check_slot_default rst idx j
                    else j
              end).
    congruence.
Defined.

Definition check_slot
  (s : { sz_js : list (nat * nat) | sz_js <> [] }) (idx : nat) : nat :=
  check_slot' (proj1_sig s) idx (proj2_sig s).

Definition indexInNode
  (ht : height) (szs : list size) (idx : nat) : (nat * nat) :=
  let slot     := index_of ht idx in
  let sz_js    := skipn slot (combine szs (seq 0 (length szs))) in
  let slot'    := match sz_js with
                  | []      => slot
                  | a :: b  => check_slot (exist _ (a :: b) (cons_not_empty a b)) idx
                  end
  in let idx' := idx - (if eqb slot' 0
                        then 0
                        else nth (slot' - 1) szs 0)
     in (slot' , idx').

Definition get {A : Set}
   (tr : vector) (s : { idx : nat | (idx < @vec_length A tr) }) (default : A) : A.
  refine ((match tr as tr' return tr = tr' -> A with
           | Leaf szs ns => match s with
                            | exist _ idx pf => fun tr => strong_nth ns idx _
                            end
           | Node ht szs trs => fun _ => default
           end) (eq_refl tr)).
  (* tr = Leaf .. *)
  + rewrite vec_length_leaves_sizes with _ szs ns in pf.
    - apply pf.
    - apply tr.
Defined.

(* Compute (1 - 1). *)
(* Definition test1 := [ 4 ; 6; 8; 16 ]. *)
(* Compute (skipn 2 test1). *)
(* Compute (seq 0 (length test1)). *)
(* Compute (indexInNode 1 test1 10). *)
