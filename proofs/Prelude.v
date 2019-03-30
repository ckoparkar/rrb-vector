Require Import Nat.
Require Import List.
Import ListNotations.

From Coq Require Import Omega.

(* -------------------------------------------------------------------------- *)

Lemma zero_gt_zero_false : 0 > 0 -> False.
Proof. omega. Qed.

Lemma zero_lt_zero_false : 0 < 0 -> False.
Proof. omega. Qed.

Lemma empty_not_empty {A : Type} : (@nil A) <> [] -> False.
Proof. congruence. Qed.

Lemma cons_not_nil {A : Type} : forall (a : A) (ls : list A), (a :: ls) <> [].
Proof. intros. congruence. Qed.

Lemma length_gt_zero_iff_not_nil {A : Set} (l : list A): length l > 0 <-> l <> [].
Proof.
  intros. split.
  + destruct l.
    - simpl. intros. apply zero_gt_zero_false in H. apply False_rec. apply H.
    - simpl. intros. apply cons_not_nil.
  + destruct l.
    - intros. congruence.
    - intros. unfold length. apply gt_Sn_O.
Qed.

Definition strong_head {A : Type} : forall ls : list A, ls <> [] -> A.
  refine (fun (ls : list A) =>
            match ls with
            | []     => fun _ => _
            | a :: _ => fun _ => a
            end).
  (* [] *)
  congruence.
Defined.

Definition strong_last {A : Type} : forall ls : list A, ls <> [] -> A.
  refine (fix f (ls : list A) :=
            match ls with
            | []       => fun pf  => _
            | a :: rst => fun _   => last rst a
            end).
  (* [] *)
  congruence.
Defined.

Definition strong_nth :
  forall {A : Set} (idx : nat) (ls : list A), idx < length ls -> A.
  refine (fix f {A : Set} (idx : nat) (ls : list A) :=
              match idx, ls with
              | 0   , []       => fun pf => _
              | S m , []       => fun pf => _
              | 0   , x :: rst => fun _  => x
              | S m , x :: rst => fun _  => nth m rst x
              end).
  (* 0   , [] *)
  + simpl in pf. omega.
  (* S m , [] *)
  + simpl in pf. omega.
Defined.

Lemma skipn_nil : forall A m, skipn m (@nil A) = (@nil A).
Proof.
  intros. induction m.
  + reflexivity.
  + reflexivity.
Qed.

Lemma skipn_cons :
  forall {A : Set} (m : nat) (xs : list A) (x : A),
  length (skipn m (x :: xs)) = length (skipn m xs) + 1.
Proof.
  intros. induction m.
  + simpl. omega.
  + simpl. Admitted.
(* Qed. *)

Lemma length_not_empty_inv {A B : Set} :
  forall (xs : list A) (ys : list B),
  length xs = length ys -> xs <> [] -> ys <> [].
Proof. Admitted.

(*

Lemma length_not_zero_inv {A : Set} :
  forall (xs : list A),  length xs <> 0 -> xs <> [].
Proof.
  intros. induction xs.
  + unfold length in H. congruence.
  + apply (cons_not_empty a xs).
Qed.

Lemma length_zero_inv {A : Set} :
  forall (xs : list A),  length xs = 0 -> xs = [].
Proof.
  intros. induction xs.
  + reflexivity.
  + apply length_zero_iff_nil. apply H.
Qed.

Lemma length_not_zero_inv_inv {A : Set} :
  forall (xs : list A), xs <> [] -> length xs <> 0.
Proof.
  intros. induction xs.
  + congruence.
  + unfold length. apply Nat.neq_succ_0.
Qed.

*)

Lemma skipn_length : forall {A : Set}
  (ls : list A) (n : nat), length (skipn n ls) = length ls - n.
Proof.
  intros. induction ls.
  + simpl. rewrite skipn_nil. reflexivity.
  + rewrite skipn_cons.
Admitted.

Lemma skipn_not_nil : forall {A : Set}
  (ls : list A) (n : nat), n < length ls -> ls <> [] -> skipn n ls <> [].
Proof. Admitted.

Lemma min_eq : forall n, min n n = n.
Proof.
  intros. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.
