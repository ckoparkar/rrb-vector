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

Definition strong_last_In {A : Type} : forall (xs : list A) (x : A) (pf : xs <> []),
  x = strong_last xs pf -> In x xs.
Proof. Admitted.

Definition strong_nth_In :
  forall {A : Set} (idx : nat) (xs : list A) (x : A) (pf : idx < length xs),
  x = strong_nth idx xs pf -> In x xs.
Proof. Admitted.

Lemma skipn_nil : forall A m, skipn m (@nil A) = (@nil A).
Proof. induction m ; auto. Qed.


Lemma min_eq : forall n, min n n = n.
Proof.
  intros. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.
