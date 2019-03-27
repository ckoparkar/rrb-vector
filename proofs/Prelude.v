Require Import Nat.
Require Import List.
Import ListNotations.

From Coq Require Import Omega.

(* -------------------------------------------------------------------------- *)

Lemma zero_gt_zero_false : 0 > 0 -> False.
Proof. omega. Qed.

Lemma empty_not_empty {A : Type} : (@nil A) <> [] -> False.
Proof. congruence. Qed.

Lemma cons_not_empty {A : Type} : forall (a : A) (ls : list A), (a :: ls) <> [].
Proof. intros. congruence. Qed.

Lemma length_gt_zero_iff_not_nil {A : Set} (l : list A): length l > 0 <-> l <> [].
Proof.
  intros. split.
  + destruct l.
    - simpl. intros. apply zero_gt_zero_false in H. apply False_rec. apply H.
    - simpl. intros. apply cons_not_empty.
  + destruct l.
    - intros. congruence.
    - intros. unfold length. apply gt_Sn_O.
Qed.

Definition strong_head : forall ls : list nat, ls <> [] -> nat.
  refine (fun (ls : list nat) =>
            match ls with
            | []     => fun _ => _
            | a :: _ => fun _ => a
            end).
  (* [] *)
  congruence.
Defined.

Definition strong_last : forall ls : list nat, ls <> [] -> nat.
  refine (fix f (ls : list nat) :=
            match ls with
            | []       => fun pf  => _
            | a :: rst => match rst with
                          | [] => fun _ => a
                          | _  => fun _ => last rst a
                          end
            end).
  (* [] *)
  congruence.
Defined.

Definition strong_nth :
  forall {A : Set} (ls : list A) (idx : nat), idx < length ls -> A.
  refine (fix f {A : Set} (ls : list A) (idx : nat) :=
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
