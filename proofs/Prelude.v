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

Lemma length_gt_zero_iff_not_nil {A : Type} (l : list A): length l > 0 <-> l <> [].
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

Program Fixpoint strong_last {A : Type} (ls : list A) (pf : ls <> []) : A :=
  match ls with
  | []       => _
  | a :: rst => last rst a
  end.

Definition strong_nth :
  forall {A : Type} (idx : nat) (ls : list A), idx < length ls -> A.
  refine (fix f {A : Type} (idx : nat) (ls : list A) :=
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
Proof. induction m ; auto. Qed.

Lemma min_eq : forall n, min n n = n.
Proof.
  intros. induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

Definition snoc_list {A : Type} (ls : list A) (v : A) : list A :=
  ls ++ [v].

Lemma In_append : forall A (a : A) xs, In a (xs ++ [a]).
Proof.
  intros. induction xs.
  + simpl. left. reflexivity.
  + simpl. right. apply IHxs.
Qed.

Lemma last_not_In : forall A (ls : list A) a (pf: ls <> []),
  ~ (In a ls) -> strong_last ls pf <> a.
Proof. Admitted.


Fixpoint append_all {A : Type} (ls : list (list A)) : list A :=
  match ls with
  | []      => []
  | x :: xs => x ++ append_all xs
  end.


Lemma div_1 : forall n, n / 1 = n.
Proof. Admitted.
