Require Import Coq.Bool.Bool.
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

Lemma not_in_neq : forall n ls, ~ (In n ls) <-> Forall (fun n => n <> 0) ls.
Proof. Admitted.

Fixpoint append_all {A : Type} (ls : list (list A)) : list A :=
  match ls with
  | []      => []
  | x :: xs => x ++ append_all xs
  end.

Lemma div_1 : forall n, n / 1 = n.
Proof. Admitted.

Lemma zero_not_in_cons_succ : forall n l, ~ In 0 (n :: l) -> ~ In 0 ([n + 1] ++ n :: l).
Proof. Admitted.

Lemma zero_not_in_succ : forall n l, ~ In 0 l -> ~ In 0 ([n + 1] ++ l).
Proof. Admitted.

Lemma zero_not_in_sublist : forall n l, ~ In 0 (n :: l) -> ~ In 0 l.
Proof. Admitted.

Lemma S_lt_eq : forall n m, n < m -> S n <= m.
Proof. Admitted.

Lemma add_not_0 : forall a b, a <> 0 -> b <> 0 -> a + b <> 0.
Proof. Admitted.

(* ---------------------------------- *)
(* -- bdestruct                       *)
(* ---------------------------------- *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
   [eauto with bdestruct
   | destruct H as [H|H];
     [ | try first [apply not_lt in H | apply not_le in H]]].

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
