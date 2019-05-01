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

Lemma sym_not_eq : forall (a : nat) b, a <> b -> b <> a.
Proof.
  intros. intro. symmetry in H0. contradiction.
Qed.

Lemma not_in_neq : forall n ls, ~ (In n ls) <-> Forall (fun m : nat => m <> n) ls.
Proof.
  intros. split.
  (* -> *)
  + unfold not. intro. induction ls.
    - apply Forall_nil.
    - apply Forall_cons. apply not_in_cons in H. inversion H. apply sym_not_eq.
      apply H0. apply IHls. intro. destruct H. apply in_cons. apply H0.
  (* <- *)
  + intros. induction ls.
    - simpl. intro. apply H0.
    - apply not_in_cons. split.
      * inversion H. apply sym_not_eq. apply H2.
      * apply IHls. inversion H. apply H3.
Qed.

Fixpoint rev_append_all {A : Type} (ls : list (list A)) : list A :=
  match ls with
  | []      => []
  | x :: xs => rev_append_all xs ++ x
  end.

Fixpoint append_all {A : Type} (ls : list (list A)) : list A :=
  match ls with
  | []      => []
  | x :: xs => x ++ append_all xs
  end.

Lemma zero_not_in_cons_succ : forall n l, ~ In 0 (n :: l) -> ~ In 0 ([n + 1] ++ n :: l).
Proof.
  intros. apply not_in_cons. split.
  + omega.
  + apply H.
Qed.

Lemma zero_not_in_succ : forall n l, ~ In 0 l -> ~ In 0 ([n + 1] ++ l).
Proof.
  intros. apply not_in_cons. split.
  + omega.
  + apply H.
Qed.

Lemma zero_not_in_sublist : forall n l, ~ In 0 (n :: l) -> ~ In 0 l.
Proof.
  intros. apply not_in_cons in H. inversion H. apply H1.
Qed.

Lemma sum_0_iff_0 : forall a b, a + b = 0 <-> a = 0 /\ b = 0.
Proof.
  split.
  (* -> *)
  + intros. split.
    - omega.
    - omega.
  + intros. omega.
Qed.

Lemma add_not_0 : forall a b, a <> 0 -> b <> 0 -> a + b <> 0.
Proof.
  intros. rewrite sum_0_iff_0. unfold not.
  intro. inversion H1. contradiction.
Qed.

Lemma n_not_lt_0 : forall n, ~ (n < 0).
Proof.
  intros. induction n.
  + unfold not. intro. inversion H.
  + unfold not. intro. inversion H.
Qed.

Lemma append_assoc : forall {A} (ls1 : list A) ls2 ls3,
  ls1 ++ (ls2 ++ ls3) = (ls1 ++ ls2) ++ ls3.
Proof.
  intros. induction ls1.
  + simpl. reflexivity.
  + simpl. rewrite IHls1. reflexivity.
Qed.

Lemma append_nil : forall {A} (ls1 : list A), ls1 ++ [] = ls1.
Proof.
  intros. induction ls1.
  + simpl. reflexivity.
  + simpl. rewrite IHls1. reflexivity.
Qed.

Lemma append_all_rw1 : forall A (val : A) ls, val :: append_all ls = append_all ([val] :: ls).
Proof.
  intros. induction ls.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

Lemma append_all_rw2 : forall {A} (ls : list A), ls = append_all [ls].
Proof.
  intros. unfold append_all. rewrite append_nil. reflexivity.
Qed.

Lemma append_all_rw3 : forall A lls (ls : list A),
  length lls = 1 -> lls = [ls] <-> append_all lls = ls.
Proof.
  split.
  (* -> *)
  + intros. rewrite H0.
    unfold append_all. apply append_nil.
  (* -> *)
  + intros. induction lls.
    - inversion H.
    - assert (H1: lls = []).
      { apply length_zero_iff_nil. inversion H. reflexivity. }
      rewrite H1. rewrite H1 in H0.
      rewrite <- append_all_rw2 in H0. rewrite H0. reflexivity.
Qed.

Lemma nth_nil : forall A n (d : A), nth n [] d = d.
Proof.
  intros. unfold nth. induction n.
  + reflexivity.
  + reflexivity.
Qed.

(*

Lemma nth_length_out_of_bound : forall {A} n (ls : list A) d,
  n >= length ls -> nth n ls d = d.
Proof. Admitted.

*)

Definition rev_nth {A : Type} (n:nat) (l:list A) (default:A) : A :=
  if n <? length l
  then nth ((length l) - n - 1) l default
  else default.


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
