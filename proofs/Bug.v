Require Import List.
Require Import Omega.

Import ListNotations.

Definition strong_head {A : Type} : forall ls : list A, ls <> [] -> A.
  refine (fun (ls : list A) =>
            match ls with
            | []     => fun _ => _
            | a :: _ => fun _ => a
            end).
  (* [] *)
  congruence.
Defined.

Definition this_works : forall (ns : list nat) (idx : nat), (ns <> []) -> nat.
  refine (fun ns idx ns_not_empty =>
            (strong_head ns _) - (strong_head ns _)).
  + apply ns_not_empty.
  + apply ns_not_empty.
Qed.

Definition bug : forall (ns : list nat) (idx : nat), (ns <> []) -> nat.
  refine (fun ns idx ns_not_empty =>
            let x := strong_head ns _ in
            let y := x - (strong_head ns _) in
            y).
  + apply ns_not_empty. Abort.

(* Unshelve *)
Definition bug_fix : forall (ns : list nat) (idx : nat), (ns <> []) -> nat.
  refine (fun ns idx ns_not_empty =>
            let x := strong_head ns _ in
            let y := x - (strong_head ns _) in
            y).
  + Unshelve. apply ns_not_empty. apply ns_not_empty.
Qed.
