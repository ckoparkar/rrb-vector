Require Import Nat.
Require Import List.
Import ListNotations.

From RRB Require Import Vector3.

(* -------------------------------------------------------------------------- *)

Definition tree10 : tree nat :=
  Node 1 [10 ; 8 ; 4]
       [ Leaf [2 ; 1]         [10 ; 9]
       ; Leaf [4 ; 3 ; 2 ; 1] [8 ; 7 ; 6 ; 5]
       ; Leaf [4 ; 3 ; 2 ; 1] [4 ; 3 ; 2 ; 1]
       ].

Definition tree20 : tree nat :=
  Node 2 [20 ; 16]
         [ Node 1 [4]
                [ Leaf [4 ; 3 ; 2 ; 1] [20 ; 19 ; 18 ; 17]
                ]
         ; Node 1 [16 ; 12 ; 8 ; 4]
                [ Leaf [4 ; 3 ; 2 ; 1] [16 ; 15 ; 14 ; 13]
                ; Leaf [4 ; 3 ; 2 ; 1] [12 ; 11 ; 10 ; 9]
                ; Leaf [4 ; 3 ; 2 ; 1] [8 ; 7 ; 6 ; 5]
                ; Leaf [4 ; 3 ; 2 ; 1] [4 ; 3 ; 2 ; 1]
                ]
       ].

Definition tree17 : tree nat :=
  Node 2 [17 ; 16]
         [ Node 1 [1]
                [ Leaf [1] [17] ]
         ; Node 1 [16 ; 12 ; 8 ; 4]
                [ Leaf [4 ; 3 ; 2 ; 1] [16 ; 15 ; 14 ; 13]
                ; Leaf [4 ; 3 ; 2 ; 1] [12 ; 11 ; 10 ; 9]
                ; Leaf [4 ; 3 ; 2 ; 1] [8 ; 7 ; 6 ; 5]
                ; Leaf [4 ; 3 ; 2 ; 1] [4 ; 3 ; 2 ; 1]
                ]
       ].

Definition test1 : toList tree10 = (seq 1 10).
Proof. reflexivity. Qed.

Definition test2 : toList tree20 = (seq 1 20).
Proof. reflexivity. Qed.

Definition test3 : fromList (seq 1 10) = tree10.
Proof. reflexivity. Qed.

Compute (fromList (seq 1 20)).

Definition test4 : fromList (seq 1 20) = tree20.
Proof. reflexivity. Qed.

Definition test5 : vec_length tree10 = 10.
Proof. reflexivity. Qed.

Definition test6 : vec_length tree20 = 20.
Proof. reflexivity. Qed.

Definition test7 : get 0 (fromList (seq 1 10)) 100 = 1.
Proof. reflexivity. Qed.

Definition test8 : get 9 (fromList (seq 1 10)) 100 = 10.
Proof. reflexivity. Qed.

Definition test9 : get 10 (fromList (seq 1 10)) 100 = 100.
Proof. reflexivity. Qed.

(*
Definition test10 : cons (fromList (seq 1 16)) 17 = tree17_cons.
Proof. reflexivity. Qed.
*)

Definition test11 : snoc (fromList (seq 1 16)) 17 = tree17.
Proof. reflexivity. Qed.

Definition test12 : vec_length (fromList (seq 1 16)) = 16.
Proof. reflexivity. Qed.

Definition test13 : @vec_length nat E = 0.
Proof. reflexivity. Qed.

Definition test14 : get 0 E 100 = 100.
Proof. reflexivity. Qed.

(*
Lemma tree10_isRRB : @is_RRB nat tree10.
Proof.
  apply Inv1.
  + simpl. reflexivity.
  + simpl. auto.
Qed.

Lemma empty_isRRB : @is_RRB nat empty_vec.
Proof.
  apply Inv1.
  + simpl. reflexivity.
  + simpl. unfold m. auto.
Qed.
*)
