Require Import Nat.
Require Import List.
Import ListNotations.

From RRB Require Import Vector.

(* -------------------------------------------------------------------------- *)

Definition tree10 : vector :=
  Node 1 [4 ; 8 ; 10]
       [ Leaf [1 ; 1 ; 1 ; 1] [1 ; 2 ; 3 ; 4]
       ; Leaf [1 ; 1 ; 1 ; 1] [5 ; 6 ; 7 ; 8]
       ; Leaf [1 ; 1]         [9 ; 10]
       ].

Definition tree20 : vector :=
  Node 2 [16 ; 20]
         [ Node 1 [4 ; 8 ; 12 ; 16]
                [ Leaf [1 ; 1 ; 1 ; 1] [1 ; 2 ; 3 ; 4]
                ; Leaf [1 ; 1 ; 1 ; 1] [5 ; 6 ; 7 ; 8]
                ; Leaf [1 ; 1 ; 1 ; 1] [9 ; 10 ; 11 ; 12]
                ; Leaf [1 ; 1 ; 1 ; 1] [13 ; 14 ; 15 ; 16]
                ]
         ; Node 1 [4]
                [ Leaf [1 ; 1 ; 1 ; 1] [17 ; 18 ; 19 ; 20]
                ]
       ].

Definition tree_ub : vector :=
  Node 2 [9 ; 21]
         [ Node 1 [3 ; 6 ; 9]
                [ Leaf [1 ; 1 ; 1] [1 ; 2 ; 3]
                ; Leaf [1 ; 1 ; 1] [4 ; 5 ; 6]
                ; Leaf [1 ; 1 ; 1] [7 ; 8 ; 9]
                ]
         ; Node 1 [3 ; 6 ; 10 ; 12]
                [ Leaf [1 ; 1 ; 1]     [10 ; 11 ; 12]
                ; Leaf [1 ; 1 ; 1]     [13 ; 14 ; 15]
                ; Leaf [1 ; 1 ; 1 ; 1] [16 ; 17 ; 18 ; 19]
                ; Leaf [1 ; 1]         [20 ; 21]
                ]
       ].

Definition tree_ub2 : vector :=
  Node 1 [1 ; 3 ; 6 ; 10]
         [ Leaf [1]             [1]
         ; Leaf [1 ; 1]         [2 ; 3]
         ; Leaf [1 ; 1 ; 1]     [4 ; 5 ; 6]
         ; Leaf [1 ; 1 ; 1 ; 1] [7 ; 8 ; 9 ; 10]
         ].


Definition tree_ub3 : vector :=
  Node 1 [1 ; 2 ; 3 ; 4]
       [ Leaf [1] [1]
       ; Leaf [1] [2]
       ; Leaf [1] [3]
       ; Leaf [1] [4]
       ].

Definition tree17 : vector :=
  Node 2 [16 ; 17]
         [ Node 1 [4 ; 8 ; 12 ; 16]
                [ Leaf [1 ; 1 ; 1 ; 1] [1 ; 2 ; 3 ; 4]
                ; Leaf [1 ; 1 ; 1 ; 1] [5 ; 6 ; 7 ; 8]
                ; Leaf [1 ; 1 ; 1 ; 1] [9 ; 10 ; 11 ; 12]
                ; Leaf [1 ; 1 ; 1 ; 1] [13 ; 14 ; 15 ; 16]
                ]
         ; Node 1 [1]
                [ Leaf [1] [17] ]
       ].

Definition tree17_cons : vector :=
  Node 2 [1 ; 17]
         [ Node 1 [1] [ Leaf [1] [17] ]
         ; Node 1 [4 ; 8 ; 12 ; 16]
                  [ Leaf [1 ; 1 ; 1 ; 1] [1 ; 2 ; 3 ; 4]
                  ; Leaf [1 ; 1 ; 1 ; 1] [5 ; 6 ; 7 ; 8]
                  ; Leaf [1 ; 1 ; 1 ; 1] [9 ; 10 ; 11 ; 12]
                  ; Leaf [1 ; 1 ; 1 ; 1] [13 ; 14 ; 15 ; 16]
                  ]
         ].

Definition test1 : toList tree10 = (seq 1 10).
Proof. reflexivity. Qed.

Definition test2 : toList tree20 = (seq 1 20).
Proof. reflexivity. Qed.

Definition test3 : fromList (seq 1 10) = tree10.
Proof. reflexivity. Qed.

Definition test4 : fromList (seq 1 20) = tree20.
Proof. reflexivity. Qed.

Definition test5 : vec_length tree10 = 10.
Proof. reflexivity. Qed.

Definition test6 : vec_length tree20 = 20.
Proof. reflexivity. Qed.

Definition test7 : get (fromList (seq 1 10)) 0 100 = 1.
Proof. reflexivity. Qed.

Definition test8 : get (fromList (seq 1 10)) 9 100 = 10.
Proof. reflexivity. Qed.

Definition test9 : get (fromList (seq 1 10)) 10 100 = 100.
Proof. reflexivity. Qed.

Definition test10 : cons (fromList (seq 1 16)) 17 = tree17_cons.
Proof. reflexivity. Qed.

Definition test11 : snoc (fromList (seq 1 16)) 17 = tree17.
Proof. reflexivity. Qed.

Definition test12 : vec_length (fromList (seq 1 16)) = 16.
Proof. reflexivity. Qed.

Definition test13 : vec_length (@empty_vec nat) = 0.
Proof. reflexivity. Qed.

Definition test14 : get (@empty_vec nat) 0 100 = 100.
Proof. reflexivity. Qed.

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
