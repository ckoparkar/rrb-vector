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
         [ Node 1 [4 ; 8 ; 10]
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

Compute (toList (fromList (seq 1 17))).
