(* An implementation of vectors backed by a Radix-Balanced Tree. *)

Require Import Nat.
Require Import List.
Import ListNotations.
From Coq Require Import Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Wf.
From Coq Require Import Bool.Bool.

From RRB Require Import Prelude.
From RRB Require Import Crush.


(* -------------------------------------------------------------------------- *)

(* Branching factor *)
Definition m := 4.

Definition log2m := log2 m.

Definition mask := m - 1.

(* Useful type synonyms *)
Definition height := nat.
Definition size := nat.

(* The main datatype. *)
Inductive tree {A : Type} : Type :=
| Leaf : list size -> list A -> tree
| Node : height -> list size -> list tree -> tree.

(* The type exported out of this module *)
Definition vector1 {A : Type} := tree (A := A).

(* Well this is technically not correct (Leaf doesn't have sizes), but OK for now. *)
Definition get_sizes {A : Type} (tr : @vector1 A) : list nat :=
  match tr with
  | Leaf szs _   => szs
  | Node _ szs _ => szs
  end.

Definition get_height {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | Leaf _ _    => 0
  | Node ht _ _ => ht
  end.

Definition get_elems_len {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | Leaf _ ns    => length ns
  | Node _ _ trs => length trs
  end.

Definition get_sizes_len {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | Leaf szs _   => length szs
  | Node _ szs _ => length szs
  end.

(* ---------------------------------- *)
(* -- Invariants                      *)
(* ---------------------------------- *)

(* Most likely, this single invariant is not going to be enough.
   I'll update this type as I start writing proofs. *)
Inductive is_RRB {A : Type} : @vector1 A -> Prop :=
| Inv1 :
    forall v, get_sizes_len v = get_elems_len v -> get_sizes_len v < m -> is_RRB v.

(* ---------------------------------- *)
(* -- Common operations               *)
(* ---------------------------------- *)

(* Inefficient, but easier to write proofs. *)
Fixpoint vec_length {A : Type} (tr : @vector1 A) : nat :=
  match tr with
  | Leaf szs ns  => length szs
  | Node _ _ trs => match trs with
                    | [] => 0
                    | a :: rst =>
                      (* strong_last (a :: rst) (cons_not_nil a rst) *)
                      fold_right (fun t acc => acc + vec_length t) 0 trs
                    end
  end.

Definition empty_vec {A : Type} : (@vector1 A) := Node 1 [] [].

Definition is_vec_empty {A : Type} (tr : @vector1 A) : bool :=
  vec_length tr =? 0.


(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : height) (i : nat) : nat :=
  (i / (m ^ ht)) mod m.

Fixpoint mb_check_slot
  (sz_js : list (nat * nat)) (idx : nat) : option nat :=
  match sz_js with
  | [] => None
  | (sz , j) :: rst => if sz <? idx
                       then mb_check_slot rst idx
                       else Some j
  end.

Definition indexInNode
  (ht : height) (szs : list size) (idx : nat) : option (nat * nat) :=
  match szs with
  | [] => None
  | _  =>
    let slot     := index_of ht idx in
    let mb_slot' := mb_check_slot (skipn slot (combine szs (seq 0 (length szs)))) slot in
    match mb_slot' with
    | None => None
    | Some slot' => let idx':= idx - (if slot' =? 0
                                      then 0
                                      else nth (slot' - 1) szs 0) in
                    Some (slot', idx')
    end
  end.

Fixpoint get {A : Type} (idx : nat) (tr : vector1) (default : A) : A :=
  match tr with
  | Leaf _ ns =>
    match (idx , ns) with
    | (0 , n0 :: _)                   => n0
    | (1 , _  :: n1 :: _)             => n1
    | (2 , _  :: _  :: n2 :: _)       => n2
    | (3 , _  :: _  :: _  :: n3 :: _) => n3
    | _                               => default
    end
  | Node ht szs trs =>
    match indexInNode ht szs idx  with
    | Some (slot' , idx') =>
      match (slot' , trs) with
      | (_ , [])                        => default
      | (0 , t0 :: _)                   => get idx' t0 default
      | (1 , _  :: t1 :: _)             => get idx' t1 default
      | (2 , _  :: _  :: t2 :: _)       => get idx' t2 default
      | (3 , _  :: _  :: _  :: t3 :: _) => get idx' t3 default
      | _                               => default
      end
    | None => default
    end
  end.

Lemma get_empty : forall {A : Type} (tr : @vector1 A), get 0 empty_vec 100 = 100.
Proof. intros. unfold empty_vec. unfold get. simpl. auto. Qed.

(* ---------------------------------- *)
(* -- Update                          *)
(* ---------------------------------- *)


(* ---------------------------------- *)
(* -- Insert front/back               *)
(* ---------------------------------- *)

Inductive wherE : Set := Front | Back.

Fixpoint mkLeafAtHeight {A : Type} (ht : height) (v1 : A) : (vector1) :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.


Definition join {A : Type} (a : @vector1 A) (b : @vector1 A) : (@vector1 A) :=
  Node (get_height a + 1) [ vec_length a ; (vec_length a + vec_length b) ] [a ; b].


Fixpoint tryBottom_back {A : Type}
  (fuel : nat) (v1 : A) (tr : @vector1 A) {struct fuel} : option (@vector1 A) :=
  match tr with
  | Leaf szs ns =>
    if length ns <? m
    then Some (Leaf (szs ++ [1]) (ns ++ [v1]))
    else None
  | Node ht szs trs =>
    match trs with
    | [] => Some (Node ht [1] [mkLeafAtHeight (ht - 1) v1])
    | t :: ts  =>
      match szs with
      | [] => None
      | s :: ss =>
        let node_to_try := last ts t in
        match fuel with
        | O => None
        | S n =>
          match tryBottom_back n v1 node_to_try with
          | mb_vec => match mb_vec with
                      | Some has_v => let last_sz := last ss s in
                                      let szs' := removelast szs ++ [1 + last_sz] in
                                      let trs' := removelast trs ++ [has_v] in
                                      Some (Node ht szs' trs')
                      | None =>
                        if length trs <? m
                        then let branch  := mkLeafAtHeight (ht - 1) v1 in
                             let last_sz := last ss s in
                             let szs'    := szs ++ [1 + last_sz] in
                             let trs'    := trs ++ [branch]
                             in Some (Node ht szs' trs')
                        else None
                      end
          end
        end
      end
    end
  end.


Fixpoint tryBottom_front {A : Type} (v1 : A) (tr : @vector1 A) : option (@vector1 A) :=
  match tr with
  | Leaf szs ns =>
    if length ns <? m
    then Some (Leaf (1 :: szs) (v1 :: ns))
    else None
  | Node ht szs trs =>
    match trs with
     | [] => Some (Node ht [1] [mkLeafAtHeight (ht - 1) v1])
     | t :: ts  =>
       match szs with
       | [] => None
       | s :: ss =>
         let node_to_try := t in
         match tryBottom_front v1 node_to_try with
         | Some has_v => let szs' := (1 + s) :: ss in
                         let trs' := has_v :: ts in
                         Some (Node ht szs' trs')
         | None =>
           if length trs <? m
           then let branch := mkLeafAtHeight (ht - 1) v1 in
                let szs'   := 1 :: (map (fun x => x + 1) szs) in
                let trs'   := branch :: trs
                in Some (Node ht szs' trs')
           else None
         end
       end
    end
  end.

Definition insert {A : Type} (whr : wherE) (tr : vector1) (v : A) : vector1 :=
  match whr with
  | Front => match tryBottom_front v tr with
             | Some has_v => has_v
             | None       => join (mkLeafAtHeight (get_height tr) v) tr
             end
  (* tryBottom_back should only need (log tr) fuel, so this should be enough. *)
  | Back  => match tryBottom_back (vec_length tr) v tr with
             | Some has_v => has_v
             | None       => join tr (mkLeafAtHeight (get_height tr) v)
             end
  end.


Definition cons {A : Type} (tr : vector1) (v : A) : vector1 :=
  insert Front tr v.

Definition snoc {A : Type} (tr : vector1) (v : A) : vector1 :=
  insert Back tr v.

(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Type} (tr : @vector1 A) (acc : list A) : list A :=
  match tr with
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Type} (tr : @vector1 A) : list A :=
  go_toList tr [].

Definition fromList {A : Type} (xs : list A) : (@vector1 A) :=
  fold_left (fun acc x => snoc acc x) xs empty_vec.

(* ---------------------------------- *)
(* -- concat                          *)
(* ---------------------------------- *)

Definition concat {A : Type} (a : @vector1 A) (b : @vector1 A) : @vector1 A :=
  fold_left (fun acc x => snoc acc x) (toList b) a.

(* ---------------------------------- *)
(* -- Theorems                        *)
(* ---------------------------------- *)

Lemma prop_length : forall ls : list nat, length ls = vec_length (fromList ls).
Proof. Admitted.

Lemma prop_fromList_toList_inv : forall ls : list nat, toList (fromList ls) = ls.
Proof. Admitted.

Lemma prop_get_ordered_list :
  forall n m, n > 1 -> m <= n -> get m (fromList (seq 1 n)) 100 = m+1.
Proof. Admitted.

Lemma prop_get_insert :
  forall (m : nat), get 0 (cons empty_vec m) 100 = m.
Proof. intros. simpl. reflexivity. Qed.

(* These are the quickcheck properties I wrote down for Assignment1.
   I'm going to at least try to prove O(..) bounds, like we did for
   RedBlack trees in class. *)


(* ---------------------------------- *)
(* -- Abs                             *)
(* ---------------------------------- *)

Inductive Abs {A : Type} : @vector1 A -> (list A) -> Prop :=
| Abs_E : Abs empty_vec []
| Abs_C: forall a b l v r,
      Abs l a ->
      Abs r b ->
      Abs (snoc (concat l r) v) (snoc_list (a ++ b) v).

Theorem get_relate:
  forall {A : Type} n v1 v2 d,
    Abs v1 v2 -> @get A n v1 d = nth n v2 d.
Proof.
  intros. induction H.
  + simpl ; destruct n ; reflexivity.
  + Admitted.
