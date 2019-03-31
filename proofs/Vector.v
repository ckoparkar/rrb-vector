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
Inductive tree {A : Set} : Set :=
| Leaf : list size -> list A -> tree
| Node : height -> list size -> list tree -> tree.

(* The type exported out of this module *)
Definition vector {A : Set} := tree (A := A).

(* Well this is technically not correct (Leaf doesn't have sizes), but OK for now. *)
Definition get_sizes {A : Set} (tr : @vector A) : list nat :=
  match tr with
  | Leaf szs _   => szs
  | Node _ szs _ => szs
  end.

Definition get_height {A : Set} (tr : @vector A) : nat :=
  match tr with
  | Leaf _ _    => 0
  | Node ht _ _ => ht
  end.

(* Should these things be written down as specs instead ? *)

Axiom leaf_sizes_elems :
  forall {A : Set} (szs : list size) (ns : list A) (tr : @vector A),
  tr = Leaf szs ns -> length szs = length ns.

Axiom leaf_sizes_elems_m :
  forall {A : Set} (szs : list size) (ns : list A) (tr : @vector A),
  tr = Leaf szs ns -> length ns <= m.

Axiom node_sizes_elems : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
  tr = Node ht szs trs -> length szs = length trs.

Axiom node_sizes_elems_m : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
   tr = Node ht szs trs -> length trs <= m.


(* ---------------------------------- *)
(* -- Common operations               *)
(* ---------------------------------- *)

(* Inefficient, but easier to write proofs. *)
Fixpoint vec_length {A : Set} (tr : @vector A) : nat :=
  match tr with
  | Leaf szs ns  => length szs
  | Node _ _ trs => match trs with
                    | [] => 0
                    | a :: rst =>
                      (* strong_last (a :: rst) (cons_not_nil a rst) *)
                      fold_right (fun t acc => acc + vec_length t) 0 trs
                    end
  end.

Definition empty_vec {A : Set} : (@vector A) := Node 1 [] [].

Definition is_vec_empty {A : Set} (tr : @vector A) : bool :=
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
  let slot     := index_of ht idx in
  let mb_slot' := mb_check_slot (skipn slot (combine szs (seq 0 (length szs)))) slot in
  match mb_slot' with
  | None => None
  | Some slot' => let idx':= idx - (if slot' =? 0
                                    then 0
                                    else nth (slot' - 1) szs 0) in
                  Some (slot', idx')
  end.

Fixpoint get {A : Set} (tr : @vector A) (idx : nat) (default : A) : A :=
  match tr with
  | Leaf _ ns =>
    match (idx , ns) with
    | (0 , n0 :: _)                   => n0
    | (1 , _  :: n1 :: _)             => n1
    | (2 , _  :: _  :: n2 :: _)       => n2
    | (3 , _  :: _  :: _  :: n3 :: _) => n3
    | _ => default
    end
  | Node ht szs trs =>
    match indexInNode ht szs idx  with
    | Some (slot' , idx') =>
      match (slot' , trs) with
      | (_ , [])                        => default
      | (0 , t0 :: _)                   => get t0 idx' default
      | (1 , _  :: t1 :: _)             => get t1 idx' default
      | (2 , _  :: _  :: t2 :: _)       => get t2 idx' default
      | (3 , _  :: _  :: _  :: t3 :: _) => get t3 idx' default
      | _ => default
      end
    | None => default
    end
  end.


Lemma lookup_empty : forall {A : Set} (tr : @vector nat), get empty_vec 0 100 = 100.
Proof. intros. unfold empty_vec. unfold get. simpl. auto. Qed.


(* ---------------------------------- *)
(* -- Insert front/back               *)
(* ---------------------------------- *)

Inductive wherE : Set := Front | Back.

Fixpoint mkLeafAtHeight {A : Set} (ht : height) (v1 : A) : (vector) :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.

Definition join {A : Set} (a : @vector A) (b : @vector A) : (@vector A) :=
  Node (get_height a + 1) [ vec_length a ; (vec_length a + vec_length b) ] [a ; b].

Inductive tmp_pair {A : Set} : Set :=
| P : A -> (@vector A) -> tmp_pair.


Program Fixpoint tryBottom_back {A : Set}
  (v1 : A) (tr : @vector A) {measure (vec_length tr)} : option (@vector A) :=
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
        let node_to_try := strong_last trs _ in
        match tryBottom_back v1 node_to_try with
        | mb_vec => match mb_vec with
                    | Some has_v => let last_sz := strong_last szs _ in
                                    let szs' := removelast szs ++ [1 + last_sz] in
                                    let trs' := removelast trs ++ [has_v] in
                                    Some (Node ht szs' trs')
                    | None =>
                      if length trs <? m
                      then let branch  := mkLeafAtHeight (ht - 1) v1 in
                           let last_sz := strong_last szs _ in
                           let szs'    := szs ++ [1 + last_sz] in
                           let trs'    := trs ++ [branch]
                           in Some (Node ht szs' trs')
                      else None
                    end
        end
      end
    end
  end.
  Admit Obligations.


Fixpoint tryBottom_front {A : Set} (v1 : A) (tr : @vector A) : option (@vector A) :=
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

Definition insert {A : Set} (whr : wherE) (tr : vector) (v : A) : vector :=
  match whr with
  | Front => match tryBottom_front v tr with
             | Some has_v => has_v
             | None       => join (mkLeafAtHeight (get_height tr) v) tr
             end
  | Back  => match tryBottom_back v tr with
             | Some has_v => has_v
             | None       => join tr (mkLeafAtHeight (get_height tr) v)
             end
  end.


Definition cons {A : Set} (tr : vector) (v : A) : vector :=
  insert Front tr v.

Definition snoc {A : Set} (tr : vector) (v : A) : vector :=
  insert Back tr v.


(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Set} (tr : @vector A) (acc : list A) : list A :=
  match tr with
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Set} (tr : @vector A) : list A :=
  go_toList tr [].

Definition fromList {A : Set} (xs : list A) : (@vector A) :=
  fold_left (fun x acc => snoc x acc) xs empty_vec.
