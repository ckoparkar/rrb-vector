(* An implementation of vectors backed by a Radix-Balanced Tree. *)

Require Import Nat.
Require Import List.
Import ListNotations.
From Coq Require Import Omega.
From Coq Require Import Logic.FunctionalExtensionality.

From RRB Require Import Prelude.

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

(* ---------------------------------- *)
(* -- Other common operations         *)
(* ---------------------------------- *)

Definition vec_length {A : Set} (tr : @vector A) : nat :=
  match tr with
  | Leaf szs ns  => length szs
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_empty a rst)
                    end
  end.

Lemma vec_length_sizes {A : Set} :
  forall (tr : vector),  (vec_length tr > 0) -> (@get_sizes A tr) <> [].
Proof.
  intros. induction tr.
  + unfold vec_length in H. unfold get_sizes.
    apply length_gt_zero_iff_not_nil. apply H.
  + unfold get_sizes. unfold vec_length in H.
    induction l.
    - apply zero_gt_zero_false in H. unfold not. intro. apply H.
    - apply cons_not_empty.
Qed.

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

Lemma vec_length_leaves_sizes {A : Set} :
  forall (tr : vector) (szs : list size) (ns : list A),
    tr = Leaf szs ns -> vec_length tr = length ns.
Proof.
  intros. remember tr as tr'. induction tr.
  + rewrite H. unfold vec_length. apply leaf_sizes_elems with tr'. apply H.
  + congruence.
Qed.

(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : height) (i : nat) : nat :=
  (i / (m ^ ht)) mod m.

Lemma index_of_lt_m {A : Set} : forall (ht i : nat), m > 0 -> index_of ht i < m.
Proof.
  intros. unfold index_of. unfold modulo. destruct m.
  + apply H.
  + omega.
Qed.

Axiom nooo : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A) (idx : nat),
  (tr = Node ht szs trs) -> (idx < vec_length tr) -> index_of ht idx < length szs.

Fixpoint check_slot_default
  (sz_js : list (nat * nat)) (idx : nat) (default : nat) : nat :=
  match sz_js with
  | [] => default
  | (sz , j) :: rst => if sz <? idx
                       then check_slot_default rst idx j
                       else j
  end.

Definition check_slot' :
  forall (sz_js : list (nat * nat)) (idx : nat), sz_js <> [] -> nat.
  refine (fix f (sz_js : list (nat * nat)) (idx : nat) :=
              match sz_js with
              | [] => fun pf  => _
              | (sz , j) :: rst =>
                  fun _ => check_slot_default rst idx j
              end).
    congruence.
Defined.

Definition check_slot
  (s : { sz_js : list (nat * nat) | sz_js <> [] }) (idx : nat) : nat :=
  check_slot' (proj1_sig s) idx (proj2_sig s).

(*

Want to prove:

    (1) slot = index_of ht idx and slot < length szs

    (2) slot' = check_slot sz_js idx and slot' < length szs

We know:

    (1) forall tr = Node ht szs trs, length szs = length trs.

*)

Definition indexInNode : forall {A : Set}
  (tr : vector) (ht : height) (szs : list size) (idx : nat),
  idx < (@vec_length A tr) -> (nat * nat).
  refine (fun A tr ht szs idx idx_lt_vec_len =>
            let slot  := index_of ht idx in
            let sz_js := skipn slot (combine szs (seq 0 (length szs))) in
            match sz_js with
            | [] => _
            | a :: b => let slot' := check_slot (exist _ (a :: b) (cons_not_empty a b)) idx in
                        let idx' := idx - (if eqb slot' 0
                                           then 0
                                           else strong_nth szs (slot' - 1) _)
                        in (slot' , idx')
            end).
  Admitted.

Definition get {A : Set}
   (tr : vector) (s : { idx : nat | (idx < @vec_length A tr) }) (default : A) : A.
  refine ((match tr as tr' return tr = tr' -> A with
           | Leaf szs ns => match s with
                            | exist _ idx pf => fun tr => strong_nth ns idx _
                            end
           | Node ht szs trs => fun _ => default
           end) (eq_refl tr)).
  (* tr = Leaf .. *)
  + rewrite vec_length_leaves_sizes with _ szs ns in pf.
    - apply pf.
    - apply tr.
Defined.

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

Lemma length_not_empty_inv {A B : Set} :
  forall (xs : list A) (ys : list B),
  length xs = length ys -> xs <> [] -> ys <> [].
Proof. Admitted.


Definition tryBottom : forall {A : Set}
  (whr : wherE) (tr : @vector A) (v1 : A), option (@vector A).
  refine
    (fix f {A : Set} (whr : wherE) (tr : @vector A) (v1 : A) : option (@vector A) :=
       ((match tr as tr' return tr = tr' -> option (vector) with
         | Leaf szs ns =>
           if length ns <? m
           then match whr with
                | Front => fun _ => Some (Leaf (1 :: szs) (v1 :: ns))
                | Back  => fun _ => Some (Leaf (szs ++ [1]) (ns ++ [v1]))
                end
           else fun _ => None
         | Node ht szs trs =>
           fun pf_tr =>
             (match trs as trs' return trs = trs' -> option (vector) with
              | [] => fun _ => Some (Node ht [1] [mkLeafAtHeight (ht - 1) v1])
              | hd :: rst  =>
                fun pf_trs' =>
                  let node_to_try := match whr with
                                     | Front => strong_head trs _
                                     | Back  => strong_last trs _
                                     end in
                  (* If we recur on node_to_try, it upsets Coq's termination checker *)
                  match (f whr hd v1) with
                  | Some has_v =>
                    match whr with
                    | Front => let hd_szs := strong_head szs _ in
                               let tl_szs := tl szs in
                               let szs'   := (1 + hd_szs) :: tl_szs in
                               let trs'   := has_v :: tl trs in
                               Some (Node ht szs' trs')
                    | Back  => let last_szs := strong_last szs _ in
                               let szs'     := removelast szs ++ [1 + last_szs] in
                               let trs'     := removelast trs ++ [has_v] in
                               Some (Node ht szs' trs')
                    end
                  | None =>
                    if length trs <? m
                    then let branch := mkLeafAtHeight (ht - 1) v1 in
                         let szs'   := (match whr with
                                        | Front => 1 :: (map (fun x => x + 1) szs)
                                        | Back  => let last_szs := strong_last szs _ in
                                                   szs ++ [1 + last_szs]
                                        end) in
                         let trs'   := (match whr with
                                        | Front => branch :: trs
                                        | Back  => trs ++ [branch]
                                        end) in
                         Some (Node ht szs' trs')
                    else None
                  end
              end) (eq_refl trs)
         end) (eq_refl tr))).
  Unshelve.
  (* when tryBottom succeeds, szs <> [] *)
  + apply length_not_empty_inv with (hd :: rst).
    rewrite node_sizes_elems with ht szs (hd :: rst) tr. auto.
    rewrite <- pf_trs'. apply pf_tr. apply (cons_not_empty hd rst).
  + apply length_not_empty_inv with (hd :: rst).
    rewrite node_sizes_elems with ht szs (hd :: rst) tr. auto.
    rewrite <- pf_trs'. apply pf_tr. apply (cons_not_empty hd rst).
  + apply length_not_empty_inv with (hd :: rst).
    rewrite node_sizes_elems with ht szs (hd :: rst) tr. auto.
    rewrite <- pf_trs'. apply pf_tr. apply (cons_not_empty hd rst).
  (* node_to_try => trs <> [] *)
  + rewrite pf_trs'. apply (cons_not_empty hd rst).
  + rewrite pf_trs'. apply (cons_not_empty hd rst).
Qed.

Definition insert {A : Set} (whr : wherE) (tr : vector) (v : A) : vector :=
  match tryBottom whr tr v with
  | Some has_v => has_v
  | None => match whr with
            | Front => join (mkLeafAtHeight (get_height tr) v) tr
            | Back  => join tr (mkLeafAtHeight (get_height tr) v)
            end

  end.
