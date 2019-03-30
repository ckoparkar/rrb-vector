(* An implementation of vectors backed by a Radix-Balanced Tree. *)

Require Import Nat.
Require Import List.
Import ListNotations.
From Coq Require Import Omega.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Wf.

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
(* -- Length                          *)
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

(*

Definition vec_length {A : Set} (tr : @vector A) : nat :=
  match tr with
  | Leaf szs ns  => length szs
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_nil a rst)
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
    - apply cons_not_nil.
Qed.

Lemma vec_length_leaves_sizes {A : Set} :
  forall (tr : vector) (szs : list size) (ns : list A),
    tr = Leaf szs ns -> vec_length tr = length ns.
Proof.
  intros. remember tr as tr'. induction tr.
  + rewrite H. unfold vec_length. apply leaf_sizes_elems with tr'. apply H.
  + congruence.
Qed.

*)


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

Definition indexInNode {A : Set}
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

Program Fixpoint get {A : Set}
  (tr : @vector A) (idx : nat) (default : A) {measure (vec_length tr)} : A :=
  match tr with
  | Leaf _ ns => if idx <? length ns
                 then strong_nth idx ns _
                 else default
  | Node ht szs trs =>
    match trs with
    | [] => default
    | a :: rst => match @indexInNode A ht szs idx  with
                  | Some (slot' , idx') => get (strong_nth slot' trs _) idx' default
                  | None => default
                  end
    end
  end.
   Admit Obligations.

(*

Verified lookup, WIP.

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
  (ht : height) (trs : list (@vector A)) (szs : list size)
  (tr : vector) (tr_node : tr = Node ht szs trs) (szs_not_nil : szs <> []) (idx : nat),
  idx < (@vec_length A tr) -> (nat * nat).
  refine (fun A ht trs szs tr tr_node szs_not_nil idx idx_lt_vec_len =>
            let slot    := index_of ht idx in
            let sz_js_1 := combine szs (seq 0 (length szs)) in
            let sz_js   := skipn slot sz_js_1 in
            (match sz_js as sz_js' return sz_js = sz_js' -> (nat * nat) with
             | [] => fun sz_js_nil => _
             | a :: b =>
               fun _ =>
                 let slot' := check_slot (exist _ (a :: b) (cons_not_nil a b)) idx in
                 let idx' := idx - (if eqb slot' 0
                                    then 0
                                    else strong_nth szs (slot' - 1) _)
                 in (slot' , idx')
             end) (eq_refl sz_js)).
  (* sz_js <> [] *)
  + assert(slot_lt : slot < length (combine szs (seq 0 (length szs)))).
    { rewrite combine_length. rewrite seq_length. rewrite min_eq.
      apply nooo with trs tr. apply tr_node. apply idx_lt_vec_len. }
  (*   assert (length_sz_js_not_O : length sz_js_1 <> 0). *)
  (*   { subst. unfold sz_js_1. rewrite combine_length. rewrite seq_length. *)
  (*     rewrite min_eq. apply length_zero_iff_nil. apply szs_not_nil. } *)
  (*   apply length_not_zero_inv in length_sz_js_not_O. *)
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

*)

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


Program Fixpoint tryBottom_back {A : Set} (tr : @vector A) (v1 : A) {measure (vec_length tr)} : option (@vector A) :=
  match tr with
  | Leaf szs ns =>
    if length ns <? m
    then Some (Leaf (szs ++ [1]) (ns ++ [v1]))
    else None
  | Node ht szs trs =>
    (match trs as trs' return trs = trs' -> option (vector) with
     | [] => fun _ => Some (Node ht [1] [mkLeafAtHeight (ht - 1) v1])
     | t :: ts  =>
       fun trs_not_nil =>
         (match szs as szs' return szs = szs' -> option (vector) with
          | [] => fun _ => None
          | s :: ss =>
            fun szs_not_nil =>
              let node_to_try := strong_last trs (cons_not_nil t ts) in
              match tryBottom_back node_to_try v1 with
              | Some has_v => let last_sz := strong_last szs (cons_not_nil s ss) in
                              let szs' := removelast szs ++ [1 + last_sz] in
                              let trs' := removelast trs ++ [has_v] in
                              Some (Node ht szs' trs')
              | None =>
                if length trs <? m
                then let branch  := mkLeafAtHeight (ht - 1) v1 in
                     let last_sz := strong_last szs (cons_not_nil s ss) in
                     let szs'    := szs ++ [1 + last_sz] in
                     let trs'    := trs ++ [branch]
                     in Some (Node ht szs' trs')
                else None
              end
          end) (eq_refl szs)
     end) (eq_refl trs)
  end.
  Admit Obligations.

Fixpoint tryBottom_front {A : Set} (tr : @vector A) (v1 : A) : option (@vector A) :=
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
         match tryBottom_front node_to_try v1 with
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
  | Front => match tryBottom_front tr v with
             | Some has_v => has_v
             | None       => join (mkLeafAtHeight (get_height tr) v) tr
             end
  | Back  => match tryBottom_back tr v with
             | Some has_v => has_v
             | None       => join tr (mkLeafAtHeight (get_height tr) v)
             end
  end.


Definition cons {A : Set} (tr : vector) (v : A) : vector :=
  insert Front tr v.

Definition snoc {A : Set} (tr : vector) (v : A) : vector :=
  insert Back tr v.


(* ---------------------------------- *)
(* -- Other common operations         *)
(* ---------------------------------- *)

Definition empty_vec {A : Set} : (@vector A) := Node 1 [] [].

Definition is_vec_empty {A : Set} (tr : @vector A) : bool :=
  vec_length tr =? 0.

Fixpoint go_toList {A : Set} (tr : @vector A) (acc : list A) : list A :=
  match tr with
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Set} (tr : @vector A) : list A :=
  go_toList tr [].

Definition fromList {A : Set} (xs : list A) : (@vector A) :=
  fold_left (fun x acc => snoc x acc) xs empty_vec.
