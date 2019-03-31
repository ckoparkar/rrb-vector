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


(*

Lemma skipn_cons :
  forall {A : Set} (m : nat) (xs : list A) (x : A),
  length (skipn m (x :: xs)) = length (skipn m xs) + 1.
Proof.
  intros. induction m.
  + simpl. omega.
  + simpl. Admitted.
(* Qed. *)

Lemma length_not_empty_inv {A B : Set} :
  forall (xs : list A) (ys : list B),
  length xs = length ys -> xs <> [] -> ys <> [].
Proof. Admitted.

Lemma length_not_zero_inv {A : Set} :
  forall (xs : list A),  length xs <> 0 -> xs <> [].
Proof.
  intros. induction xs.
  + unfold length in H. congruence.
  + apply (cons_not_empty a xs).
Qed.

Lemma length_zero_inv {A : Set} :
  forall (xs : list A),  length xs = 0 -> xs = [].
Proof.
  intros. induction xs.
  + reflexivity.
  + apply length_zero_iff_nil. apply H.
Qed.

Lemma length_not_zero_inv_inv {A : Set} :
  forall (xs : list A), xs <> [] -> length xs <> 0.
Proof.
  intros. induction xs.
  + congruence.
  + unfold length. apply Nat.neq_succ_0.
Qed.

Lemma skipn_length : forall {A : Set}
  (ls : list A) (n : nat), length (skipn n ls) = length ls - n.
Proof.
  intros. induction ls.
  + simpl. rewrite skipn_nil. reflexivity.
  + rewrite skipn_cons.
Admitted.

Lemma skipn_not_nil : forall {A : Set}
  (ls : list A) (n : nat), n < length ls -> ls <> [] -> skipn n ls <> [].
Proof. Admitted.

*)
