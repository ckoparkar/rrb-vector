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

(*

Definition get' {A : Set} (default : A) : (@vector A) -> nat -> A.
  refine (Fix vec_length_order_wf
           (fun _ => nat -> A)
           (fun (tr : @vector A)
                (get' : forall (tr' : @vector A), vec_length_order tr' tr -> nat -> A) =>
              fun idx =>
              (match tr as tr' return tr = tr' -> A with
               | Leaf _ ns => fun tr_is_leaf =>
                                if idx <? length ns
                                then nth idx ns default
                                else default
               | Node ht szs trs =>
                 fun tr_is_node =>
                 (match trs as trs' return trs = trs' -> A with
                 | [] => fun _ => default
                 | a :: rst =>
                   fun trs_not_nil =>
                     match @indexInNode A ht szs idx  with
                     | Some (slot' , idx') =>
                       let node := strong_nth slot' trs _
                       in get' node _ idx
                     | None => default
                     end
                 end) (eq_refl trs)
               end) (eq_refl tr))).
  (* vec_length_order node tr *)
  + rewrite tr_is_node. apply vec_length_node_elems with ht szs trs.
    reflexivity. rewrite trs_not_nil.
    (* apply (strong_nth_In slot' (a :: rst) node _). *)
  Admitted.

Global Transparent get'.

Definition get {A : Set}
  (tr : @vector A) (idx : nat) (default : A) : A := get' default tr idx.

Definition tryBottom_back {A : Set} (v1 : A) : (@vector A) -> option (@vector A).
  refine (Fix vec_length_order_wf
            (fun _ => option (@vector A))
            (fun (tr : @vector A)
                 (try_bottom_back : forall (tr' : @vector A), vec_length_order tr' tr -> option (@vector A)) =>
               ((match tr as tr' return tr = tr' -> option (@vector A) with
               | Leaf szs ns =>
                 fun _ =>
                 if length ns <? m
                 then Some (Leaf (szs ++ [1]) (ns ++ [v1]))
                 else None
               | Node ht szs trs =>
                 fun tr_is_Node =>
                 (match trs as trs' return trs = trs' -> option (@vector A) with
                  | [] => fun _ => Some (Node ht [1] [mkLeafAtHeight (ht - 1) v1])
                  | t :: ts  =>
                    fun trs_not_nil =>
                      (match szs as szs' return szs = szs' -> option (@vector A) with
                       | [] => fun _ => None
                       | s :: ss =>
                         fun szs_not_nil =>
                           let node_to_try := strong_last trs _ in
                           match try_bottom_back node_to_try _ with
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
                       end) (eq_refl szs)
                  end) (eq_refl trs)
               end) (eq_refl tr) ))).
  Unshelve.
  (* szs <> [] *)
  + rewrite szs_not_nil. apply (cons_not_nil s ss).
  + rewrite szs_not_nil. apply (cons_not_nil s ss).
  (* trs <> [] *)
  + rewrite trs_not_nil. apply (cons_not_nil t ts).
  (* vec_length node_to_try < vec_length trs *)
  + unfold vec_length_order. rewrite tr_is_Node. rewrite trs_not_nil.
    assert (H: In node_to_try (t :: ts)).
    { apply (strong_last_In (t :: ts) node_to_try (cons_not_nil t ts)).
      apply node_to_try. }
    Admitted.

*)


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

(*
Definition strong_last_In {A : Type} : forall (xs : list A) (x : A) (pf : xs <> []),
  x = strong_last xs pf -> In x xs.
Proof.
  intros. unfold strong_last in H. cbv in H. Admitted.

Definition strong_nth_In :
  forall {A : Set} (idx : nat) (xs : list A) (x : A) (pf : idx < length xs),
  x = strong_nth idx xs pf -> In x xs.
Proof. Admitted.

*)

(*

(* Source: http://adam.chlipala.net/cpdt/html/GeneralRec.html *)
Definition vec_length_order {A : Set} (tr1 tr2 : @vector A) :=
  vec_length tr1 < vec_length tr2.

Lemma vec_length_node_elems {A : Set} :
  forall (tr : @vector A) (ht : height) (szs : list size) (trs : list vector) (tr2 : vector),
    tr = Node ht szs trs -> In tr2 trs -> vec_length tr2 < vec_length tr.
  Admitted.

Hint Constructors Acc.

Lemma vec_length_order_wf' :
  forall len, forall A ls, vec_length ls <= len -> Acc (@vec_length_order A) ls.
  unfold vec_length_order; induction len; crush.
Defined.

Theorem vec_length_order_wf {A : Set} : well_founded (@vec_length_order A).
  red; intro; eapply vec_length_order_wf'; eauto.
Defined.

*)

(* Should these things be written down as specs instead ? *)

(*

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

*)
