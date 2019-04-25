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
Definition M := 4.

(* The main datatype. *)
Inductive tree (A : Type) : Type :=
| E    : tree A
| Leaf : list nat -> list A -> tree A
| Node : nat -> list nat -> list (tree A) -> tree A.

Arguments E    {A}.
Arguments Leaf {A}.
Arguments Node {A}.

Print tree_ind.


(* See Nested Induction Types under:

  http://adam.chlipala.net/cpdt/html/InductiveTypes.html *)

Section tree_ind'.
  Variable A : Type.
  Variable P : (tree A) -> Prop.

  Hypothesis E_case : P E.

  Hypothesis Leaf_case : forall (szs : list nat) (ls : list A),
    P (Leaf szs ls).

  Hypothesis Node_case : forall (ht : nat) (szs : list nat) (ls : list (tree A)),
    Forall P ls -> P (Node ht szs ls).

  Fixpoint tree_ind' (tr : tree A) : P tr :=
    match tr with
      | E => E_case
      | Leaf szs ls => Leaf_case szs ls
      | Node ht szs ls => Node_case ht szs ls
        ((fix list_tree_ind (ls : list (tree A)) : Forall P ls :=
          match ls with
            | [] => Forall_nil P
            | tr' :: rest => Forall_cons tr' (tree_ind' tr') (list_tree_ind rest)
          end) ls)
    end.
End tree_ind'.

Print tree_ind'.


(* The type exported out of this module *)
Definition vector1 (A : Type) := tree A.


(* Upper bound on the #elems in a tree of height h *)
Definition vec_capacity {A : Type} (tr : tree A) : nat :=
  match tr with
  | E           => 0
  | Leaf _ _    => M
  | Node ht _ _ => M ^ (ht + 1)
  end.

Definition get_height {A : Type} (tr : tree A) : nat :=
  match tr with
  | E           => 0
  | Leaf _ _    => 0
  | Node ht _ _ => ht
  end.


(* ---------------------------------- *)
(* -- Invariant datatype              *)
(* ---------------------------------- *)

Inductive is_RRB {A : Type} : tree A -> Prop :=
| Inv1 : forall (ht : nat) (szs : list nat) (ns : list (tree A)) (tr : tree A),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns < M -> length szs < M
    -> is_RRB (Node ht szs ns)
| Inv2 : forall (szs : list nat) (ns : list A) (tr : tree A),
    ns <> [] -> szs <> [] -> ~ (In 0 szs)
    -> length ns < M -> length szs < M
    -> is_RRB (Leaf szs ns).

Lemma node_elems_not_nil' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> ns <> [].
Proof. intros. inversion H. subst. apply H3. Qed.

Lemma node_szs_not_nil' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> szs <> [].
Proof. intros. inversion H. subst. apply H4. Qed.

Lemma node_zero_not_in_szs' :
  forall {A : Type} (ht : nat) (szs : list nat) (ns : list (tree A)),
    is_RRB (Node ht szs ns) -> ~ (In 0 szs).
Proof. intros. inversion H. subst. apply H5. Qed.

Lemma leaf_elems_not_nil' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> ns <> [].
Proof. intros. inversion H. subst. apply H2. Qed.

Lemma leaf_szs_not_nil' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> szs <> [].
Proof. intros. inversion H. subst. apply H3. Qed.

Lemma leaf_zero_not_in_szs' :
  forall {A : Type} (szs : list nat) (ns : list A),
    is_RRB (Leaf szs ns) -> ~ (In 0 szs).
Proof. intros. inversion H. subst. apply H4. Qed.

(*

Axiom leaf_elems_M :
  forall {A : Type} (szs : list size) (ns : list A) (tr : tree A),
v    tr = Leaf szs ns -> length ns <= M.

Axiom leaf_sizes_elems :
  forall {A : Set} (szs : list size) (ns : list A) (tr : @vector A),
  tr = Leaf szs ns -> length szs = length ns.

Axiom node_sizes_elems : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
   tr = Node ht szs trs -> length szs = length trs.

Axiom node_sizes_elems_m : forall {A : Set}
  (ht : nat) (szs : list size) (trs : list (@vector A)) (tr : @vector A),
tr = Node ht szs trs -> length trs <= m.

*)


(* ---------------------------------- *)
(* -- Length                          *)
(* ---------------------------------- *)

Definition vec_length {A : Type} (tr : tree A) : nat :=
  match tr with
  | E => 0
  | Leaf szs ns  => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_nil a rst)
                    end
  | Node _ szs _ => match szs with
                    | [] => 0
                    | a :: rst => strong_last (a :: rst) (cons_not_nil a rst)
                    end
  end.

Lemma vec_length_0_E : forall A vec,
  is_RRB vec -> @vec_length A vec = 0 <-> vec = E.
Proof.
  intros. split.
  (* -> *)
  + induction vec using tree_ind'.
    - reflexivity.
    - unfold vec_length. intro.
      destruct szs eqn:szs'.
      * assert (H2: szs <> []).
        { subst. apply (leaf_szs_not_nil' [] ls H). }
        contradiction.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        { apply last_not_In.
          apply (leaf_zero_not_in_szs' (n :: l) ls H). }
        contradiction.
    - unfold vec_length. intro. destruct szs eqn:szs'.
      * assert (H2: szs <> []).
        { subst. apply (node_szs_not_nil' ht [] ls H). }
        contradiction.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        { apply last_not_In.
          apply (node_zero_not_in_szs' ht (n :: l) ls H). }
        contradiction.
  (* <-  *)
  + intro. rewrite H0. unfold vec_length. reflexivity.
Qed.


(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : nat) (i : nat) : nat := (i / (M ^ ht)) mod M.

Lemma mod_lt : forall n, n mod M < M.
Proof. intros. unfold modulo, M. omega. Qed.

Lemma index_of_lt_M : forall ht i, index_of ht i < M.
Proof. intros. unfold index_of, M. apply mod_lt. Qed.

Fixpoint get {A : Type} (idx : nat) (tr : tree A) (default : A) : A :=
  match tr with
  | E => default
  | Leaf _ ns =>
    (* Need to prove: (slot' < length ns) *)
    let slot' := index_of 0 idx in
    nth slot' ns default
  | Node ht szs trs =>
    let slot' := index_of ht idx in
    (* Need to prove: (slot' < length trs) *)
    match (slot' , trs) with
    | (0 , t0 :: [])                   => get idx t0 default
    | (1 , t0 :: t1 :: [])             => get idx t1 default
    | (2 , t0 :: t1 :: t2 :: [])       => get idx t2 default
    | (3 , t0 :: t1 :: t2 :: t3 :: []) => get idx t3 default
    | _                                => default
    end
  end.


(* ---------------------------------- *)
(* -- Snoc                            *)
(* ---------------------------------- *)

Fixpoint mkLeafAtHeight {A : Type} (ht : nat) (v1 : A) : tree A :=
  match ht with
  | O => Leaf [1] [v1]
  | S n => Node ht [1] [mkLeafAtHeight n v1]
  end.


Definition join {A : Type} (a : tree A) (b : tree A) : (tree A) :=
  Node (get_height a + 1) [ vec_length a ; (vec_length a + vec_length b) ] [a ; b].


Definition vec_has_space_p {A : Type} (tr : tree A) : bool :=
  match tr with
  | E             => true
  | Leaf _ ns     => length ns <? M
  | Node ht szs _ =>
    match szs with
    | [] => true
    | sz :: rst =>
      let last_sz := last rst sz in
      last_sz <? vec_capacity tr
    end
  end.


Fixpoint snoc_Bottom
  {A : Type} (fuel : nat) (tr : tree A) (v1 : A) : option (tree A) :=
  match tr with
  | E => Some (Node 1 [1] [Leaf [1] [v1]])

  | Leaf [] ns => Some (Leaf [1] [v1])

  (* We don't check if (length ns) < M here, but do it before recurring
     in the Node case. *)
  | Leaf (sz :: rst) ns =>
    let last_sz := last rst sz in
    Some (Leaf ((sz :: rst) ++ [last_sz + 1]) (ns ++ [v1]))

  | Node ht szs trs =>
    match fuel with
    (* This value will never be None. Should I try to prove it to Coq? *)
    | 0   => None
    | S n =>
      match (szs, trs) with
      | (sz :: ss, tr :: ts) =>
        let last_tr := strong_last (tr :: ts) (cons_not_nil tr ts) in
        if vec_has_space_p last_tr
        then let last_sz := strong_last (sz :: ss) (cons_not_nil sz ss) in
             let szs'    := removelast szs in
             let trs'    := removelast trs in
             match snoc_Bottom n last_tr v1 with
             | Some snocd => Some (Node ht (szs' ++ [last_sz + 1]) (trs' ++ [snocd]))
             (* This value will never be None. Should I try to prove it to Coq? *)
             | None => None
             end
        else
          let branch  := mkLeafAtHeight (ht - 1) v1 in
          let last_sz := last ss sz in
          let szs'    := szs ++ [1 + last_sz] in
          let trs'    := trs ++ [branch]
          in Some (Node ht szs' trs')

      | _ => None
      end
    end
  end.

Fixpoint snoc {A : Type} (tr : tree A) (v : A) : tree A :=
  if vec_has_space_p tr
  then  match snoc_Bottom (vec_length tr) tr v with
        | Some tr2 => tr2
        | None => E
        end
  else join tr (mkLeafAtHeight (get_height tr) v).

Lemma snoc_Bottom_Some :
  forall {A : Type} (tr : tree A) (v : A),
  exists fuel tr2, snoc_Bottom fuel tr v = Some tr2.
Proof.
  intros. destruct tr eqn:tr'.
  + exists 0. exists (Node 1 [1] [(Leaf [1] [v])]). reflexivity.
  + destruct l eqn:l'.
    - exists 0. exists (Leaf [1] [v]). unfold snoc_Bottom.
      reflexivity.
    - exists 0.
      exists (Leaf (l ++ [(last l1 n) + 1]) (l0 ++ [v])).
      simpl. subst. reflexivity.
  + exists 1. econstructor. unfold snoc_Bottom. simpl.
    destruct l eqn:l'.
    (* Impossible case. *)
    - admit.
    - destruct l0 eqn:l0'.
      (* Impossible case. *)
      * admit.
      * destruct (vec_has_space_p (last l2 t)) eqn:vec_has_space.
        ++ Admitted.

Axiom snoc_Bottom_Not_None :
  forall {A : Type} fuel (tr : tree A) (v : A),
    vec_has_space_p tr = true -> snoc_Bottom fuel tr v <> None.

(* ---------------------------------- *)
(* -- to/from list                    *)
(* ---------------------------------- *)

Fixpoint go_toList {A : Type} (tr : tree A) (acc : list A) : list A :=
  match tr with
  | E => []
  | Leaf _ ns    => ns ++ acc
  | Node _ _ trs => fold_right (fun t acc => go_toList t acc) acc trs
  end.

Definition toList {A : Type} (tr : tree A) : list A :=
  go_toList tr [].

Fixpoint fromList {A : Type} (xs : list A) : (tree A) :=
  fold_left (fun acc x => snoc acc x) xs E.


(* ---------------------------------- *)
(* -- Theorems                        *)
(* ---------------------------------- *)

Fixpoint In_Vec {A : Type} (a : A) (tr : tree A) : Prop :=
  match tr with
  | E            => False
  | Leaf _ ns    => In a ns
  | Node _ _ trs =>
    ((fix in_vecs (a : A) (ls : list (tree A)) :=
        match ls with
        | [] => False
        | t :: ts => In_Vec a t \/ in_vecs a ts
        end) a trs)
  end.

Lemma in_vec_mkLeafAtHeight :
  forall {A} ht (a : A), In_Vec a (mkLeafAtHeight ht a).
Proof.
  intros. induction ht.
  + unfold mkLeafAtHeight, In_Vec. apply in_eq.
  + simpl. left. apply IHht.
Qed.

Lemma In_Vec_node_append : forall {A} (a : A) ht vec vecs szs,
  In_Vec a vec -> In_Vec a (Node ht szs (vecs ++ [vec])).
Proof.
  intros. induction vecs.
  + simpl. left. apply H.
  + simpl. right. apply IHvecs.
Qed.

Lemma snoc_Bottom_In_Vec : forall {A} fuel vec (a : A) vec2,
  snoc_Bottom fuel vec a = Some vec2 -> In_Vec a vec2.
Proof. Admitted.


Lemma snoc_In_Vec : forall A (a : A) vec, is_RRB vec -> In_Vec a (snoc vec a).
Proof.
  intros. destruct vec.
  (* tr = E *)
  + unfold snoc, vec_has_space_p, snoc_Bottom.
    cbv. left. left. reflexivity.

  (* tr = Leaf *)
  + unfold snoc, vec_has_space_p. destruct (length l0 <? M).

    (* snoc_Bottom ... *)
    - unfold vec_length. destruct l.
      (* Leaf [] [] *)
      * unfold snoc_Bottom. unfold In_Vec. apply in_eq.

      (* Leaf (s :: ss) (n :: ns) *)
      * assert(H1: snoc_Bottom (strong_last (n :: l) (cons_not_nil n l)) (Leaf (n :: l) l0) a =
                   let last_sz := last l n in
                   Some (Leaf ((n :: l) ++ [last_sz + 1]) (l0 ++ [a]))).
        (* Hack b/c Coq doesn't automatically eliminate redundant cases. *)
        { admit. }
        ++ rewrite H1. simpl. apply In_append.

    (* join ... *)
    - unfold join, get_height, mkLeafAtHeight.
      unfold In_Vec. right. left. apply in_eq.

  (* tr = Node *)
  + unfold snoc, vec_has_space_p. destruct l eqn:l'.
    - apply (node_szs_not_nil' n [] l0 H). reflexivity.
    - destruct (last l1 n0 <? vec_capacity (Node n (n0 :: l1) l0)).
      (* Root has space *)
      * assert (H1: snoc_Bottom (vec_length (Node n (n0 :: l1) l0)) (Node n ( n0 :: l1) l0) a =
                   (match (vec_length (Node n (n0 :: l1) l0)) with
                    | 0   => None
                    | S n1 =>
                      match ((n0 :: l1), l0) with
                      | ((n0 :: l1), tr :: ts) =>
                        if vec_has_space_p (last ts tr)
                        then let last_sz := last l1 n0 in
                             let szs'    := removelast (n0 :: l1) in
                             let trs'    := removelast l0 in
                             match snoc_Bottom n1 (last ts tr) a with
                             | Some snocd => Some (Node n (szs' ++ [last_sz + 1]) (trs' ++ [snocd]))
                             (* This value will never be None. Should I try to prove it to Coq? *)
                             | None => None
                             end
                        else
                          let branch  := mkLeafAtHeight (n - 1) a in
                          let last_sz := last l1 n0 in
                          let szs'    := (n0 :: l1) ++ [1 + last_sz] in
                          let trs'    := l0 ++ [branch]
                          in Some (Node n szs' trs')

                      | _ => None
                      end
                    end)). { admit. }
        rewrite H1.
        destruct (vec_length (Node n (n0 :: l1) l0)) eqn:node_len.
        (* Impossible case. Need a lemma to prove that we'll never run out of fuel. *)
        ++ assert (H2: vec_length (Node n (n0 :: l1) l0) <> 0).
           { rewrite vec_length_0_E. intro. inversion H0. apply H. }
           contradiction.
        ++ destruct l0 eqn:l0'.
           (*  Impossible case. l0 can never be empty. *)
           -- apply (node_elems_not_nil' n (n0 :: l1) [] H). reflexivity.
           -- destruct (vec_has_space_p (last l2 t)) eqn:vec_has_space.
              (* vec_has_space_p =? false *)
              +++ simpl. destruct (snoc_Bottom n1 (last l2 t) a) eqn:snocd.
                  --- apply In_Vec_node_append. subst.
                  assert(H2: In_Vec a t0).
                  { apply (snoc_Bottom_In_Vec n1 (last l2 t) a). apply snocd. }
                  apply H2.
                  (*  Impossible case. if vec_has_space_p == true, snocd_Bottom will never be None. *)
                  --- assert(H2: snoc_Bottom n1 (last l2 t) a <> None).
                      { apply snoc_Bottom_Not_None. apply vec_has_space. }
                      contradiction.
              (* vec_has_space_p =? true *)
              +++ apply In_Vec_node_append. apply (in_vec_mkLeafAtHeight (n - 1) a).
      (* Root overflow *)
      * unfold join, mkLeafAtHeight. simpl. right. left. apply (in_vec_mkLeafAtHeight n a).
Admitted.


Theorem get_and_default :
  forall {A : Type} (idx : nat) (tr : tree A) (default : A),
    ~ (In_Vec default tr) ->
    (get idx tr default = default) <-> idx >= vec_length tr.
Proof. Admitted.

Theorem get_2 :
  forall {A : Type} (idx : nat) (tr : tree A) (default : A),
    ~ (In_Vec default tr) -> idx <= vec_length tr ->
    In_Vec (get idx tr default) tr.
Proof. Admitted.


(* ---------------------------------- *)
(* -- Abs                             *)
(* ---------------------------------- *)

Inductive Abs  {A : Type} : tree A -> list A -> Prop :=
| Abs_E : Abs E []
| Abs_L : forall szs ns, Abs (Leaf szs ns) ns
| Abs_N : forall ht szs ns ls,
          AbsL ns ls -> Abs (Node ht szs ns) (append_all ls)

with AbsL {A : Type} : list (tree A) -> list (list A) -> Prop :=
| AbsL_Nil  : AbsL [] []
| AbsL_Cons : forall t l ts ls,
              Abs t l -> AbsL ts ls -> AbsL (t :: ts) (l :: ls).


Theorem get_relate:
  forall {A : Type} n vec ls d,
    is_RRB vec ->
    Abs vec ls -> @get A n vec d = nth n ls d.
Proof.
  intros. induction H0.
  + simpl ; destruct n ; reflexivity.
  + simpl. unfold index_of, M.
    assert(H1: (n / M ^ 0) mod M = n).
Admitted.

Theorem snoc_relate:
 forall {A : Type} vec ls val,
    Abs vec ls -> Abs (@snoc A vec val) (snoc_list ls val).
Proof. Admitted.
