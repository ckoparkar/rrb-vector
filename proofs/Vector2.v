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
    -> Forall is_RRB ns -> is_RRB (Node ht szs ns)
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
        { apply strong_last_not_In.
          apply (leaf_zero_not_in_szs' (n :: l) ls H). }
        contradiction.
    - unfold vec_length. intro. destruct szs eqn:szs'.
      * assert (H2: szs <> []).
        { subst. apply (node_szs_not_nil' ht [] ls H). }
        contradiction.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        { apply strong_last_not_In.
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

Lemma In_Vec_mkLeafAtHeight :
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

Axiom dont_worry_about_fuel : forall {A} (a : A) fuel vec,
  vec_has_space_p vec = true ->
  snoc_Bottom fuel vec a <> None.

Axiom dont_worry_about_fuel2 : forall {A} (a : A) fuel vec vec2,
  vec_has_space_p vec = true ->
  snoc_Bottom fuel vec a = Some vec2 -> In_Vec a vec2.

Lemma snoc_Bottom_in_vec : forall {A} vec (a : A) vec2,
  is_RRB vec -> snoc_Bottom (vec_length vec) vec a = Some vec2 -> In_Vec a vec2.
Proof.
  intros. induction vec using tree_ind'.
  + inversion H.
  + unfold vec_length in H0. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - destruct (strong_last (n :: l) (cons_not_nil n l)) eqn:d_fuel.
      * assert(H1: strong_last (n :: l) (cons_not_nil n l) <> 0).
        apply strong_last_not_In. inversion H. apply H5. contradiction.
      * inversion H0. apply In_append.
  + unfold vec_length in H0. destruct szs eqn:d_szs.
    - inversion H. contradiction.
    - destruct (strong_last (n :: l) (cons_not_nil n l)) eqn:d_fuel.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        apply strong_last_not_In. inversion H. apply H7. contradiction.
      * inversion H0. destruct ls eqn:d_ls.
        ++ inversion H. contradiction.
        ++ destruct (vec_has_space_p (last l0 t)) eqn:d_vec_has_space.
           -- destruct (snoc_Bottom n0 (last l0 t) a) eqn:snoc_bot.
              ** inversion H3. apply In_Vec_node_append.
                 apply dont_worry_about_fuel2 with n0 (last l0 t).
                 apply d_vec_has_space. apply snoc_bot.
              ** inversion H3.
           -- inversion H3. apply (In_Vec_node_append a ht (mkLeafAtHeight (ht - 1) a) (t :: l0) (n :: l ++ [S (last l n)])).
              apply In_Vec_mkLeafAtHeight.
Qed.


Lemma snoc_In_Vec : forall A (a : A) vec, is_RRB vec -> In_Vec a (snoc vec a).
Proof.
  intros. induction vec using tree_ind'.
  (* tr = E *)
  + unfold snoc, vec_has_space_p, snoc_Bottom.
    simpl. left. left. reflexivity.

  (* tr = Leaf *)
  + unfold snoc, vec_has_space_p. destruct (length ls <? M).
    (* snoc_Bottom ... *)
    - unfold vec_length. destruct szs.
      (* Leaf [] [] *)
      * unfold snoc_Bottom. unfold In_Vec. apply in_eq.

      (* Leaf (s :: ss) (n :: ns) *)
      * destruct (strong_last (n :: szs) (cons_not_nil n szs)) eqn:fuel.
        (* Impossible case, cannot run out of fuel. *)
        ++ assert(H1: (strong_last (n :: szs) (cons_not_nil n szs)) <> 0).
           { apply strong_last_not_In. inversion H. apply H4. }
           contradiction.
        ++ simpl. apply In_append.
    (* join ... *)
    - unfold join, get_height, mkLeafAtHeight.
      unfold In_Vec. right. left. apply in_eq.

  (* tr = Node *)
  + unfold snoc, vec_has_space_p. destruct szs eqn:d_szs.
    - apply (node_szs_not_nil' ht [] ls H). reflexivity.
    - destruct (last l n <? vec_capacity (Node ht (n :: l) ls)).
      (* Root has space *)
      * unfold vec_length. destruct (strong_last (n :: l) (cons_not_nil n l)) eqn:fuel.
        (* Impossible case: cannot run out of fuel *)
        ++ assert(H1: (strong_last (n :: l) (cons_not_nil n l)) <> 0).
           { apply strong_last_not_In. inversion H. apply H6. }
           contradiction.
        ++ simpl. destruct ls.
           (* Impossible case: ls cannot be empty *)
           -- inversion H. contradiction.
           -- destruct (vec_has_space_p (last ls t)) eqn:vec_has_space.
              simpl. destruct (snoc_Bottom n0 (last ls t) a) eqn:snocd.
              ** apply In_Vec_node_append.
                 apply (dont_worry_about_fuel2 a n0 (last ls t) t0).
                 apply vec_has_space. apply snocd.
              (*  Impossible case. if vec_has_space_p == true, snocd_Bottom will never be None. *)
              ** assert(H2: snoc_Bottom n0 (last ls t) a <> None).
                 { apply dont_worry_about_fuel. apply vec_has_space. }
                 contradiction.
              ** apply In_Vec_node_append. apply (In_Vec_mkLeafAtHeight (ht - 1) a).
      (* Root overflow *)
      * unfold join, mkLeafAtHeight. simpl. right. left. apply (In_Vec_mkLeafAtHeight ht a).
Qed.


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
