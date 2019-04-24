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

Definition log2M := log2 M.

Definition mask := M - 1.

(* Useful type synonyms *)
Definition height := nat.
Definition size := nat.

(* The main datatype.
   Invariant: only rightmost node is allowed to be partially full. *)
Inductive tree (A : Type) : Type :=
| E    : tree A
| Leaf : list size -> list A -> tree A
| Node : height -> list size -> list (tree A) -> tree A.

Arguments E    {A}.
Arguments Leaf {A}.
Arguments Node {A}.

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

Axiom node_elems_not_nil :
  forall {A : Type} (ht : height) (szs : list size) (ns : list (tree A)) (tr : tree A),
    tr = Node ht szs ns -> ns <> [].

Axiom node_szs_not_nil :
  forall {A : Type} (ht : height) (szs : list size) (ns : list (tree A)) (tr : tree A),
    tr = Node ht szs ns -> szs <> [].

Axiom node_zero_not_in_szs :
  forall {A : Type} (ht : height) (szs : list size) (ns : list (tree A)) (tr : tree A),
    tr = Node ht szs ns -> ~ (In 0 szs).

Axiom leaf_szs_not_nil :
  forall {A : Type} (szs : list size) (ns : list A) (tr : tree A),
    tr = Leaf szs ns -> szs <> [].

Axiom leaf_zero_not_in_szs :
  forall {A : Type} (szs : list size) (ns : list A) (tr : tree A),
    tr = Leaf szs ns -> ~ (In 0 szs).

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
  @vec_length A vec = 0 <-> vec = E.
Proof.
  intros. split.
  (* -> *)
  + induction vec using tree_ind'.
    - reflexivity.
    - unfold vec_length. intro.
      destruct szs eqn:szs'.
      * assert (H2: szs <> []).
        { apply (leaf_szs_not_nil szs ls (Leaf szs ls)). reflexivity. }
        contradiction.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        { apply last_not_In.
          apply (leaf_zero_not_in_szs (n :: l) ls (Leaf (n :: l) ls)).
          reflexivity. }
        contradiction.
    - unfold vec_length. intro. destruct szs eqn:szs'.
      * assert (H2: szs <> []).
        { apply (node_szs_not_nil ht szs ls (Node ht szs ls)). reflexivity. }
        contradiction.
      * assert(H2: strong_last (n :: l) (cons_not_nil n l) <> 0).
        { apply last_not_In.
          apply (node_zero_not_in_szs ht (n :: l) ls (Node ht (n :: l) ls)).
          reflexivity. }
        contradiction.
  (* <-  *)
  + intro. rewrite H. unfold vec_length. reflexivity.
Qed.

(* ---------------------------------- *)
(* -- Lookup                          *)
(* ---------------------------------- *)

(* Not using bit operations for now *)
Definition index_of (ht : height) (i : nat) : nat := (i / (M ^ ht)) mod M.

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

(* Axiom get_and_default : *)
(*   forall {A : Type} (idx : nat) (tr : tree A) (default : A), *)
(*     idx < vec_length tr -> get idx tr default <> default. *)

Definition last_vec {A : Type} (tr : tree A) (default : A) : A :=
  get (vec_length tr) tr default.


(* ---------------------------------- *)
(* -- Snoc                            *)
(* ---------------------------------- *)

Fixpoint mkLeafAtHeight {A : Type} (ht : height) (v1 : A) : tree A :=
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


(* Assume that vector has space at the end, and snoc. *)
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

Axiom snoc_Bottom_Some :
  forall {A : Type} (tr : tree A) (v : A),
    vec_has_space_p tr = true -> exists fuel tr2, snoc_Bottom fuel tr v = Some tr2.

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

Lemma snoc_In_Vec : forall A (a : A) vec, In_Vec a (snoc vec a).
Proof.
  intros. induction vec.
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
      * assert(H: snoc_Bottom (strong_last (s :: l) (cons_not_nil s l)) (Leaf (s :: l) l0) a =
                  let last_sz := last l s in
                  Some (Leaf ((s :: l) ++ [last_sz + 1]) (l0 ++ [a]))).
        (* Hack b/c Coq doesn't automatically eliminate redundant cases. *)
        { admit. }
        ++ rewrite H. simpl. apply In_append.

    (* join ... *)
    - unfold join, get_height, mkLeafAtHeight.
      unfold In_Vec. right. left. apply in_eq.

  (* tr = Node *)
  + unfold snoc, vec_has_space_p. destruct l eqn:l'.
    - apply (node_szs_not_nil h l l0 (Node h l l0)). reflexivity. apply l'.
    - destruct (last l1 s <? vec_capacity (Node h (s :: l1) l0)).
      (* Root has space *)
      * assert (H: snoc_Bottom (vec_length (Node h (s :: l1) l0)) (Node h (s :: l1) l0) a =
                   (match (vec_length (Node h (s :: l1) l0)) with
                    | 0   => None
                    | S n =>
                      match ((s :: l1), l0) with
                      | ((s :: l1), tr :: ts) =>
                        if vec_has_space_p (last ts tr)
                        then let last_sz := last l1 s in
                             let szs'    := removelast (s :: l1) in
                             let trs'    := removelast l0 in
                             match snoc_Bottom n (last ts tr) a with
                             | Some snocd => Some (Node h (szs' ++ [last_sz + 1]) (trs' ++ [snocd]))
                             (* This value will never be None. Should I try to prove it to Coq? *)
                             | None => None
                             end
                        else
                          let branch  := mkLeafAtHeight (h - 1) a in
                          let last_sz := last l1 s in
                          let szs'    := (s :: l1) ++ [1 + last_sz] in
                          let trs'    := l0 ++ [branch]
                          in Some (Node h szs' trs')

                      | _ => None
                      end
                    end)). { admit. }
        rewrite H.
        destruct (vec_length (Node h (s :: l1) l0)) eqn:node_len.
        (* Impossible case. Need a lemma to prove that we'll never run out of fuel. *)
        ++ assert (H2: vec_length (Node h (s :: l1) l0) <> 0).
           { rewrite vec_length_0_E. intro. inversion H0. }
           contradiction.
        ++ destruct l0 eqn:l0'.
           (*  Impossible case. l0 can never be empty. *)
           -- apply (node_elems_not_nil h l l0 (Node h l l0)). reflexivity. apply l0'.
           -- destruct (vec_has_space_p (last l2 t)) eqn:vec_has_space.
              (* vec_has_space_p =? false *)
              +++ simpl. destruct (snoc_Bottom n (last l2 t) a) eqn:snocd.
                  --- assert(H2: In_Vec a t0).
                      { apply (snoc_Bottom_In_Vec n (last l2 t) a). apply snocd. }
                      apply In_Vec_node_append. apply H2.
                  (*  Impossible case. if vec_has_space_p == true, snocd_Bottom will never be None. *)
                  --- assert(H2: snoc_Bottom n (last l2 t) a <> None).
                      { apply snoc_Bottom_Not_None. apply vec_has_space. }
                      contradiction.
              (* vec_has_space_p =? true *)
              +++ apply In_Vec_node_append. apply (in_vec_mkLeafAtHeight (h - 1) a).
      (* Root overflow *)
      * unfold join, mkLeafAtHeight. simpl. right. left. apply (in_vec_mkLeafAtHeight h a).
Admitted.

(* ---------------------------------- *)
(* -- Abs                             *)
(* ---------------------------------- *)

Inductive Abs {A : Type} : @vector1 A -> list A -> Prop :=
| Abs_E : Abs E []
| Abs_L : forall szs ns, Abs (Leaf szs ns) ns
| Abs_S : forall l1 v1 val,
            (* is_RRB v1 -> *)
            Abs v1 l1 -> Abs (snoc v1 val) (snoc_list l1 val).
