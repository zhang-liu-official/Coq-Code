(* 2_logic_theorems.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 23 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

(* ********** *)

(* Exercise 1 *)

Inductive polymorphic_binary_tree (V : Type) : Type :=
| PLeaf : V -> polymorphic_binary_tree V
| PNode : polymorphic_binary_tree V -> polymorphic_binary_tree V -> polymorphic_binary_tree V.

Check (PNode (nat * bool)
               (PLeaf (nat * bool) (2, true))
               (PLeaf (nat * bool) (90, false)) : polymorphic_binary_tree (nat * bool)).

Check (PNode (polymorphic_binary_tree nat)
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6)))
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6))) : polymorphic_binary_tree (polymorphic_binary_tree nat)).

Compute PNode (polymorphic_binary_tree nat)
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6)))
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6))) : polymorphic_binary_tree (polymorphic_binary_tree nat).

(* ********** *)

(* Exercise 2 *)

Fixpoint eqb_polymorphic_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : polymorphic_binary_tree V) : bool :=
  match t1 with
  | PLeaf _ v1 =>
    match t2 with
    | PLeaf _ v2 =>
      eqb_V v1 v2
    | PNode _ t11 t12 =>
      false
    end
  | PNode _ t11 t12 =>
    match t2 with
    | PLeaf _ v2 =>
      false
    | PNode _ t21 t22 =>
      eqb_polymorphic_binary_tree V eqb_V t11 t21
      &&
      eqb_polymorphic_binary_tree V eqb_V t12 t22
    end
  end.

(*
Check(eqb_polymorphic_binary_tree (nat * bool)).

Check beq_nat.

Compute(beq_nat 2 3).

Compute(beq_nat 22 22).

Check eqb.

Compute(eqb true true).

Compute(eqb true false).


Check(eqb_polymorphic_binary_tree (polymorphic_binary_tree nat)).
 *)

(* Define equality predicate for nat * bool *)

Definition beq_natbool (p1 p2: nat * bool) : bool
  := let (n1, b1) := p1 in
     let (n2, b2) := p2 in
     (beq_nat n1 n2) && (eqb b1 b2).

Check beq_natbool.

(* Implement equality test for bt of nat * bool *)

Definition eqb_binary_tree_of_nats_and_bools (t1 t2: polymorphic_binary_tree (nat * bool)) : bool := eqb_polymorphic_binary_tree (nat * bool) beq_natbool t1 t2.
  
Check eqb_binary_tree_of_nats_and_bools.

(* Implemnet equality test for bt of nat *)

Definition eqb_binary_trees_of_nat (t1 t2: polymorphic_binary_tree nat) : bool
  := eqb_polymorphic_binary_tree nat beq_nat t1 t2.

Check (eqb_polymorphic_binary_tree (polymorphic_binary_tree nat)).

Compute eqb_polymorphic_binary_tree.

(* Implement equality predicate for bt of bt *)

Definition  eqb_binary_tree_of_binary_trees_of_nats (t1 t2: polymorphic_binary_tree (polymorphic_binary_tree nat)) : bool
  := eqb_polymorphic_binary_tree (polymorphic_binary_tree nat) eqb_binary_trees_of_nat t1 t2.

Check eqb_binary_tree_of_binary_trees_of_nats.

(*
A simple test:
Check PNode (polymorphic_binary_tree nat)
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (2)))
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6))).
Compute(eqb_binary_tree_of_binary_trees_of_nats (PNode (polymorphic_binary_tree nat)
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (2)))
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6))))

               (PNode (polymorphic_binary_tree nat)
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (2)))
               (PLeaf (polymorphic_binary_tree nat) (PLeaf (nat) (6))))). 
 *)

(* ********** *)

(* Exercises about types: *)

Definition ta : forall A : Type, A -> A * A :=
  fun A a => (a, a).

Definition tb : forall A B : Type, A -> B -> A * B :=
  fun A B a b => (a, b).

Definition tc : forall A B : Type, A -> B -> B * A :=
  fun A B a b => (b, a).

Check (tt : unit).

Definition td : forall (A : Type), (unit -> A) -> A :=
  fun A f => f tt.

Definition te : forall A B : Type, (A -> B) -> A -> B :=
  fun A B f a => f a.

Definition tf : forall A B : Type, A -> (A -> B) -> B :=
  fun A B a f => f a.

Definition tg : forall A B C : Type, (A -> B -> C) -> A -> B -> C :=
  fun A B C f a b => f a b.

Definition th : forall A B C : Type, (A -> B -> C) -> B -> A -> C :=
  fun A B C f b a => f a b.

Definition ti : forall A B C D : Type, (A -> C) -> (B -> D) -> A -> B -> C * D :=
  fun A B C D f g a b => (f a, g b).

Definition tj : forall A B C : Type, (A -> B) -> (B -> C) -> A -> C :=
  fun A B C f g x => g (f x).

Definition tk : forall A B : Type, A * B -> B * A :=
  fun A B p =>
    match p with
      (a, b) => (b, a)
    end.
(* Hint: use a match expression to destructure the input pair. *)

Definition tl : forall A B C : Type, (A * B -> C) -> A -> B -> C :=
  fun A B C f a b => f (a, b).

Definition tm : forall A B C : Type, (A -> B -> C) -> A * B -> C :=
  fun A B C f p =>
    match p with
      (a, b) => f a b
    end.

Definition tn : forall A B C : Type, (A * (B * C)) -> (A * B) * C :=
  fun A B C p =>
    match p with
      (a, q) =>
      match q with
        (b, c) => ((a, b), c)
      end
   end.

(* ********** *)

(* Exercises about propositions: *)

Proposition pa :
  forall A : Prop,
    A -> A * A. 
 Proof.  
  intro A.
  intro H_A.
  split.
  exact H_A.
  exact H_A.
Qed.

Proposition pb :
  forall A B : Prop, 
    A -> B -> A * B.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  exact H_A.
  exact H_B.
Qed.

Proposition pc :
  forall A B : Prop,
    A -> B -> B * A.
Proof.
  intros A B.
  intros H_A H_B.
  split.
  exact H_B.
  exact H_A.
Qed.

Check tt.

Proposition pd :
  forall (A : Prop),
    (unit -> A) -> A.
Proof.
  intro A.
  intro H_A.
  apply H_A.
  exact tt.
Qed.

Proposition pe :
  forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B.
  intros H_A_implies_B H_A.
  apply H_A_implies_B.
  exact H_A.
Qed.

Proposition pf :
  forall A B : Prop,
    A -> (A -> B) -> B.
Proof.
  intros A B.
  intros H_A H_A_implies_B.
  exact (H_A_implies_B H_A).
Qed.


Proposition pg :
  forall A B C : Prop,
    (A -> B -> C) -> A -> B -> C.
Proof.  
  intros A B C.
  intros H_A_implies_B_implies_C.
  intros H_A H_B.
  apply H_A_implies_B_implies_C.
  exact H_A.
  exact H_B.
Qed.

Proposition ph :
  forall A B C : Prop,
    (A -> B -> C) -> B -> A -> C.
Proof.  
  intros A B C.
  intros H_A_implies_B_implies_C.
  intros H_A H_B.
  apply H_A_implies_B_implies_C.
  exact H_B.
  exact H_A.
Qed.

Proposition pi :
  forall A B C D : Prop,
    (A -> C) -> (B -> D) -> A -> B -> C /\ D.
Proof. 
  intros A B C D.
  intro H_A_implies_C.
  intro H_B_implies_D.
  intros H_A H_B.
  split. 
  apply H_A_implies_C.
  exact H_A.
  apply H_B_implies_D.
  exact H_B.
Qed.

Proposition pj :
  forall A B C : Prop,
    (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros A B C.
  intros H_A_implies_B H_B_implies_C H_A.
  apply H_B_implies_C.
  apply H_A_implies_B.
  exact H_A.
Qed.

Proposition pk :
  forall A B : Prop,
    A /\ B -> B /\ A.
Proof.
  intros A B.
  intro H_A_and_B.
  destruct H_A_and_B as [H_A H_B].
  Check (conj H_B H_A).
  exact (conj H_B H_A).
Qed.

Proposition pl :
  forall A B C : Prop,
    (A /\ B -> C) -> A -> B -> C.
Proof.
  intros A B C.
  intro H_A_and_B_implies_C.
  intros H_A H_B.
  apply H_A_and_B_implies_C.
  split.
  - exact H_A.
  - exact H_B.
Qed.

Proposition pm :
  forall A B C : Prop,
    (A -> B -> C) -> A /\ B -> C.
Proof.
  intros A B C.
  intro H_ABC.
  intro H_A_and_B.
  apply H_ABC.
  apply H_A_and_B.
  apply H_A_and_B.
Qed.

Proposition pn : 
  forall A B C : Prop,
    (A /\ (B /\ C)) -> (A /\ B) /\ C.
Proof.
  intros A B C.
  intro H_A_and_B_and_C.
  split.
  destruct H_A_and_B_and_C as [H_A H_B_and_C].
  destruct H_B_and_C as [H_B H_C].
  split.
  - exact H_A.
  - exact H_B.
  - apply H_A_and_B_and_C.
Qed.

(* Optional Exercises *)

(* Exercise 12 *)

Proposition disjunction_distributes_over_conjunction_on_the_left :
  forall A B C : Prop,
    A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split.

  - intros [H_A | [H_B H_C]].

    + split.

      * left.
        exact H_A.

      * left.
        exact H_A.

    + split.

      * right.
        exact H_B.

      * right.
        exact H_C.

  - intros [[H_A | H_B] [H_A' | H_C]].

    * left.
      exact H_A.

    * left.
      exact H_A.

    * left.
      exact H_A'.

    * right.
      exact (conj H_B H_C).
Qed.

Proposition disjunction_distributes_over_conjunction_on_the_right :
  forall A B C : Prop,
    (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
  intros A B C.
  split.

  - intros [[H_A H_B] | H_C].

    + split.

      * left.
        exact H_A.

      * left.
        exact H_B.

    + split.

      * right.
        exact H_C.

      * right.
        exact H_C.

  - intros [[H_A | H_C] [H_B | H_C']].

    * left.
      exact (conj H_A H_B).

    * right.
      exact H_C'.

    * right.
      exact H_C.

    * right.
      exact H_C.
Qed.

(* Exercise 13 *)

Proposition conjunction_distributes_over_disjunction_on_the_left :
  forall A B C : Prop,
    A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split.

  - intros [H_A [H_B | H_C]].

    * left.
      exact (conj H_A H_B).

    * right.
      exact (conj H_A H_C).

  - intros [[H_A H_B] | [H_A H_C]].

    + split.

      exact H_A.

      * left.
        exact H_B.

    + split.

      exact H_A.

      * right.
        exact H_C.
Qed.

Proposition conjunction_distributes_over_disjunction_on_the_right :
  forall A B C : Prop,
    (A \/ B) /\ C <-> (A /\ C) \/ (B /\ C).
Proof.
  intros A B C.
  split.

  - intros [[H_A | H_B] H_C].

    * left.
      exact (conj H_A H_C).

    * right.
      exact (conj H_B H_C).

  - intros [[H_A H_C] | [H_B H_C]].

    + split.

      * left.
        exact H_A.

      * exact H_C.

    + split.

      * right.
        exact H_B.

      * exact H_C.
Qed.

(* end of week-02_exercises.v *)
