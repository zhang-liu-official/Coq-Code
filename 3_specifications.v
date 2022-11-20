(* 3_specifications.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 30 Aug 2020 *)

(* ********** *)

(* Paraphernalia: *)

Require Import Arith.

Inductive binary_tree (V : Type) : Type :=
| Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* ********** *)

Definition recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
      add (S x') y = S (add x' y)).

Proposition there_is_at_most_one_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    recursive_specification_of_addition add1 ->
    recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
  intros add1 add2.
  unfold recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].

  - intro y.
    rewrite -> (H_add2_O y).
    exact (H_add1_O y).

  - intro y.
    rewrite -> (H_add1_S x' y).
    rewrite -> (H_add2_S x' y).
    Check (IHx' y).
    rewrite -> (IHx' y).
    reflexivity.
Qed.

(* ********** *)

Definition tail_recursive_specification_of_addition (add : nat -> nat -> nat) :=
  (forall y : nat,
      add O y = y)
  /\
  (forall x' y : nat,
     add (S x') y = add x' (S y)).

(* Exercise 1 *)

Proposition there_is_at_most_one_tail_recursive_addition :
  forall add1 add2 : nat -> nat -> nat,
    tail_recursive_specification_of_addition add1 ->
    tail_recursive_specification_of_addition add2 ->
    forall x y : nat,
      add1 x y = add2 x y.
Proof.
  intros add1 add2.
  unfold tail_recursive_specification_of_addition.
  intros [H_add1_O H_add1_S] [H_add2_O H_add2_S].
  intro x.
  induction x as [ | x' IHx'].

  - intro y.
    rewrite -> (H_add2_O y).
    Check (H_add1_O y).
    exact (H_add1_O y).

  - intro y.
    rewrite -> (H_add1_S x').
    rewrite -> (H_add2_S x').
    Check (IHx' (S y)).
    rewrite -> (IHx' (S y)).
    reflexivity.
Qed.

(* Exercise 4 *)

Theorem the_resident_addition_function_satisfies_the_recursive_specification_of_addition :
  recursive_specification_of_addition Nat.add.
Proof.
  unfold recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = S (_ + _)).
    exact (Nat.add_succ_l x' y).
Qed.

Theorem the_resident_addition_function_satisfies_the_tail_recursive_specification_of_addition :
  tail_recursive_specification_of_addition Nat.add.
Proof.
  unfold tail_recursive_specification_of_addition.
  split.
  - intro y.
    Search (0 + _ = _).
    exact (Nat.add_0_l y).
  - intros x' y.
    Search (S _ + _ = _ + S _).
    exact (Nat.add_succ_comm x' y).
Qed.

(* Exercise 9 *)

(* ********** *)

Definition specification_of_mirror (mirror : forall V : Type, binary_tree V -> binary_tree V) : Prop :=
  (forall (V : Type)
          (v : V),
      mirror V (Leaf V v) =
      Leaf V v)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      mirror V (Node V t1 t2) =
      Node V (mirror V t2) (mirror V t1)).

Proposition there_is_at_most_one_mirror_function :
  forall mirror1 mirror2 : forall V : Type, binary_tree V -> binary_tree V,
    specification_of_mirror mirror1 ->
    specification_of_mirror mirror2 ->
    forall (V : Type)
           (t : binary_tree V),
      mirror1 V t = mirror2 V t.
Proof.
  intros mirror1 mirror2.
  unfold specification_of_mirror.
  intros [H_mirror1_Leaf H_mirror1_Node] [H_mirror2_Leaf H_mirror2_Node].
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - rewrite -> (H_mirror1_Leaf V v).
    rewrite -> (H_mirror2_Leaf V v).
    reflexivity.
  - rewrite -> (H_mirror1_Node V t1 t2).
    rewrite -> (H_mirror2_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_number_of_leaves (number_of_leaves : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_leaves V (Leaf V v) =
      1)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_leaves V (Node V t1 t2) =
      number_of_leaves V t1 + number_of_leaves V t2).

Proposition there_is_at_most_one_number_of_leaves_function :
  forall number_of_leaves1 number_of_leaves2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_leaves number_of_leaves1 ->
    specification_of_number_of_leaves number_of_leaves2 ->
    forall (V : Type)
           (t : binary_tree V),
      number_of_leaves1 V t = number_of_leaves2 V t.
Proof.
  intros number_of_leaves1 number_of_leaves2.
  unfold specification_of_number_of_leaves.
  intros [H_number_of_leaves1_Leaf H_number_of_leaves1_Node] [H_number_of_leaves2_Leaf H_number_of_leaves2_Node].
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - rewrite -> (H_number_of_leaves1_Leaf V v).
    rewrite -> (H_number_of_leaves2_Leaf V v).
    reflexivity.
  - rewrite -> (H_number_of_leaves1_Node V t1 t2).
    rewrite -> (H_number_of_leaves2_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_number_of_nodes (number_of_nodes : forall V : Type, binary_tree V -> nat) : Prop :=
  (forall (V : Type)
          (v : V),
      number_of_nodes V (Leaf V v) =
      0)
  /\
  (forall (V : Type)
          (t1 t2 : binary_tree V),
      number_of_nodes V (Node V t1 t2) =
      S (number_of_nodes V t1 + number_of_nodes V t2)).

Proposition there_is_at_most_one_number_of_nodes_function :
  forall number_of_nodes1 number_of_nodes2 : forall V : Type, binary_tree V -> nat,
    specification_of_number_of_nodes number_of_nodes1 ->
    specification_of_number_of_nodes number_of_nodes2 ->
    forall (V : Type)
           (t : binary_tree V),
      number_of_nodes1 V t = number_of_nodes2 V t.
Proof.
  intros number_of_nodes1 number_of_nodes2.
  unfold specification_of_number_of_nodes.
  intros [H_number_of_nodes1_Leaf H_number_of_nodes1_Node] [H_number_of_nodes2_Leaf H_number_of_nodes2_Node].
  intros V t.
  induction t as [ v | t1 IHt1 t2 IHt2 ].
  - rewrite -> (H_number_of_nodes1_Leaf V v).
    rewrite -> (H_number_of_nodes2_Leaf V v).
    reflexivity.
  - rewrite -> (H_number_of_nodes1_Node V t1 t2).
    rewrite -> (H_number_of_nodes2_Node V t1 t2).
    rewrite -> IHt1.
    rewrite -> IHt2.
    reflexivity.
Qed.

(* ********** *)

(* Exercise 5 *)

Theorem the_two_specifications_of_addition_are_equivalent :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add <-> tail_recursive_specification_of_addition add.
Proof.
  intro add.
  split.
  - unfold recursive_specification_of_addition.
    intros [H_rec_add_O H_rec_add_S].
    unfold tail_recursive_specification_of_addition.
    split.
    -- intro y.
       exact (H_rec_add_O y).
    -- intros x' y.
       Check (H_rec_add_S x' y).
       rewrite -> (H_rec_add_S x' y).
       induction x' as [ | x'' IHx''].
       --- rewrite -> (H_rec_add_O y).
           rewrite -> (H_rec_add_O (S y)).
           reflexivity.
       --- rewrite -> (H_rec_add_S x'' (S y)).
           rewrite <- IHx''.
           rewrite -> (H_rec_add_S x'' y).
           reflexivity.
  - unfold tail_recursive_specification_of_addition.
    intros [H_tail_add_O H_tail_add_S].
    unfold recursive_specification_of_addition.
    split.
    -- intro y.
       exact (H_tail_add_O y).
    -- intros x' y.
       Check (H_tail_add_S x' y).
       rewrite -> (H_tail_add_S x' y).
       revert y.
       induction x' as [ | x'' IHx''].
       --- intro y.
           rewrite -> (H_tail_add_O y).
           rewrite -> (H_tail_add_O (S y)).
           reflexivity.
       --- intro y.
           rewrite -> (H_tail_add_S x'' y).
           rewrite -> (H_tail_add_S x'' (S y)).
           Check (IHx''(S y)).
           exact (IHx''(S y)).
Qed.

(* Exercise 6 *)

Theorem associativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intro S.
  destruct S as [S_O S_S].
  induction n1 as [| n1' IHn1'].
  - intros n2 n3.
    Check (S_O (add n2 n3)).
    rewrite -> (S_O (add n2 n3)).
    Check (S_O n2).
    rewrite -> (S_O n2).
    reflexivity.
  - intros n2 n3.
    Check (S_S (n1') (add n2 n3)).
    rewrite -> (S_S (n1') (add n2 n3)).
    Check (IHn1').
    Check (IHn1' n2 n3).
    rewrite -> (IHn1' n2 n3).
    rewrite <- (S_S (add n1' n2) n3).
    Check (S_S n1' n2).
    rewrite -> (S_S n1' n2).
    reflexivity.
Qed.

Theorem associativity_of_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n1 n2 n3 : nat,
      add n1 (add n2 n3) = add (add n1 n2) n3.
Proof.
  intros add tr_add.
  destruct (the_two_specifications_of_addition_are_equivalent add) as [r_implies_tr tr_implies_r].
  Check (tr_implies_r tr_add).
  Check (associativity_of_recursive_addition add (tr_implies_r tr_add)).
  exact (associativity_of_recursive_addition add (tr_implies_r tr_add)).
Qed.

(* ********** *)

Lemma commutativity_of_recursive_addition_O :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n O = n.
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intro S.
  destruct S as [S_O S_S].
  intro n.
  induction n as [| n' IHn'].
  - rewrite -> (S_O 0).
    reflexivity.
  - rewrite -> (S_S n' 0).
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma commutativity_of_recursive_addition_S :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 (S n2) = S (add n1 n2).
Proof.
  intro add.
  unfold recursive_specification_of_addition.
  intro S.
  destruct S as [S_O S_S].
  intros n1 n2.
  induction n1 as [| n1' IHn1'].
  - rewrite -> (S_O (S n2)).
    rewrite -> (S_O (n2)).
    reflexivity.
  - rewrite -> (S_S n1' (S n2)).
    rewrite -> (S_S n1' n2).
    rewrite -> IHn1'.
    reflexivity.
Qed.

Theorem commutativity_of_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
  intros add S_add.
  assert (H_add_O := commutativity_of_recursive_addition_O add S_add).
  assert (H_add_S := commutativity_of_recursive_addition_S add S_add).
  unfold recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O S_add_S].
  intros n1 n2.
  induction n1 as [| n1' IHn1'].
  - rewrite -> (S_add_O n2).
    rewrite -> (H_add_O n2).
    reflexivity.
  - rewrite -> (S_add_S n1' n2).
    rewrite -> (H_add_S n2 n1').
    rewrite -> IHn1'.
    reflexivity.
Qed.


(* commutativity for tail recursive addition *)


Lemma commutativity_of_tail_recursive_addition_O :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add n O = n.
Proof.
  intros add tr_add.
  destruct (the_two_specifications_of_addition_are_equivalent add) as [r_implies_tr tr_implies_r].
  Check (tr_implies_r tr_add).
  Check (commutativity_of_recursive_addition_O add (tr_implies_r tr_add)).
  exact (commutativity_of_recursive_addition_O add (tr_implies_r tr_add)).
Qed.

Lemma commutativity_of_tail_recursive_addition_S :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 (S n2) = S (add n1 n2).
Proof.
  intros add tr_add.
  destruct (the_two_specifications_of_addition_are_equivalent add) as [r_implies_tr tr_implies_r].
  Check (tr_implies_r tr_add).
  Check (commutativity_of_recursive_addition_S add (tr_implies_r tr_add)).
  exact (commutativity_of_recursive_addition_S add (tr_implies_r tr_add)).
Qed.

Theorem commutativity_of_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n1 n2 : nat,
      add n1 n2 = add n2 n1.
Proof.
  intros add tr_add.
  destruct (the_two_specifications_of_addition_are_equivalent add) as [r_implies_tr tr_implies_r].
  Check (tr_implies_r tr_add).
  Check (commutativity_of_recursive_addition add (tr_implies_r tr_add)).
  exact (commutativity_of_recursive_addition add (tr_implies_r tr_add)).
Qed.

(* ------------- *)
(* Exercise 8 *)
 
Theorem O_is_left_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof. 
  intros add S_add. 
  unfold recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O S_add_S]. 
  intro n.
  rewrite -> (S_add_O n).
  reflexivity.
Qed.


Theorem O_is_left_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add 0 n = n.
Proof. 
  intros add S_add. 
  unfold tail_recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O S_add_S].
  intro n.
  rewrite -> (S_add_O n).
  reflexivity.
Qed.

Theorem O_is_right_neutral_for_recursive_addition :
  forall add : nat -> nat -> nat,
    recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof. 
  intros add S_add. 
  unfold recursive_specification_of_addition in S_add.
  destruct S_add as [S_add_O S_add_S].
  intro n.
  induction n as [ | n' IHn'].  
  - rewrite -> (S_add_O O).
    reflexivity.     
  - rewrite -> (S_add_S n' O).
    rewrite  -> IHn'. 
    reflexivity.
    
    Restart.

    intros add S_add.  
    assert (S_add_O := commutativity_of_recursive_addition_O add S_add).
    assert (S_add_S := commutativity_of_recursive_addition_S add S_add).
    intro n.
    rewrite -> (S_add_O n).
    reflexivity.    
Qed.


Theorem O_is_right_neutral_for_tail_recursive_addition :
  forall add : nat -> nat -> nat,
    tail_recursive_specification_of_addition add ->
    forall n : nat,
      add n 0 = n.
Proof. 
    intros add tr_add.
    destruct (the_two_specifications_of_addition_are_equivalent add) as [r_implies_tr tr_implies_r].
    Check (tr_implies_r tr_add).
    Check (O_is_right_neutral_for_recursive_addition add (tr_implies_r tr_add)).
    exact (O_is_right_neutral_for_recursive_addition add (tr_implies_r tr_add)).

    Restart. 
 
    intros add S_add. 
    unfold tail_recursive_specification_of_addition in S_add.
    assert (H := commutativity_of_tail_recursive_addition_S add S_add).
    destruct S_add as [S_add_O S_add_S].
    intro n.
    induction n as [ | n' IHn'].
    - rewrite -> (S_add_O O).
      reflexivity.         
    - rewrite -> (S_add_S n' O). 
      Check H.
      rewrite -> H. 
      rewrite -> IHn'.
      reflexivity.
Qed.

(* ********** *)

(* end of week-03_specifications.v *)
