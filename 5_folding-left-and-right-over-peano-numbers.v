(* 5_folding-left-and-right-over-peano-numbers.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

Definition specification_of_power (power : nat -> nat -> nat) :=
  (forall x : nat,
      power x 0 = 1)
  /\
  (forall (x : nat)
          (n' : nat),
      power x (S n') = x * power x n').

(* ***** *)

Proposition there_is_at_most_one_function_satisfying_the_specification_of_power :
  forall power1 power2 : nat -> nat -> nat,
    specification_of_power power1 ->
    specification_of_power power2 ->
    forall x n : nat,
      power1 x n = power2 x n.
Proof.
  intros power1 power2.
  unfold specification_of_power.
  intros [S1_O S1_S] [S2_O S2_S] x n.
  induction n as [ | n' IHn'].
  - rewrite -> (S2_O x).
    exact (S1_O x).
  - rewrite -> (S1_S x n').
    rewrite -> (S2_S x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

Definition test_power (candidate : nat -> nat -> nat) : bool :=
  (candidate 2 0 =? 1) &&
  (candidate 10 2 =? 10 * 10) &&
  (candidate 3 2 =? 3 * 3).

(* ***** *)

Fixpoint power_v0_aux (x n : nat) : nat :=
  match n with
  | O =>
    1
  | S n' =>
    x * power_v0_aux x n'
  end.

Definition power_v0 (x n : nat) : nat :=
  power_v0_aux x n.

Compute (test_power power_v0).

Lemma fold_unfold_power_v0_aux_O :
  forall x : nat,
    power_v0_aux x 0 = 1.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Lemma fold_unfold_power_v0_aux_S :
  forall x n' : nat,
    power_v0_aux x (S n') = x * power_v0_aux x n'.
Proof.
  fold_unfold_tactic power_v0_aux.
Qed.

Proposition power_v0_safisfies_the_specification_of_power :
  specification_of_power power_v0.
Proof.
  unfold specification_of_power, power_v0.
  split.
  - exact fold_unfold_power_v0_aux_O.
  - exact fold_unfold_power_v0_aux_S.
Qed.

(* ***** *)

Fixpoint power_v1_aux (x n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    power_v1_aux x n' (x * a)
  end.

Definition power_v1 (x n : nat) : nat :=
  power_v1_aux x n 1.

Compute (test_power power_v1).

Lemma fold_unfold_power_v1_aux_O :
  forall x a : nat,
    power_v1_aux x 0 a =
    a.
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

Lemma fold_unfold_power_v1_aux_S :
  forall x n' a : nat,
    power_v1_aux x (S n') a =
    power_v1_aux x n' (x * a).
Proof.
  fold_unfold_tactic power_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_power_v0_aux_and_power_v1_aux :
  forall x n a : nat,
    power_v0_aux x n * a = power_v1_aux x n a.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_O x).
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    exact (Nat.mul_1_l a).
  - intro a.
    rewrite -> (fold_unfold_power_v0_aux_S x n').
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    Check (IHn' (x * a)).
    rewrite <- (IHn' (x * a)).
    rewrite -> (Nat.mul_comm x (power_v0_aux x n')).
    Check (Nat.mul_assoc).
    symmetry.
    exact (Nat.mul_assoc (power_v0_aux x n') x a).
Qed.

Theorem power_v0_and_power_v1_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  unfold power_v0, power_v1.
  Check (about_power_v0_aux_and_power_v1_aux x n 1).
  rewrite <- (Nat.mul_1_r (power_v0_aux x n)).
  exact (about_power_v0_aux_and_power_v1_aux x n 1).
Qed.

(* ********** *)

Fixpoint nat_fold_right (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    s (nat_fold_right V z s n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_right V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_right V z s (S n') =
    s (nat_fold_right V z s n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

(* ***** *)

Fixpoint nat_fold_left (V : Type) (z : V) (s : V -> V) (n : nat) : V :=
  match n with
  | O =>
    z
  | S n' =>
    nat_fold_left V (s z) s n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (z : V)
         (s : V -> V),
    nat_fold_left V z s O =
    z.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (z : V)
         (s : V -> V)
         (n' : nat),
    nat_fold_left V z s (S n') =
    nat_fold_left V (s z) s n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ********** *)

Definition power_v0_alt (x n : nat) : nat :=
  nat_fold_right nat 1 (fun ih => x * ih) n.

Compute (test_power power_v0_alt).

Proposition power_v0_alt_safisfies_the_specification_of_power :
  specification_of_power power_v0_alt.
Proof.
  unfold specification_of_power, power_v0_alt.
  split.
  - intro x.
    rewrite -> (fold_unfold_nat_fold_right_O nat 1 (fun ih : nat => x * ih)).
    reflexivity.
  - intros x n'.
    rewrite -> (fold_unfold_nat_fold_right_S nat 1 (fun ih : nat => x * ih) n').
    reflexivity.
Qed.

Corollary power_v0_and_power_v0_alt_are_equivalent :
  forall x n : nat,
    power_v0 x n = power_v0_alt x n.
Proof.
  intros x n.
  Check (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
  exact (there_is_at_most_one_function_satisfying_the_specification_of_power
           power_v0
           power_v0_alt
           power_v0_safisfies_the_specification_of_power
           power_v0_alt_safisfies_the_specification_of_power
           x
           n).
Qed.

(* ***** *)

Definition power_v1_alt (x n : nat) : nat :=
  nat_fold_left nat 1 (fun ih => x * ih) n.

Compute (test_power power_v1_alt).

Lemma power_v1_and_power_v1_alt_are_equivalent_aux :
  forall x n a : nat,
    power_v1_aux x n a = nat_fold_left nat a (fun ih : nat => x * ih) n.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_power_v1_aux_O x a).
    rewrite -> (fold_unfold_nat_fold_left_O nat a (fun ih : nat => x * ih)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_power_v1_aux_S x n' a).
    rewrite -> (fold_unfold_nat_fold_left_S nat a (fun ih : nat => x * ih) n').
    Check (IHn' (x * a)).
    exact (IHn' (x * a)).
Qed.

    
Proposition power_v1_and_power_v1_alt_are_equivalent :
  forall x n : nat,
    power_v1 x n = power_v1_alt x n.
Proof.
  intros x n.
  unfold power_v1, power_v1_alt.
  exact (power_v1_and_power_v1_alt_are_equivalent_aux x n 1).
Qed.

(* ********** *)

Lemma about_nat_fold_left :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V (s z) s n = s (nat_fold_left V z s n).
Proof.
Admitted.

Lemma about_nat_fold_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_right V (s z) s n = s (nat_fold_right V z s n).
Proof.
Admitted.

Theorem folding_left_and_right :
  forall (V : Type) (z : V) (s : V -> V) (n : nat),
    nat_fold_left V z s n = nat_fold_right V z s n.
Proof.
  intros V z s n.
  revert z.
  induction n as [ | n' IHn'].
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_O V z s).
    rewrite -> (fold_unfold_nat_fold_right_O V z s).
    reflexivity.
  - intro z.
    rewrite -> (fold_unfold_nat_fold_left_S V z s n').
    rewrite -> (fold_unfold_nat_fold_right_S V z s n').
(*
    rewrite -> (about_nat_fold_left V z s n').
    rewrite -> (IHn' z).
    reflexivity.
*)
    rewrite <- (about_nat_fold_right V z s n').
    Check (IHn' (s z)).
    exact (IHn' (s z)).
Qed.
    
(* ********** *)

Corollary power_v0_and_power_v1_are_equivalent_alt :
  forall x n : nat,
    power_v0 x n = power_v1 x n.
Proof.
  intros x n.
  rewrite -> (power_v0_and_power_v0_alt_are_equivalent x n).
  rewrite -> (power_v1_and_power_v1_alt_are_equivalent x n).
  unfold power_v0_alt, power_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 1 (fun ih : nat => x * ih) n).
Qed.

(* ********** *)

(* Exercise 2a *)

Definition recursive_specification_of_multiplication (mul : nat -> nat -> nat) :=
    ((forall j : nat,
         mul O j = 0)
     /\
     (forall i' j : nat,
         mul (S i') j = j + (mul i' j))).

Proposition there_is_at_most_one_function_satisfying_the_recursive_specification_of_multiplication :
  forall mul1 mul2 : nat -> nat -> nat,
    recursive_specification_of_multiplication mul1 ->
    recursive_specification_of_multiplication mul2 ->
    forall i j : nat,
      mul1 i j = mul2 i j.
Proof.
  intros mul1 mul2.
  unfold recursive_specification_of_multiplication.
  intros [S1_O S1_S] [S2_O S2_S] i j.
  induction i as [ | i' IHi'].
  - rewrite -> (S2_O j).
    exact (S1_O j).
  - rewrite -> (S2_S i' j).
    rewrite -> (S1_S i' j).
    rewrite -> IHi'.
    reflexivity.
Qed.
    
Definition test_mul (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 0)
  &&
  (candidate 1 0 =n= 0)
  &&
  (candidate 1 1 =n= 1)
  &&
  (candidate 1 2 =n= 2)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 6)
  &&
  (candidate 3 2 =n= 6)
  &&
  (candidate 6 4 =n= 24)
  &&
  (candidate 4 6 =n= 24)
  (* etc. *)
  .

Fixpoint mul_v0_aux (i j : nat) : nat :=
  match i with
    | O => 0
    | S i' => j + (mul_v0_aux i' j)
  end.

Lemma fold_unfold_mul_v0_aux_O :
  forall j : nat,
    mul_v0_aux O j = 0.
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Lemma fold_unfold_mul_v0_aux_S :
  forall i' j : nat,
    mul_v0_aux (S i') j = j + (mul_v0_aux i' j).
Proof.
  fold_unfold_tactic mul_v0_aux.
Qed.

Definition mul_v0 (i j : nat) : nat :=
  mul_v0_aux i j.

Proposition mul_v0_safisfies_the_specification_of_multiplication :
  recursive_specification_of_multiplication mul_v0.
Proof.
  unfold recursive_specification_of_multiplication, mul_v0.
  split.
  - exact fold_unfold_mul_v0_aux_O.
  - exact fold_unfold_mul_v0_aux_S.
Qed.

Compute (test_mul mul_v0).

Definition mul_v0_alt (i j : nat) : nat :=
  nat_fold_right nat 0 (fun ih => j + ih) i.

Proposition mul_v0_alt_safisfies_the_specification_of_multiplication :
  recursive_specification_of_multiplication mul_v0_alt.
Proof.
  unfold recursive_specification_of_multiplication, mul_v0_alt.
  split.
  - intro j.
    rewrite -> (fold_unfold_nat_fold_right_O nat 0 (fun ih : nat => j + ih)).
    reflexivity.
  - intros i' j.
    rewrite -> (fold_unfold_nat_fold_right_S nat 0 (fun ih : nat => j + ih) i').
    reflexivity.
Qed.

Compute (test_mul mul_v0_alt).

Corollary mul_v0_and_mul_v0_alt_are_equivalent :
  forall i j : nat,
    mul_v0 i j = mul_v0_alt i j.
Proof.
  - intros i j.
    Check (there_is_at_most_one_function_satisfying_the_recursive_specification_of_multiplication
             mul_v0
             mul_v0_alt
             mul_v0_safisfies_the_specification_of_multiplication
             mul_v0_alt_safisfies_the_specification_of_multiplication
             i
             j
          ).
    exact (there_is_at_most_one_function_satisfying_the_recursive_specification_of_multiplication
             mul_v0
             mul_v0_alt
             mul_v0_safisfies_the_specification_of_multiplication
             mul_v0_alt_safisfies_the_specification_of_multiplication
             i
             j
          ).
Qed.

(* Exercise 2b *)

Fixpoint mul_v1_aux (i j a : nat) : nat :=
  match i with
    | O => a
    | S i' => mul_v1_aux i' j (j + a)
  end.

Lemma fold_unfold_mul_v1_aux_O :
  forall j a : nat,
    mul_v1_aux O j a = a.
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Lemma fold_unfold_mul_v1_aux_S :
  forall i' j a : nat,
    mul_v1_aux (S i') j a = mul_v1_aux i' j (j + a).
Proof.
  fold_unfold_tactic mul_v1_aux.
Qed.

Definition mul_v1 (i j : nat) : nat :=
  mul_v1_aux i j 0.

Compute (test_mul mul_v1).

Definition mul_v1_alt (i j : nat) : nat :=
  nat_fold_left nat 0 (fun ih => j + ih) i.

Compute (test_mul mul_v1_alt).

Lemma mul_v1_and_mul_v1_alt_are_equivalent_aux :
  forall i j a : nat,
    mul_v1_aux i j a = nat_fold_left nat a (fun ih : nat => j + ih) i.
Proof.
  intros i j.
  induction i as [ | i' IHi'].
  - intro a.
    rewrite -> (fold_unfold_mul_v1_aux_O j a).
    rewrite -> (fold_unfold_nat_fold_left_O nat a (fun ih : nat => j + ih)).
    reflexivity.
  - intro a.
    rewrite -> (fold_unfold_mul_v1_aux_S i' j a).
    rewrite -> (fold_unfold_nat_fold_left_S nat a (fun ih : nat => j + ih) i').
    Check (IHi' (j + a)).
    exact (IHi' (j + a)).
Qed.

Proposition mul_v1_and_mul_v1_alt_are_equivalent :
  forall i j : nat,
    mul_v1 i j = mul_v1_alt i j.
Proof.
  intros i j.
  unfold mul_v1, mul_v1_alt.
  exact (mul_v1_and_mul_v1_alt_are_equivalent_aux i j 0).
Qed.

(* Exercise 2c *)

Corollary mul_v0_and_mul_v1_are_equivalent_alt :
  forall i j : nat,
    mul_v0 i j = mul_v1 i j.
Proof.
  intros i j.
  rewrite -> (mul_v0_and_mul_v0_alt_are_equivalent i j).
  rewrite -> (mul_v1_and_mul_v1_alt_are_equivalent i j).
  unfold mul_v0_alt, mul_v1_alt.
  symmetry.
  exact (folding_left_and_right nat 0 (fun ih : nat => j + ih) i).
Qed.


(* ********** *)

(* Exercise 3 *)

(* The sumtorial function *)

Definition specification_of_sum_n (sum_n :  nat -> nat) :=
  (sum_n 0 = 0)
  /\
  (forall n' : nat,
      sum_n (S n') = (S n') + sum_n n').

(* ***** *)


Proposition there_is_at_most_one_function_satisfying_the_specification_of_sum_n :
  forall sum_n1 sum_n2 :  nat -> nat,
    specification_of_sum_n sum_n1 ->
    specification_of_sum_n sum_n2 ->
    forall n : nat,
      sum_n1 n = sum_n2 n.
Proof.
  intros sum_n1 sum_n2.
  unfold specification_of_sum_n.
  intros [S1_O S1_S] [S2_O S2_S] n.
  induction n as [ | n' IHn']. 
  - rewrite -> (S2_O).
    exact (S1_O).
  - rewrite -> (S1_S n').
    rewrite -> (S2_S n').
    rewrite -> IHn'.
    reflexivity.
Qed.
(* ***** *)

Definition test_sum_n (candidate : nat  -> nat) : bool :=
  (candidate 1 =? 1) &&
  (candidate 2 =? 3) &&
  (candidate 3 =? 6) &&
  (candidate 10 =? 55)
.

(* ***** *)

Fixpoint sum_n_v0_aux (n : nat) : nat :=
  match n with
  | O =>
    0
  | S n' =>
    S n' + (sum_n_v0_aux n')
  end.

Definition sum_n_v0 (n : nat) : nat :=
  sum_n_v0_aux n.
 
Compute (test_sum_n sum_n_v0). 

Lemma fold_unfold_sum_n_v0_aux_O :
   sum_n_v0_aux 0 = 0.
Proof.
  fold_unfold_tactic sum_n_v0_aux.
Qed.

Lemma fold_unfold_sum_n_v0_aux_S :
  forall n' : nat,
    sum_n_v0_aux (S n') = (S n') + sum_n_v0_aux n'.
Proof.
  fold_unfold_tactic sum_n_v0_aux.
Qed.

Proposition sum_n_v0_safisfies_the_specification_of_sum_n :
  specification_of_sum_n sum_n_v0.
Proof.
  unfold specification_of_sum_n, sum_n_v0.
  split.
  - exact fold_unfold_sum_n_v0_aux_O.
  - exact fold_unfold_sum_n_v0_aux_S.
Qed.

(* ***** *)

Fixpoint sum_n_v1_aux (n a : nat) : nat :=
  match n with
  | O =>
    a
  | S n' =>
    sum_n_v1_aux n' ( (S n') + a)
  end.

Definition sum_n_v1 (n : nat) : nat :=
  sum_n_v1_aux n 0.
 
Compute (test_sum_n sum_n_v1).

Lemma fold_unfold_sum_n_v1_aux_O :
  forall a : nat,
    sum_n_v1_aux 0 a =
    a.
Proof.
  fold_unfold_tactic sum_n_v1_aux.
Qed.

Lemma fold_unfold_sum_n_v1_aux_S :
  forall n' a : nat,
    sum_n_v1_aux (S n') a =
    sum_n_v1_aux n' ((S n') + a).
Proof.
  fold_unfold_tactic sum_n_v1_aux.
Qed.

(* ***** *)

(* Eureka lemma: *)

Lemma about_sum_n_v0_aux_and_sum_n_v1_aux :
  forall n a : nat,
    sum_n_v0_aux n + a = sum_n_v1_aux n a.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - intro a.
    rewrite -> (fold_unfold_sum_n_v0_aux_O).
    rewrite -> (fold_unfold_sum_n_v1_aux_O a).
    Search(0+_).
    exact (Nat.add_0_l a).
  - intro a.
    rewrite -> (fold_unfold_sum_n_v0_aux_S n').
    rewrite -> (fold_unfold_sum_n_v1_aux_S n' a).
    Check (IHn' ((S n') + a)).
    rewrite <- (IHn' ((S n') + a)).
    rewrite -> (Nat.add_comm (S n') (sum_n_v0_aux n')).
    Check (Nat.add_assoc).
    symmetry.
    exact (Nat.add_assoc (sum_n_v0_aux n') (S n') a).
Qed.

Theorem sum_n_v0_and_sum_n_v1_are_equivalent :
  forall n : nat,
    sum_n_v0 n = sum_n_v1 n.
Proof.
  intros n.
  unfold sum_n_v0, sum_n_v1.
  Check (about_sum_n_v0_aux_and_sum_n_v1_aux n 0).
  rewrite <- (Nat.add_0_r (sum_n_v0_aux n)).
  exact (about_sum_n_v0_aux_and_sum_n_v1_aux n 0).
Qed.

(* ********** *)
(* ********** *)

(* Remark: partitially inspired by Section 2.4 of Prof Danvy's paper "Folding left and right over Peano numbers" *)

(* <OD> *)

(*
Definition sum_n_v0_alt_helper (n : nat) : nat * nat :=
  nat_fold_right (nat * nat)
                 (0,0)
                 (fun c => let (ind, sum) := c in (ind + 1, sum + ind + 1))
                 n.
*)

Definition sum_n_v0_alt_helper (n : nat) : nat * nat :=
  nat_fold_right (nat * nat)
                 (0, 0)
                 (fun c => let (ind, sum) := c in (S ind, S ind + sum))
                 n.

Definition sum_n_v0_alt (n : nat) : nat :=
   let (ind, sum) := sum_n_v0_alt_helper n in sum.
     
Compute (test_sum_n sum_n_v0_alt).

Lemma about_sum_n_v0_alt_helper :
  forall n ind res: nat,
    nat_fold_right (nat * nat)
                   (0, 0)
                   (fun c => let (ind, sum) := c in (S ind, S ind + sum))
                   n = (ind, res) ->
    n = ind.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - intros ind res.
    rewrite -> (fold_unfold_nat_fold_right_O (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum))).
    intros H_tmp.
    injection H_tmp as H_ind H_res.
    exact H_ind.
  - intros ind res.
    rewrite -> (fold_unfold_nat_fold_right_S (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum)) n').
    case (nat_fold_right (nat * nat) (0, 0) (fun c : nat * nat => let (ind0, sum) := c in (S ind0, S ind0 + sum)) n') as (x, y).
    intro H_tmp.
    injection H_tmp as H_ind H_res.
    rewrite <- H_ind.
    Check (IHn' x y).
    Check (IHn' x y (eq_refl (x, y))).
    rewrite <- (IHn' x y (eq_refl (x, y))).
    reflexivity.
Qed.

(* NO PROBLEM HERE *)

Proposition sum_n_v0_alt_safisfies_the_specification_of_sum_n :
  specification_of_sum_n sum_n_v0_alt.
Proof.
  unfold specification_of_sum_n, sum_n_v0_alt.
  Check specification_of_sum_n.
  split.     
  - destruct (sum_n_v0_alt_helper 0) as (_, sum_n_O).
    rewrite <- (sum_n_v0_alt 0).
    Check sum_n_O.
    Check (fold_unfold_nat_fold_right_O (nat * nat) (_,sum_n_O) (fun c => let (_, sum_n_O) := c in (_, sum_n_O +_+ 1))).
=======
  unfold specification_of_sum_n, sum_n_v0_alt, sum_n_v0_alt_helper.
  split.     
  - rewrite -> (fold_unfold_nat_fold_right_O (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum))).
    reflexivity.
>>>>>>> 98035c6356c96242f70ffd7a101fd8d1c8d19331
=======
  unfold specification_of_sum_n, sum_n_v0_alt, sum_n_v0_alt_helper.
  split.     
  - rewrite -> (fold_unfold_nat_fold_right_O (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum))).
    reflexivity.
>>>>>>> 98035c6356c96242f70ffd7a101fd8d1c8d19331
  - intro n'.
    rewrite -> (fold_unfold_nat_fold_right_S (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum)) n').
    destruct (nat_fold_right (nat * nat) (0, 0) (fun c : nat * nat => let (ind, sum) := c in (S ind, S ind + sum)) n') as (ind, res) eqn:H_witness.
    Check (about_sum_n_v0_alt_helper n' ind res H_witness).
    rewrite <- (about_sum_n_v0_alt_helper n' ind res H_witness).
    reflexivity.
Qed.

Corollary sum_n_v0_and_sum_n_v0_alt_are_equivalent :
  forall n : nat,
    sum_n_v0 n = sum_n_v0_alt n.
Proof.
  intros n.
  exact (there_is_at_most_one_function_satisfying_the_specification_of_sum_n
           sum_n_v0
           sum_n_v0_alt
           sum_n_v0_safisfies_the_specification_of_sum_n
           sum_n_v0_alt_safisfies_the_specification_of_sum_n
           n).
Qed.
(* ***** *)


Definition sum_n_v1_alt_helper (n : nat) : nat * nat :=
  nat_fold_left (nat * nat)
                 (0,0)
                 (fun c => let (ind, sum) := c in (ind + 1, sum + ind + 1))
                 n.
Definition sum_n_v1_alt (n : nat) : nat :=
   let (ind,sum) := sum_n_v0_alt_helper n in sum.
     
Compute (test_sum_n sum_n_v1_alt).

Lemma sum_n_v1_and_sum_n_v1_alt_are_equivalent_aux :
  forall n a : nat,
    sum_n_v1_aux n a = sum_n_v1_alt n.
Proof.
Admitted.

Proposition sum_n_v1_and_sum_n_v1_alt_are_equivalent :
  forall n : nat,
    sum_n_v1 n = sum_n_v1_alt n.
Proof.
  intro  n.
  unfold sum_n_v1, sum_n_v1_alt.
  exact (sum_n_v1_and_sum_n_v1_alt_are_equivalent_aux n 0).
Qed.

(* ********** *)

Corollary sum_n_v0_and_sum_n_v1_are_equivalent_alt :
  forall n : nat,
    sum_n_v0 n = sum_n_v1 n.
Proof.
  intros n.
  rewrite -> (sum_n_v0_and_sum_n_v0_alt_are_equivalent n).
  rewrite -> (sum_n_v1_and_sum_n_v1_alt_are_equivalent n). 
  unfold sum_n_v0_alt, sum_n_v1_alt.
  symmetry.
  reflexivity.
Qed.


(* end of week-05_folding-left-and-right-over-peano-numbers.v *)
