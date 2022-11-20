(* 8_informal_proofs.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 19 Oct 2020 *)

(* ********** *)

Require Import Arith Bool.

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Inductive m22 : Type :=
| M22 : nat -> nat -> nat -> nat -> m22.

Definition m22_add (x y : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    match y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 + y11) (x12 + y12)
          (x21 + y21) (x22 + y22)
    end
  end.

Definition m22_zero :=
  M22 0 0
      0 0.

Definition m22_one :=
  M22 1 0
      0 1.

(* ex1a Defintion 9 *)

Definition m22_mult (x y : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    match y with
    | M22 y11 y12
          y21 y22 =>
      M22 (x11 * y11 + x12 * y21) (x11 * y12 + x12 * y22)
          (x21 * y11 + x22 * y21) (x21 * y12 + x22 * y22)
    end
  end.

(* ex1b Property 10 *)

Proposition property_10 :
  forall m22_1 m22_2 m22_3 : m22,
    m22_mult m22_1 (m22_mult m22_2 m22_3) = m22_mult (m22_mult m22_1 m22_2) m22_3.
Proof.
  intros [x11 x12 x21 x22]
         [y11 y12 y21 y22]
         [z11 z12 z21 z22].
  unfold m22_mult.
  rewrite ->8 Nat.mul_add_distr_l.
  rewrite ->16 Nat.mul_assoc.
  rewrite ->2 (Nat.add_shuffle1 _ (x11 * y12 * _) _ _).
  rewrite ->2 (Nat.add_shuffle1 _ (x21 * y12 * _) _ _).
  rewrite ->8 Nat.mul_add_distr_r.
  reflexivity.
Qed.

(* ex1c Property 12 *)

Proposition property_12_1 :
  forall m22' : m22,
    m22_mult m22_one m22' = m22'.
Proof.
  intros [x11' x12' x21' x22'].
  unfold m22_mult, m22_one.
  rewrite ->4 Nat.mul_1_l.
  rewrite ->4 Nat.mul_0_l.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  reflexivity.
Qed.

Proposition property_12_2 :
  forall m22' : m22,
    m22' = m22_mult m22' m22_one.
Proof.
  intros [x11' x12' x21' x22'].
  unfold m22_mult, m22_one.
  rewrite ->4 Nat.mul_1_r.
  rewrite ->4 Nat.mul_0_r.
  rewrite ->2 Nat.add_0_l.
  rewrite ->2 Nat.add_0_r.
  reflexivity.
Qed.

(* ex1d Defintion 13 *)

Fixpoint m22_exp (x : m22) (n : nat) : m22 :=
  match n with
  | O => m22_one
  | S n' =>
    m22_mult (m22_exp x n') x
  end.

Lemma fold_unfold_lemma_m22_exp_O :
  forall (x : m22),
    m22_exp x O = m22_one.
Proof.
  fold_unfold_tactic m22_exp.
Qed.

Lemma fold_unfold_lemma_m22_exp_S :
  forall (x : m22)
         (n' : nat),
    m22_exp x (S n') = m22_mult (m22_exp x n') x.
Proof.
  fold_unfold_tactic m22_exp.
Qed.

Corollary m22_exp_1 :
  forall (x : m22),
    m22_exp x 1 = x.
Proof.
  intro x.
  rewrite -> (fold_unfold_lemma_m22_exp_S x 0).
  rewrite -> (fold_unfold_lemma_m22_exp_O x).
  exact (property_12_1 x).
Qed.
(* ex1e Proposition 14 *)

Proposition proposition_14 :
  forall n : nat,
    m22_exp (M22 1 1
                 0 1)
            n =
    M22 1 n
        0 1.
Proof.
  intro n.
  induction n as [ | n' IHn' ].
  - exact (fold_unfold_lemma_m22_exp_O (M22 1 1 0 1)).
  - rewrite -> (fold_unfold_lemma_m22_exp_S (M22 1 1 0 1) n').
    rewrite -> IHn'.
    unfold m22_mult.
    rewrite ->2 Nat.mul_1_l.
    rewrite -> Nat.mul_0_l.
    rewrite -> Nat.mul_0_r.
    rewrite -> Nat.mul_1_r.
    rewrite ->2 Nat.add_0_r.
    rewrite -> Nat.add_0_l.
    Search (1 + _ = _).
    rewrite -> (Nat.add_1_l n').
    reflexivity.
Qed.

(* ex1f
The logic is the same; there are more steps involved in proving the equivalence by definition of matrix multiplication.
 *)

(* ex1g Exercise 25 *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => O
  | S n' => match n' with
            | O => 1
            | S n'' => fib n' + fib n''
            end
  end.

Lemma fold_unfold_fib_O :
  fib O = 0.
Proof.
  fold_unfold_tactic fib.
Qed.

Lemma fold_unfold_fib_S :
  forall n' : nat,
    fib (S n') =
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''
    end.
Proof.
  fold_unfold_tactic fib.
Qed.

Corollary fold_unfold_fib_1 :
  fib 1 = 1.
Proof.
  rewrite -> (fold_unfold_fib_S 0).
  reflexivity.
Qed.

Property exponentiation_of_a_special_m22_contains_all_fib_numbers :
  forall (n : nat),
    m22_exp (M22 1 1
                 1 0)
            (S n) = M22 (fib (S (S n))) (fib (S n))
                        (fib (S n)) (fib n).
Proof.
  intro n.
  induction n as [ | n' IHn' ].
  - rewrite -> (m22_exp_1 (M22 1 1 1 0)).
    rewrite -> (fold_unfold_fib_S 1).
    rewrite -> fold_unfold_fib_O.
    rewrite -> fold_unfold_fib_1.
    rewrite -> (Nat.add_0_r 1).
    reflexivity.
  - rewrite -> (fold_unfold_lemma_m22_exp_S (M22 1 1 1 0) (S n')).
    rewrite -> IHn'.
    unfold m22_mult.
    rewrite ->2 Nat.mul_0_r.
    rewrite ->3 Nat.mul_1_r.
    rewrite ->2 Nat.add_0_r.
    rewrite <- (fold_unfold_fib_S (S (S n'))).
    rewrite <- (fold_unfold_fib_S (S n')).
    reflexivity.
Qed.


(* ex1h Definition 27 *)

Fixpoint m22_exp_v1 (x : m22) (n : nat) : m22 :=
  match n with
  | O => m22_one
  | S n' =>
    m22_mult x (m22_exp_v1 x n')
  end.

Lemma fold_unfold_lemma_m22_exp_v1_O :
  forall (x : m22),
    m22_exp_v1 x O = m22_one.
Proof.
  fold_unfold_tactic m22_exp_v1.
Qed.

Lemma fold_unfold_lemma_m22_exp_v1_S :
  forall (x : m22)
         (n' : nat),
    m22_exp_v1 x (S n') = m22_mult x (m22_exp_v1 x n').
Proof.
  fold_unfold_tactic m22_exp.
Qed.

(* ex1i are Definitions 13 and 27 equivalent? *)

Proposition m22_exp_can_be_written_as_mult_of_two_m22_exp_functions :
  forall (x : m22)
         (m n : nat),
    m22_exp x (m + n) = m22_mult (m22_exp x n) (m22_exp x m).
Proof.
  intros x m.
  induction m as [ | m' IHm'].
  - intro n.
    rewrite -> (Nat.add_0_l n).
    rewrite -> (fold_unfold_lemma_m22_exp_O x).
    exact (property_12_2 (m22_exp x n)).
  - intro n.
    rewrite -> (Nat.add_succ_l m' n).
    rewrite -> (fold_unfold_lemma_m22_exp_S x (m' + n)).
    rewrite -> (fold_unfold_lemma_m22_exp_S x m').
    rewrite -> IHm'.
    symmetry.
    exact (property_10 (m22_exp x n) (m22_exp x m') x).
Qed.

Corollary corollary_about_m22_exp_S :
  forall (x : m22)
         (n' : nat),
    m22_exp x (S n') = m22_mult x (m22_exp x n').
Proof.
  intros x n'.
  rewrite <- (Nat.add_1_r n').
  rewrite -> (m22_exp_can_be_written_as_mult_of_two_m22_exp_functions x n' 1).
  rewrite -> (m22_exp_1 x).
  reflexivity.
Qed.

Proposition m22_exp_and_m22_exp_v1_are_equavalent :
  forall (x : m22)
         (n : nat),
    m22_exp_v1 x n = m22_exp x n.
Proof.
  intros x n.
  induction n as [ | n' IHn' ].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    exact (fold_unfold_lemma_m22_exp_v1_O x).
  - rewrite -> (fold_unfold_lemma_m22_exp_v1_S x n').
    rewrite -> IHn'.
    symmetry.
    exact (corollary_about_m22_exp_S x n').
Qed.

(* alternative proofs *)

Proposition mult_transitivity_in_m22_exp :
  forall (x : m22)
         (n : nat),
    m22_mult x (m22_exp x n) = m22_mult (m22_exp x n) x.
Proof.
  intros x n.
  induction n as [ | n' IHn' ].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    rewrite -> (property_12_1 x).
    symmetry.
    exact (property_12_2 x).
  - rewrite -> (fold_unfold_lemma_m22_exp_S x n').
    rewrite -> (property_10 x (m22_exp x n') x).
    rewrite -> IHn'.
    reflexivity.
Qed.

Proposition mult_transitivity_in_m22_exp_v1 :
  forall (x : m22)
         (n : nat),
    m22_mult x (m22_exp_v1 x n) = m22_mult (m22_exp_v1 x n) x.
Proof.
  intros x n.
  induction n as [ | n' IHn' ].
  - rewrite -> (fold_unfold_lemma_m22_exp_v1_O x).
    rewrite -> (property_12_1 x).
    symmetry.
    exact (property_12_2 x).
  - rewrite -> (fold_unfold_lemma_m22_exp_v1_S x n').
    rewrite <- (property_10 x (m22_exp_v1 x n') x).
    rewrite -> IHn'.
    reflexivity.
Qed.

Proposition m22_exp_and_m22_exp_v1_are_equavalent_alternative :
  forall (x : m22)
         (n : nat),
    m22_exp x n = m22_exp_v1 x n.
Proof.
  intros x n.
  induction n as [ | n' IHn' ].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    rewrite -> (fold_unfold_lemma_m22_exp_v1_O x).
    reflexivity.
  - rewrite -> (fold_unfold_lemma_m22_exp_S x n').
    rewrite -> (fold_unfold_lemma_m22_exp_v1_S x n').
    rewrite <- (mult_transitivity_in_m22_exp x n').
    rewrite -> IHn'.
    reflexivity.

  Restart.

  intros x n.
  induction n as [ | n' IHn' ].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    rewrite -> (fold_unfold_lemma_m22_exp_v1_O x).
    reflexivity.
  - rewrite -> (fold_unfold_lemma_m22_exp_S x n').
    rewrite -> (fold_unfold_lemma_m22_exp_v1_S x n').
    rewrite -> (mult_transitivity_in_m22_exp_v1 x n').
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ex1j Definition 35 *)

Definition m22_transpose (x : m22) : m22 :=
  match x with
  | M22 x11 x12
        x21 x22 =>
    M22 x11 x21
        x12 x22
  end.

(* ex1k Property 36 *)
Proposition transpose_is_involutory :
  forall x : m22,
    m22_transpose (m22_transpose x) = x.
Proof.
  intros [x11 x12 x21 x22].
  unfold m22_transpose.
  reflexivity.
Qed.

(* ex1l Proposition 38 *)

Proposition proposition_29 :
  forall (x : m22)
         (n : nat),
    m22_mult x (m22_exp x n) = m22_mult (m22_exp x n) x.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    rewrite -> (property_12_1 x).
    rewrite <- (property_12_2 x).
    reflexivity.
  - rewrite -> (fold_unfold_lemma_m22_exp_S x n').
    rewrite -> (property_10 x (m22_exp x n') x).
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma lemma_37 :
  forall (x y : m22),
    m22_transpose (m22_mult x y) = m22_mult (m22_transpose y) (m22_transpose x).
Proof.
  intros [x11 x12 x21 x22]
         [y11 y12 y21 y22].
  unfold m22_transpose, m22_mult.
  Search (_ * _).
  rewrite -> (Nat.mul_comm y11 x11).
  rewrite -> (Nat.mul_comm y21 x12).
  rewrite -> (Nat.mul_comm y11 x21).
  rewrite -> (Nat.mul_comm y21 x22).
  rewrite -> (Nat.mul_comm y12 x11).
  rewrite -> (Nat.mul_comm y22 x12).
  rewrite -> (Nat.mul_comm y12 x21).
  rewrite -> (Nat.mul_comm y22 x22).
  reflexivity.
Qed.


Proposition m22_transpose_m22_one_is_m22_one :
  m22_transpose m22_one = m22_one.
Proof.
  fold_unfold_tactic m22_exp.
Qed.

Proposition proposition_38 :
  forall (x : m22)
         (n : nat),
  m22_transpose (m22_exp x n) = m22_exp (m22_transpose x) n.
Proof.
  intros x n.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_lemma_m22_exp_O x).
    rewrite -> (fold_unfold_lemma_m22_exp_O (m22_transpose x)).
    rewrite -> (m22_transpose_m22_one_is_m22_one).
    reflexivity.
  - rewrite (fold_unfold_lemma_m22_exp_S x n').
    rewrite -> (lemma_37 (m22_exp x n') x).
    rewrite -> (IHn').
    rewrite -> (proposition_29 (m22_transpose x)).
    rewrite -> (fold_unfold_lemma_m22_exp_S (m22_transpose x) n').
    reflexivity.
Qed.

(* ex1m *)

Lemma transposing_m22s :
  m22_transpose (M22 1 1 0 1) = (M22 1 0 1 1).
Proof.
  unfold m22_transpose.
  reflexivity.
Qed.
  
Proposition proposition_33 :
  forall n : nat,
    m22_exp (M22 1 0
                 1 1) n = M22 1 0
                              n 1.
Proof.
  intro n.
  induction n as [ | n IHn'].
  - rewrite -> (fold_unfold_lemma_m22_exp_O (M22 1 0 1 1)).
    unfold m22_one.
    reflexivity.
  - rewrite -> (fold_unfold_lemma_m22_exp_S (M22 1 0 1 1) n).
    rewrite -> IHn'.
    unfold m22_mult.
    Search (_ * 1).
    Search (0 * _).
    rewrite -> (Nat.mul_1_r).
    rewrite -> (Nat.mul_0_l).
    rewrite -> (Nat.mul_0_r).
    rewrite -> (Nat.mul_1_r n).
    rewrite -> (Nat.mul_0_r n).
    Search (_ + 0).
    rewrite -> (Nat.add_0_r).
    rewrite -> (Nat.add_0_r).
    rewrite -> (Nat.add_0_l).
    Search (_ + 1).
    rewrite -> (Nat.add_1_r n).
    reflexivity.

    Restart.
    intro n.
    rewrite <- transposing_m22s.
    rewrite <- (proposition_38 (M22 1 1 0 1) n).
    rewrite -> proposition_14.
    unfold m22_transpose.
    reflexivity.
Qed.



(* Exercise 2 : Matrices of matrices*)

(* Part a : Implementation *)

Inductive mm22 : Type :=
| MM22 : m22 -> m22 -> m22 -> m22 -> mm22.


Definition mm22_add (x y: mm22) : mm22 :=
  match x with
  | MM22 x11 x12
         x21 x22 =>
    match y with
    | MM22 y11 y12
           y21 y22 =>
      MM22 (m22_add x11 y11) (m22_add x12 y12)
           (m22_add x21 y21) (m22_add x22 y22)
    end
  end.

Definition mm22_zero :=
  MM22 m22_zero m22_zero
       m22_zero m22_zero.

Definition mm22_one :=
  MM22 m22_one m22_zero
       m22_zero m22_one.

(* matrix multiplicaiton *)
Definition mm22_mult (x y: mm22) : mm22 :=
  match x with
  | MM22 x11 x12
         x21 x22 =>
    match y with
    | MM22 y11 y12
           y21 y22 =>
      MM22 (m22_add (m22_mult x11  y11) (m22_mult x12 y21)) (m22_add (m22_mult x11  y12) (m22_mult x12 y22))
           (m22_add (m22_mult x21  y11) (m22_mult x22 y21)) (m22_add (m22_mult x21  y12) (m22_mult x22 y22))
    end
  end.

Fixpoint mm22_exp_aux (x : mm22)(n : nat) : mm22 :=
  match n with
  | O =>
    mm22_one
  | S n' =>
    mm22_mult x (mm22_exp_aux x n')
  end.

Definition mm22_exp (x : mm22)(n : nat) : mm22 :=
  mm22_exp_aux x n.

Lemma fold_unfold_lemma_mm22_exp_aux_O :
  forall (x : mm22),
    mm22_exp_aux x 0 =
    mm22_one.
Proof.
  fold_unfold_tactic mm22_exp_aux.
Qed.

Lemma fold_unfold_lemma_mm22_exp_aux_S :
    forall (x : mm22)
           (n' : nat),
      mm22_exp_aux x (S n') =
      mm22_mult x (mm22_exp_aux x n').
Proof.
  fold_unfold_tactic mm22_exp_aux.
Qed.

(* Part b : Property of Fibonacci Matrix *)

(* ex1g Exercise 25 *)

Definition F :=
  (M22 1 1
       1 0).

Fixpoint FIB (n : nat) : m22 :=
  match n with
  | O => m22_one
  | S n' => match n' with
            | O => F
            | S n'' => (m22_add (FIB n') (FIB n''))
            end
  end.

Lemma fold_unfold_FIB_O :
  FIB O = m22_one.
Proof.
  fold_unfold_tactic FIB.
Qed.

Lemma fold_unfold_FIB_S :
  forall n' : nat,
    FIB (S n') =
    match n' with
    | 0 => F
    | S n'' => (m22_add (FIB n') (FIB n''))
    end.
Proof.
  fold_unfold_tactic FIB.
Qed.

Corollary fold_unfold_FIB_1 :
  FIB 1 = F.
Proof.
  rewrite -> (fold_unfold_FIB_S 0).
  reflexivity.
Qed.
(*
Proposition equivalence_of_FIB_and_fib :
   forall 
         ()
         (oov1 oov2 : option (option V)),
    option_option_eqb V V_eqb oov1 oov2 = option_option_eqb'' V V_eqb oov1 oov2.)
*)
Lemma FIB_n_is_equal_to_F_power_n :
  forall (n : nat),
    FIB (S n) = (m22_mult
                   F (m22_exp F n)).
Proof.
  intro n.
  unfold F.
  induction n as [ | n' IHn'].
  - rewrite -> (fold_unfold_lemma_m22_exp_O (M22 1 1 1 0)).
    unfold m22_one.
    unfold m22_mult.
    rewrite ->2 Nat.mul_1_l.
    rewrite -> Nat.mul_1_r.
    rewrite -> Nat.mul_0_r.
    rewrite ->2 Nat.add_0_r.
    rewrite -> Nat.add_0_l.
    fold F.
    exact fold_unfold_FIB_1.
  - rewrite -> (fold_unfold_lemma_m22_exp_S (M22 1 1 1 0) n').
    rewrite -> (fold_unfold_FIB_S (S n')).
    fold F. 
    admit.
    Admitted.
    (*
Compute (mm22_exp_aux (MM22 (M22 1 0
                                 0 1) (M22 1 1
                                           1 0)
                            (M22 1 1
                                 1 0) (M22 2 1
                                           1 1)) 1).


Examples:
n = 1:
     = MM22 (M22 1 0 0 1) (M22 1 1 1 0) (M22 1 1 1 0) (M22 2 1 1 1)
n = 2:
     = MM22 (M22 3 1 1 2) (M22 4 3 3 1) (M22 4 3 3 1) (M22 7 4 4 3)
n = 3:
     = MM22 (M22 10 5 5 5) (M22 15 10 10 5) (M22 15 10 10 5) (M22 25 15 15 10)
n = 4:
     = MM22 (M22 35 20 20 15) (M22 55 35 35 20) (M22 55 35 35 20) (M22 90 55 55 35)
     *)

Theorem about_exponentiation_of_F :
  forall (n : nat),
    mm22_exp (MM22 (M22 1 0 0 1) (M22 1 1 1 0)
                   (M22 1 1 1 0) (M22 2 1 1 1))
             (S n) =
    (MM22 (FIB n)     (FIB (S n))
          (FIB (S n)) (FIB (S (S n)))).
Proof.
  intro n.
  induction n as [ | n' IHn'].
  - unfold mm22_exp.
    rewrite -> (fold_unfold_lemma_mm22_exp_aux_S (MM22 (M22 1 0 0 1) (M22 1 1 1 0)
                                                       (M22 1 1 1 0) (M22 2 1 1 1)) 0).
    rewrite -> (fold_unfold_lemma_mm22_exp_aux_O (MM22 (M22 1 0 0 1) (M22 1 1 1 0)
                                                       (M22 1 1 1 0) (M22 2 1 1 1))).
    unfold mm22_one.
    unfold m22_zero.
    unfold m22_one.
    unfold mm22_mult. 
    unfold mm22_add.     
    rewrite -> (fold_unfold_FIB_S 1).
    rewrite -> fold_unfold_FIB_O.
    rewrite -> fold_unfold_FIB_1.
    unfold F.
    unfold m22_one.
    unfold m22_mult.
    unfold m22_add.
    rewrite ->2 Nat.mul_0_l.
    rewrite ->2 Nat.mul_0_r. 
    rewrite ->7 Nat.add_0_l.
    rewrite ->4 Nat.add_0_r.
    rewrite -> Nat.mul_1_l.
    rewrite ->1 Nat.mul_1_r.
    rewrite -> Nat.add_1_r.    
    reflexivity.
  - unfold mm22_exp.
    rewrite -> (fold_unfold_lemma_mm22_exp_aux_S (MM22 (M22 1 0 0 1) (M22 1 1 1 0)
                                                       (M22 1 1 1 0) (M22 2 1 1 1)) (S n')).
    unfold mm22_exp in IHn'.
    rewrite -> IHn'.
    Check (fold_unfold_FIB_S (S n')).
    rewrite -> (fold_unfold_FIB_S (S n')).
    unfold mm22_mult.
    Check (fold_unfold_FIB_S (S n')).

    assert (H_identity := property_12_1).
    unfold m22_one in H_identity.

    rewrite -> (H_identity (FIB n')).   
    rewrite -> (H_identity (FIB (S n'))).

Qed.

(* end of week-09_informal_proofs.v *)
