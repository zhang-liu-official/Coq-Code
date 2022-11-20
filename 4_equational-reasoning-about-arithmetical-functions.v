(* 4_equational-reasoning-about-arithmetical-functions.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 05 Sep 2020 *)

(* ********** *)

(* Exercise 9 *)

(* Prove foo:

   (1) backward, in a goal-directed way

   (2) forward, from the assumptions
*)

Proposition foo :
  forall P Q R1 R2 : Prop,
    P -> (P -> Q) -> (Q -> R1) /\ (Q -> R2) -> R1 /\ R2.
Proof.
  (* backward proof *)
  intros P Q R1 R2 H_P H_P_implies_H_Q [H_Q_implies_R1 H_Q_implies_R2].
  split.
  - apply H_Q_implies_R1.
    apply H_P_implies_H_Q.
    apply H_P.
  - apply H_Q_implies_R2.
    apply H_P_implies_H_Q.
    apply H_P. 
    Show Proof. 

(*
(fun (P Q R1 R2 : Prop)
   (H_P : P)
   (H_P_implies_H_Q : P -> Q)
   (H : (Q -> R1) /\ (Q -> R2))
 =>
 match H with
 | conj H_Q_implies_R1
   H_Q_implies_R2 =>
     conj
       (H_Q_implies_R1
          (H_P_implies_H_Q H_P))
       (H_Q_implies_R2
          (H_P_implies_H_Q H_P))
 end)
*)
    Restart. 

    (* forward proof *)
    intros P Q R1 R2 H_P H_P_implies_H_Q [H_Q_implies_R1 H_Q_implies_R2].
    assert (H_Q := H_P_implies_H_Q H_P).
    exact (conj (H_Q_implies_R1 H_Q) (H_Q_implies_R2 H_Q)).
    Show Proof. 
(*
(fun (P Q R1 R2 : Prop) (H_P : P) (H_P_implies_H_Q : P -> Q) (H : (Q -> R1) /\ (Q -> R2))
 =>
 match H with
 | conj H_Q_implies_R1 H_Q_implies_R2 =>
     let H_Q : Q := H_P_implies_H_Q H_P in conj (H_Q_implies_R1 H_Q) (H_Q_implies_R2 H_Q)
 end)
*)
Qed.

(* ********** *)

(* Exercise 10 *)

(* Prove bar:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition bar :
  forall P1 P2 Q R1 R2 T1 T2 : Prop,
    P1 -> (P1 -> P2) -> (P2 -> Q) -> (Q -> R1) -> (R1 -> T1) -> (Q -> R2) -> (R2 -> T2) -> T1 /\ T2.
Proof.
  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  (* Here, use the split tactic as early as possible. *)

  split.
  - apply H_R1_implies_T1.
    apply H_Q_implies_R1.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    apply H_P1.
  - apply H_R2_implies_T2.
    apply H_Q_implies_R2.
    apply H_P2_implies_Q.
    apply H_P1_implies_P2.
    apply H_P1.
    Show Proof. 
(*
(fun
   (P1 P2 Q R1 R2 T1
    T2 : Prop) (H_P1 : P1)
   (H_P1_implies_P2 : 
    P1 -> P2)
   (H_P2_implies_Q : P2 -> Q)
   (H_Q_implies_R1 : Q -> R1)
   (H_R1_implies_T1 : 
    R1 -> T1)
   (H_Q_implies_R2 : Q -> R2)
   (H_R2_implies_T2 : 
    R2 -> T2) =>
 conj
   (H_R1_implies_T1
      (H_Q_implies_R1
         (H_P2_implies_Q
            (H_P1_implies_P2
               H_P1))))
   (H_R2_implies_T2
      (H_Q_implies_R2
         (H_P2_implies_Q
            (H_P1_implies_P2
               H_P1)))))
*)
  Restart.

  intros P1 P2 Q R1 R2 T1 T2.
  intros H_P1 H_P1_implies_P2 H_P2_implies_Q H_Q_implies_R1 H_R1_implies_T1 H_Q_implies_R2 H_R2_implies_T2.

  (* Here, use the split tactic as late as possible. *)

  (*  P1 -> (P1 -> P2) -> (P2 -> Q) -> (Q -> R1) -> (R1 -> T1) -> (Q -> R2) -> (R2 -> T2) -> T1 /\ T2. *)

  Check (H_P1_implies_P2 H_P1).
  assert (H_P2 := H_P1_implies_P2 H_P1).
  Check (H_P2_implies_Q H_P2).
  assert (H_Q := H_P2_implies_Q H_P2).
  assert (H_R1 := H_Q_implies_R1 H_Q).
  assert (H_R2 := H_Q_implies_R2 H_Q).
  assert (H_T1 := H_R1_implies_T1 H_R1).
  assert (H_T2 := H_R2_implies_T2 H_R2).
  split.
  - exact H_T1.
  - exact H_T2. 
    Show Proof.
(*
(fun (P1 P2 Q R1 R2 T1 T2 : Prop) (H_P1 : P1) (H_P1_implies_P2 : P1 -> P2)
   (H_P2_implies_Q : P2 -> Q) (H_Q_implies_R1 : Q -> R1) (H_R1_implies_T1 : R1 -> T1)
   (H_Q_implies_R2 : Q -> R2) (H_R2_implies_T2 : R2 -> T2) =>
 let H_P2 : P2 := H_P1_implies_P2 H_P1 in
 let H_Q : Q := H_P2_implies_Q H_P2 in
 let H_R1 : R1 := H_Q_implies_R1 H_Q in
 let H_R2 : R2 := H_Q_implies_R2 H_Q in
 let H_T1 : T1 := H_R1_implies_T1 H_R1 in
 let H_T2 : T2 := H_R2_implies_T2 H_R2 in conj H_T1 H_T2)
*)
Qed.

(* ********** *)

(* Exercise 11 *)

(* Prove baz:

   (1) by using the split tactic as early as possible 

   (2) by using the split tactic as late as possible 
*)

Proposition baz :
  forall P Q R T U1 U2 : Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> U1 /\ U2.
Proof.
  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  (* Here, use the split tactic as early as possible. *)
  
  split.
  - apply H_T_implies_U1.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    apply H_P.
  - apply H_T_implies_U2.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    apply H_P_implies_Q.
    apply H_P. 
    Show Proof.
(*
(fun (P Q R T U1 U2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q)
   (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T)
   (H_T_implies_U1 : T -> U1) (H_T_implies_U2 : T -> U2) =>
 conj (H_T_implies_U1 (H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P))))
   (H_T_implies_U2 (H_R_implies_T (H_Q_implies_R (H_P_implies_Q H_P)))))
 *)
    
  Restart.

  intros P Q R T U1 U2.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2.

  (* Here, use the split tactic as late as possible. *)
  
  assert (H_Q := H_P_implies_Q H_P).
  assert (H_R := H_Q_implies_R H_Q).
  assert (H_T := H_R_implies_T H_R).
  assert (H_U1 := H_T_implies_U1 H_T).
  assert (H_U2 := H_T_implies_U2 H_T).
  split.
  - exact H_U1.
  - exact H_U2. 
    Show Proof.
(*
(fun (P Q R T U1 U2 : Prop) (H_P : P) (H_P_implies_Q : P -> Q) 
   (H_Q_implies_R : Q -> R) (H_R_implies_T : R -> T) (H_T_implies_U1 : T -> U1)
   (H_T_implies_U2 : T -> U2) =>
 let H_Q : Q := H_P_implies_Q H_P in
 let H_R : R := H_Q_implies_R H_Q in
 let H_T : T := H_R_implies_T H_R in
 let H_U1 : U1 := H_T_implies_U1 H_T in
 let H_U2 : U2 := H_T_implies_U2 H_T in conj H_U1 H_U2)
*)
Qed.
(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Two implementations of the addition function *)

(* ***** *)

(* Unit tests *)

Definition test_add (candidate: nat -> nat -> nat) : bool :=
  (candidate 0 0 =n= 0)
  &&
  (candidate 0 1 =n= 1)
  &&
  (candidate 1 0 =n= 1)
  &&
  (candidate 1 1 =n= 2)
  &&
  (candidate 1 2 =n= 3)
  &&
  (candidate 2 1 =n= 3)
  &&
  (candidate 2 2 =n= 4)
  (* etc. *)
  .

(* ***** *)

(* Recursive implementation of the addition function *)

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
  | O =>
    j
  | S i' =>
    S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Lemma fold_unfold_add_v1_O :
  forall j : nat,
    add_v1 O j =
    j.
Proof.
  fold_unfold_tactic add_v1.
Qed.

Lemma fold_unfold_add_v1_S :
  forall i' j : nat,
    add_v1 (S i') j =
    S (add_v1 i' j).
Proof.
  fold_unfold_tactic add_v1.
Qed.

(* ***** *)

(* Tail-recursive implementation of the addition function *)

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Lemma fold_unfold_add_v2_O :
  forall j : nat,
    add_v2 O j =
    j.
Proof.
  fold_unfold_tactic add_v2.
Qed.

Lemma fold_unfold_add_v2_S :
  forall i' j : nat,
    add_v2 (S i') j =
    add_v2 i' (S j).
Proof.
  fold_unfold_tactic add_v2.
Qed.

(* ********** *)

(* Equivalence of add_v1 and add_v2 *)

(* ***** *)

(* The master lemma: *)

Lemma about_add_v2 :
  forall i j : nat,
    add_v2 i (S j) = S (add_v2 i j).
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v2_O (S j)).

  - intro j.
    rewrite -> (fold_unfold_add_v2_S i' (S j)).
    rewrite -> (fold_unfold_add_v2_S i' j).
    Check (IHi' (S j)).
    exact (IHi' (S j)).
Qed.

(* ***** *)

(* The main theorem: *)

Theorem equivalence_of_add_v1_and_add_v2 :
  forall i j : nat,
    add_v1 i j = add_v2 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    rewrite -> (fold_unfold_add_v2_O j).
    exact (fold_unfold_add_v1_O j).

  - intro j.
    rewrite -> (fold_unfold_add_v1_S i' j).
    rewrite -> (fold_unfold_add_v2_S i' j).
    rewrite -> (IHi' j).
    symmetry.
    exact (about_add_v2 i' j).
Qed.

(* ********** *)

(* Neutral (identity) element for addition *)

(* ***** *)

Property O_is_left_neutral_wrt_add_v1 :
  forall y : nat,
    add_v1 0 y = y.
Proof.
Abort.

(* ***** *)

Property O_is_left_neutral_wrt_add_v2 :
  forall y : nat,
    add_v2 0 y = y.
Proof.
Abort.

(* ***** *)

Property O_is_right_neutral_wrt_add_v1 :
  forall x : nat,
    add_v1 x 0 = x.
Proof.
Abort.

Property O_is_right_neutral_wrt_add_v2 :
  forall x : nat,
    add_v2 x 0 = x.
Proof.
Abort.

(* ********** *)

(* Associativity of addition *)

(* ***** *)

Property add_v1_is_associative :
  forall x y z : nat,
    add_v1 x (add_v1 y z) = add_v1 (add_v1 x y) z.
Proof.
Abort.

(* ***** *)

Property add_v2_is_associative :
  forall x y z : nat,
    add_v2 x (add_v2 y z) = add_v2 (add_v2 x y) z.
Proof.
Abort.

(* ********** *)

(* Commutativity of addition *)

(* ***** *)

Property add_v1_is_commutative :
  forall x y : nat,
    add_v1 x y = add_v1 y x.
Proof.
Abort.

(* ***** *)

Property add_v2_is_commutative :
  forall x y : nat,
    add_v2 x y = add_v2 y x.
Proof.
Abort.

(* ********** *)

(* Four implementations of the multiplication function *)

(* ***** *)

(* Unit tests *)

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

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v11 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v1 (mul_v11 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v11_O :
  forall y : nat,
    mul_v11 O y =
    O.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

Lemma fold_unfold_mul_v11_S :
  forall x' y : nat,
    mul_v11 (S x') y =
    add_v1 (mul_v11 x' y) y.
Proof.
  fold_unfold_tactic mul_v11.
Qed.

(* ***** *)

(* Recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v12 (x y : nat) : nat :=
  match x with
  | O =>
    O
  | S x' =>
    add_v2 (mul_v12 x' y) y
  end.

Compute (test_mul mul_v11).

Lemma fold_unfold_mul_v12_O :
  forall y : nat,
    mul_v12 O y =
    O.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

Lemma fold_unfold_mul_v12_S :
  forall x' y : nat,
    mul_v12 (S x') y =
    add_v2 (mul_v12 x' y) y.
Proof.
  fold_unfold_tactic mul_v12.
Qed.

(* Exercise 12 *)

Proposition baz_dual_early :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.

  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    exact (H_P1_implies_Q H_P1).
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    exact (H_P2_implies_Q H_P2).
Qed.

Proposition baz_dual_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros H_P1_or_P2 H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - exact (H_P1_implies_Q H_P1).
  - exact (H_P2_implies_Q H_P2).
Qed.

Proposition baz_dual_early_or_late :
  forall P1 P2 Q R T U : Prop,
    (P1 \/ P2) -> (P1 -> Q) -> (P2 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 Q R T U.
  intros [H_P1 | H_P2] H_P1_implies_Q H_P2_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    exact (H_P1_implies_Q H_P1).
  - apply H_T_implies_U.
    apply H_R_implies_T.
    apply H_Q_implies_R.
    exact (H_P2_implies_Q H_P2).
Qed.
    

(* Exercise 13 *)

(* Use destruct as late as possible to avoid repeating computation *)

Proposition ladidah :
  forall P1 P2 P3 P4 Q R T U : Prop,
    (P1 \/ P2) \/ (P3 \/ P4) -> (P1 -> Q) -> (P2 -> Q) -> (P3 -> Q) -> (P4 -> Q) -> (Q -> R) -> (R -> T) -> (T -> U) -> U.
Proof.
  intros P1 P2 P3 P4 Q R T U.
  intros H_P1_or_P2_or_P3_or_P4 H_P1_implies_Q H_P2_implies_Q H_P3_implies_Q H_P4_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
  apply H_T_implies_U.
  apply H_R_implies_T.
  apply H_Q_implies_R.
  destruct H_P1_or_P2_or_P3_or_P4 as [H_P1_or_P2 | H_P3_or_P4 ].
  destruct H_P1_or_P2 as [H_P1 | H_P2].
  - exact (H_P1_implies_Q H_P1).
  - exact (H_P2_implies_Q H_P2).
  - destruct H_P3_or_P4 as [H_P3 | H_P4].
    exact (H_P3_implies_Q H_P3).
    exact (H_P4_implies_Q H_P4).

    Restart.

    (* early verison *)

    intros P1 P2 P3 P4 Q R T U.
    intros [H_P1_or_P2 | H_P3_or_P4 ] H_P1_implies_Q H_P2_implies_Q H_P3_implies_Q H_P4_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U.
    destruct H_P1_or_P2 as [H_P1 | H_P2].
  -   apply H_T_implies_U.
      apply H_R_implies_T.
      apply H_Q_implies_R.
      exact (H_P1_implies_Q H_P1).
  -     apply H_T_implies_U.
        apply H_R_implies_T.
        apply H_Q_implies_R.
        exact (H_P2_implies_Q H_P2).
  -  destruct H_P3_or_P4 as [H_P3 | H_P4].
     apply H_T_implies_U.
     apply H_R_implies_T.
     apply H_Q_implies_R.
     exact (H_P3_implies_Q H_P3).
     apply H_T_implies_U.
     apply H_R_implies_T.
     apply H_Q_implies_R.
      exact (H_P4_implies_Q H_P4).
Qed.

(* Proving backwards *)

Proposition toodeloo :
  forall P Q R T U1 U2 U3 U4: Prop,
    P -> (P -> Q) -> (Q -> R) -> (R -> T) -> (T -> U1) -> (T -> U2) -> (T -> U3) -> (T -> U4) -> (U1 /\ U2) /\ (U3 /\ U4).
Proof.
  intros P Q R T U1 U2 U3 U4.
  intros H_P H_P_implies_Q H_Q_implies_R H_R_implies_T H_T_implies_U1 H_T_implies_U2 H_T_implies_U3 H_T_implies_U4.
  apply H_P_implies_Q in H_P.
  apply H_Q_implies_R in H_P.
  apply H_R_implies_T in H_P.
  Check (conj (conj (H_T_implies_U1 H_P) (H_T_implies_U2 H_P)) (conj (H_T_implies_U3 H_P) (H_T_implies_U4 H_P))).
  exact (conj (conj (H_T_implies_U1 H_P) (H_T_implies_U2 H_P)) (conj (H_T_implies_U3 H_P) (H_T_implies_U4 H_P))).
Qed.       
                               
(* Exercise 27 *)

(* Tail-recursive implementation of the multiplication function, using add_v1 *)

Fixpoint mul_v21_aux (x y a : nat) :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v21_aux x' y (add_v1 a y)
  end.

Definition mul_v21 (x y : nat) : nat :=
  mul_v21_aux x y 0. 

Compute (test_mul mul_v21).

Lemma fold_unfold_mul_v21_aux_O :
  forall y a : nat,
    mul_v21_aux O y a =
    a.
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

Lemma fold_unfold_mul_v21_aux_S :
  forall x' y a : nat,
    mul_v21_aux (S x') y a =
    mul_v21_aux x' y (add_v1 a y).
Proof.
  fold_unfold_tactic mul_v21_aux.
Qed.

(* Exercise 28 *)

(* Tail-recursive implementation of the multiplication function, using add_v2 *)

Fixpoint mul_v22_aux (x y a : nat) :=
  match x with
  | O =>
    a
  | S x' =>
    mul_v22_aux x' y (add_v2 a y)
  end.

Definition mul_v22 (x y : nat) : nat :=
  mul_v22_aux x y 0. 

Compute (test_mul mul_v22).

Lemma fold_unfold_mul_v22_aux_O :
  forall y a : nat,
    mul_v22_aux O y a =
    a.
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

Lemma fold_unfold_mul_v22_aux_S :
  forall x' y a : nat,
    mul_v22_aux (S x') y a =
    mul_v22_aux x' y (add_v2 a y).
Proof.
  fold_unfold_tactic mul_v22_aux.
Qed.

(* Exercise 29 *)

(* Equivalence of mul_v11, mul_v12, mul_v21, and mul_v22 *)

(* ***** *)

Theorem equivalence_of_mul_v11_and_mul_v12 :
  forall i j : nat,
    mul_v11 i j = mul_v12 i j.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    Check (fold_unfold_mul_v11_O j).
    rewrite -> (fold_unfold_mul_v11_O j).
    Check (fold_unfold_mul_v12_O j).    
    rewrite -> (fold_unfold_mul_v12_O j).
    reflexivity.

  - intro j.
    Check (fold_unfold_mul_v11_S i' j).
    rewrite -> (fold_unfold_mul_v11_S i' j).
    Check (fold_unfold_mul_v12_S i' j).
    rewrite -> (fold_unfold_mul_v12_S i' j).
    Check (IHi' j).
    rewrite -> (IHi' j).
    Check (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
    exact (equivalence_of_add_v1_and_add_v2 (mul_v12 i' j) j).
Qed.

(* ***** *)

(* ***** *)

Lemma equivalence_of_mul_v21_aux_and_mul_v22_aux :
  forall i j a : nat,
    mul_v21_aux i j a = mul_v22_aux i j a.
Proof.
  intro i.
  induction i as [ | i' IHi'].

  - intros j a.
    Check (fold_unfold_mul_v21_aux_O j a).
    rewrite -> (fold_unfold_mul_v21_aux_O j a).
    Check (fold_unfold_mul_v22_aux_O j a).    
    rewrite -> (fold_unfold_mul_v22_aux_O j a).
    reflexivity.

  - intros j a.
    Check (fold_unfold_mul_v21_aux_S i' j a).
    rewrite -> (fold_unfold_mul_v21_aux_S i' j a).
    Check (fold_unfold_mul_v22_aux_S i' j a).
    rewrite -> (fold_unfold_mul_v22_aux_S i' j a).
    (*  mul_v21_aux i' j (add_v1 0 j) = mul_v22_aux i' j (add_v2 0 j) *)
    Check (equivalence_of_add_v1_and_add_v2 a j).
    rewrite -> (equivalence_of_add_v1_and_add_v2 a j).
    Check (IHi' j (add_v2 a j)).
    exact (IHi' j (add_v2 a j)).
Qed.


Theorem equivalence_of_mul_v21_and_mul_v22 :
  forall i j : nat,
    mul_v21 i j = mul_v22 i j.
Proof.
  unfold mul_v21, mul_v22.
  intro i.
  induction i as [ | i' IHi'].

  - intro j.
    Check (fold_unfold_mul_v21_aux_O j 0).
    rewrite -> (fold_unfold_mul_v21_aux_O j 0).
    Check (fold_unfold_mul_v22_aux_O j 0).    
    rewrite -> (fold_unfold_mul_v22_aux_O j 0).
    reflexivity.

  - intro j.
    Check (equivalence_of_mul_v21_aux_and_mul_v22_aux (S i') j 0).
    exact (equivalence_of_mul_v21_aux_and_mul_v22_aux (S i') j 0).
Qed.

(* ********** *)

(* 0 is left absorbing with respect to multiplication *)

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v11 :
  forall y : nat,
    mul_v11 0 y = 0.
Proof.
Abort.

(* ***** *)

Property O_is_left_absorbing_wrt_mul_v12 :
  forall y : nat,
    mul_v12 0 y = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v21 :
  forall y : nat,
    mul_v21 0 y = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_left_absorbing_wrt_mul_v22 :
  forall y : nat,
    mul_v22 0 y = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is left neutral with respect to multiplication *)

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v11 :
  forall y : nat,
    mul_v11 1 y = y.
Proof.
Abort.

(* ***** *)

Property SO_is_left_neutral_wrt_mul_v12 :
  forall y : nat,
    mul_v12 1 y = y.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v21 :
  forall y : nat,
    mul_v21 1 y = y.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_left_neutral_wrt_mul_v22 :
  forall y : nat,
    mul_v22 1 y = y.
Proof.
Abort.
*)

(* ********** *)

(* 0 is right absorbing with respect to multiplication *)

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 0 = 0.
Proof.
Abort.

(* ***** *)

Property O_is_right_absorbing_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 0 = 0.
Proof.
Abort.

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 0 = 0.
Proof.
Abort.
*)

(* ***** *)

(*
Property O_is_right_absorbing_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 0 = 0.
Proof.
Abort.
*)

(* ********** *)

(* 1 is right neutral with respect to multiplication *)

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v11 :
  forall x : nat,
    mul_v11 x 1 = x.
Proof.
Abort.

(* ***** *)

Property SO_is_right_neutral_wrt_mul_v12 :
  forall x : nat,
    mul_v12 x 1 = x.
Proof.
Abort.

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v21 :
  forall x : nat,
    mul_v21 x 1 = x.
Proof.
Abort.
*)

(* ***** *)

(*
Property SO_is_right_neutral_wrt_mul_v22 :
  forall x : nat,
    mul_v22 x 1 = x.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is right-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* Multiplication is associative *)

(* ***** *)

Property mul_v11_is_associative :
  forall x y z : nat,
    mul_v11 x (mul_v11 y z) = mul_v11 (mul_v11 x y) z.
Proof.
Abort.

(* ***** *)

Property mul_v12_is_associative :
  forall x y z : nat,
    mul_v12 x (mul_v12 y z) = mul_v12 (mul_v12 x y) z.
Proof.
Abort.

(* ***** *)

(*
Property mul_v21_is_associative :
  forall x y z : nat,
    mul_v21 x (mul_v21 y z) = mul_v21 (mul_v21 x y) z.
Proof.
Abort.
*)

(* ***** *)

(*
Property mul_v22_is_associative :
  forall x y z : nat,
    mul_v22 x (mul_v22 y z) = mul_v22 (mul_v22 x y) z.
Proof.
Abort.
*)

(* ********** *)

(* Multiplication is left-distributive over addition *)

(* ***** *)

(* ... *)

(* ********** *)

(* end of week-04_equational-reasoning-about-arithmetical-functions.v *)
