(* 6_mystery-functions.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 12 Sep 2020 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

Compute (fst (2,3)).

Notation "A =p= B" :=
  (beq_nat (fst A) (fst B) && beq_nat (snd A) (snd B)) (at level 70, right associativity).

(* ********** *)

Definition specification_of_mystery_function_00 (mf : nat -> nat) :=
  mf 0 = 1 /\ forall i j : nat, mf (S (i + j)) = mf i + mf j.

(* ***** *)

Proposition there_is_at_most_one_mystery_function_00 :
  forall f g : nat -> nat,
    specification_of_mystery_function_00 f ->
    specification_of_mystery_function_00 g ->
    forall n : nat,
      f n = g n.
Proof.
Abort.

(* ***** *)

Definition unit_test_for_mystery_function_00a (mf : nat -> nat) :=
  (mf 0 =n= 1) (* etc. *).

Definition unit_test_for_mystery_function_00b (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) (* etc. *).

Definition unit_test_for_mystery_function_00c (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) (* etc. *).

Definition unit_test_for_mystery_function_00d (mf : nat -> nat) :=
  (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) && (mf 3 =n= 4)
  (* etc. *).

(* ***** *)

Definition mystery_function_00 := S.

Definition less_succinct_mystery_function_00 (n : nat) : nat :=
  S n.

Compute (unit_test_for_mystery_function_00d mystery_function_00).

Theorem there_is_at_least_one_mystery_function_00 :
  specification_of_mystery_function_00 mystery_function_00.
Proof.
  unfold specification_of_mystery_function_00, mystery_function_00.
  split.
  - reflexivity.
  - intros i j.
    rewrite -> (plus_Sn_m i (S j)).
    rewrite <- (plus_n_Sm i j).
    reflexivity.
Qed.

(* ***** *)

Definition mystery_function_00_alt := fun (n : nat) => n + 1.

Theorem there_is_at_least_one_mystery_function_00_alt :
  specification_of_mystery_function_00 mystery_function_00_alt.
Proof.
Abort.

(* ***** *)

Theorem soundness_of_the_unit_test_function_for_mystery_function_00 :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00c mf = true.
Proof.
  unfold specification_of_mystery_function_00.
  unfold unit_test_for_mystery_function_00c.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) && (mf 2 =n= 3) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  Check (Nat.eqb_refl 2).
  rewrite -> (Nat.eqb_refl 2).
  rewrite -> (andb_true_l (mf 2 =n= 3)).
  Check (Nat.add_1_l 1).
  rewrite <- (Nat.add_1_l 1) at 1.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  rewrite -> (H_S 0 1).
  rewrite -> H_O.
  rewrite <- (Nat.add_1_l 0) at 2.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  rewrite -> (Nat.add_1_l 1).
  rewrite -> (Nat.add_1_l 2).
  exact (Nat.eqb_refl 3).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00b :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].
  (* Goal: (mf 0 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> H_O.
  (* Goal: (1 =n= 1) && (mf 1 =n= 2) = true *)
  rewrite -> (Nat.eqb_refl 1).
  (* Goal: true && (mf 1 =n= 2) = true *)
  rewrite -> (andb_true_l (mf 1 =n= 2)).
  (* Goal: (mf 1 =n= 2) = true *)
  (* etc. *)
  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

Theorem soundness_of_the_unit_test_function_for_mystery_function_00_with_Search :
  forall mf : nat -> nat,
    specification_of_mystery_function_00 mf ->
    unit_test_for_mystery_function_00b mf = true.
Proof.
  unfold specification_of_mystery_function_00,
         unit_test_for_mystery_function_00b.
  intros mf [H_O H_S].

  rewrite -> H_O.
  Search (beq_nat _  _ = true).
  Check (Nat.eqb_refl 1).
  rewrite -> (Nat.eqb_refl 1).
  Search (true && _ = _).
  Check (andb_true_l (mf 1 =n= 2)).
  rewrite -> (andb_true_l (mf 1 =n= 2)).

  Check (Nat.add_1_l 0).
  rewrite <- (Nat.add_1_l 0) at 1.
  Check (plus_Sn_m 0 0).
  rewrite -> (plus_Sn_m 0 0).
  rewrite -> (H_S 0 0).
  rewrite -> H_O.
  Check (plus_Sn_m 0 1).
  rewrite -> (plus_Sn_m 0 1).
  Check (Nat.add_1_r 0).
  rewrite -> (Nat.add_1_r 0).
  Check (Nat.eqb_refl 2).
  exact (Nat.eqb_refl 2).
Qed.

(* ********** *)

Definition specification_of_mystery_function_11 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i j : nat,
    mf (i + j) = mf i + 2 * i * j + mf j.

Definition unit_test_for_mystery_function_11 (mf : nat -> nat) :=
  (mf 1 =n= 1) && (mf 2 =n= 4) && (mf 3 =n= 9) && (mf 4 =n= 16)
(* etc. *).

Search (Nat.square).

Check Nat.square.

Definition mystery_function_11 := Nat.square.

Compute (unit_test_for_mystery_function_11 mystery_function_11).

Lemma quadratic_formula :
  forall i j : nat,
    (i + j) * (i + j) = i * i + 2 * i * j + j * j.
Proof.
    intros i j.
    Search ((_ + _) * _).
    Check (Nat.mul_add_distr_r i j (i + j)).
    rewrite -> (Nat.mul_add_distr_r i j (i + j)).
    Check (Nat.mul_add_distr_l i i j).
    rewrite -> (Nat.mul_add_distr_l i i j).
    Check (Nat.mul_add_distr_l j i j).
    rewrite -> (Nat.mul_add_distr_l j i j).
    Search (_ * _ = _ * _).
    Check (Nat.mul_comm i j).
    rewrite <- (Nat.mul_comm i j).
    Search (S _ * _).
    Check (Nat.mul_succ_l 1 (i * j)).
    Check (Nat.mul_assoc 2 i j).
    rewrite <- (Nat.mul_assoc 2 i j).
    rewrite -> (Nat.mul_succ_l 1 (i * j)).
    rewrite -> (Nat.mul_1_l (i * j)).
    Check (Nat.add_assoc (i * i) (i * j) (i * j + j * j)).
    rewrite <- (Nat.add_assoc (i * i) (i * j) (i * j + j * j)).
    Check (Nat.add_assoc (i * i) (i * j + i * j) (j * j)).
    rewrite <- (Nat.add_assoc (i * i) (i * j + i * j) (j * j)).
    Check (Nat.add_assoc (i * j) (i * j) (j * j)).
    rewrite -> (Nat.add_assoc (i * j) (i * j) (j * j)).
    reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_11:
  specification_of_mystery_function_11 mystery_function_11.
Proof.
  unfold specification_of_mystery_function_11, mystery_function_11.
  split.

  - Search (Nat.square _ = _).
    Check (Nat.square_spec 1).
    rewrite -> (Nat.square_spec 1).
    Search (1 * _ = _).
    Check (Nat.mul_1_l 1).
    exact (Nat.mul_1_l 1).

  - Check (quadratic_formula).
    exact (quadratic_formula).
Qed.

(* ********** *)

Definition specification_of_mystery_function_04 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  forall n' : nat,
    mf (S n') = mf n' + S (2 * n').

Definition unit_test_for_mystery_function_04 (mf : nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 4) && (mf 3 =n= 9).

Definition mystery_function_04 := Nat.square.

Compute (unit_test_for_mystery_function_04 mystery_function_04).

Theorem there_is_at_least_one_mystery_function_04:
  specification_of_mystery_function_04 mystery_function_04.
Proof.
  unfold specification_of_mystery_function_04, mystery_function_04.
  split.

  - Check (Nat.square_spec 0).
    rewrite -> (Nat.square_spec 0).
    Search (0 * _ = 0).
    Check (Nat.mul_0_l 0).
    exact (Nat.mul_0_l 0).
  - intro n'.
    rewrite -> (Nat.square_spec (S n')).
    rewrite -> (Nat.square_spec n').
    Search (_ + 1 = _).
    rewrite <- (Nat.add_1_r n').
    rewrite <- (Nat.add_1_r (2 * n')).
    Check (quadratic_formula n' 1).
    rewrite -> (quadratic_formula n' 1).
    Search (1 * _ = _).
    rewrite -> (Nat.mul_1_l 1).
    rewrite -> (Nat.mul_1_r (2 * n')).
    Check (Nat.add_assoc (n' * n') (2 * n') 1).
    rewrite -> (Nat.add_assoc (n' * n') (2 * n') 1).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_15 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (S x, y * S x).

Search (_ = (_,_)).

Definition unit_test_for_mystery_function_15 (mf : nat -> nat * nat) :=
  (mf 0 =p= (0,1)) &&
  (mf 1 =p= (1,1)) &&
  (mf 2 =p= (2,2)) &&
  (mf 3 =p= (3,6)) &&
  (mf 4 =p= (4,24)) &&
  (mf 5 =p= (5,120)).

Fixpoint fac (n : nat) : (nat * nat) :=
  match n with
  | O => (0,1)
  | S n' => let (x,y) := fac n'
            in (S x, y * S x)
  end.

Definition mystery_function_15 := fac.

Compute (unit_test_for_mystery_function_15 mystery_function_15).

Lemma fold_unfold_fac_O :
  fac O = (0,1).
Proof.
  fold_unfold_tactic fac.
Qed.

Lemma fold_unfold_fac_S :
  forall n' : nat,
    fac (S n') =
    let (x,y) := fac n'
    in (S x, y * S x).
Proof.
  fold_unfold_tactic fac.
Qed.

Theorem there_is_at_least_one_mystery_function_15:
  specification_of_mystery_function_15 mystery_function_15.
Proof.
  unfold specification_of_mystery_function_15, mystery_function_15.
  split.

  - exact fold_unfold_fac_O.

  - Check (fold_unfold_fac_S).
    exact fold_unfold_fac_S.
Qed.

(* ********** *)

Definition specification_of_mystery_function_16 (mf : nat -> nat * nat) :=
  mf 0 = (0, 1)
  /\
  forall n' : nat,
    mf (S n') = let (x, y) := mf n'
                in (y, x + y).

Definition unit_test_for_mystery_function_16 (mf : nat -> nat * nat) :=
  (mf 0 =p= (0,1)) &&
  (mf 1 =p= (1,1)) &&
  (mf 2 =p= (1,2)) &&
  (mf 3 =p= (2,3)) &&
  (mf 4 =p= (3,5)) &&
  (mf 5 =p= (5,8)).

Fixpoint fibp (n : nat) : (nat * nat) :=
  match n with
  | O => (0,1)
  | S n' => let (x,y) := fibp n'
            in (y, x + y)
  end.

Definition mystery_function_16 := fibp.

Compute (unit_test_for_mystery_function_16 mystery_function_16).

Lemma fold_unfold_fibp_O :
  fibp O = (0,1).
Proof.
  fold_unfold_tactic fibp.
Qed.

Lemma fold_unfold_fibp_S :
  forall n' : nat,
    fibp (S n') =
    let (x,y) := fibp n'
    in (y, x + y).
Proof.
  fold_unfold_tactic fibp.
Qed.

Theorem there_is_at_least_one_mystery_function_16:
  specification_of_mystery_function_16 mystery_function_16.
Proof.
  unfold specification_of_mystery_function_16, mystery_function_16.
  split.

  - exact fold_unfold_fibp_O.

  - Check (fold_unfold_fibp_S).
    exact fold_unfold_fibp_S.
Qed.

(* ********** *)

Definition specification_of_mystery_function_17 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall p q : nat,
    mf (S (p + q)) = mf (S p) * mf (S q) + mf p * mf q.

Definition unit_test_for_mystery_function_17 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 1) && (mf 3 =n= 2).

Fixpoint fib (n : nat) : nat :=
  match n with
  | O => O
  | S n' => match n' with
            | O => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition mystery_function_17 := fib.

Compute (unit_test_for_mystery_function_17 mystery_function_17).

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

Corollary fold_unfold_fib_SS :
  forall n'' : nat,
    fib (S (S n'')) =
    fib (S n'') + fib n''.
Proof.
  intro n''.
  rewrite -> (fold_unfold_fib_S (S n'')).
  reflexivity.
Qed.

Theorem there_is_at_least_one_mystery_function_17 :
  specification_of_mystery_function_17 mystery_function_17.
Proof.
  unfold specification_of_mystery_function_17, mystery_function_17.
  split.
  - rewrite -> fold_unfold_fib_O.
    reflexivity.
  - split.
    -- rewrite -> fold_unfold_fib_1.
       reflexivity.
    -- split.
       --- rewrite -> (fold_unfold_fib_S 1).
           rewrite -> fold_unfold_fib_O.
           rewrite -> fold_unfold_fib_1.
           Search (_ + 0 = _).
           rewrite -> (Nat.add_0_r 1).
           reflexivity.
       --- intro p.
           induction p as [| p' IHp'].
    + intro q.
      rewrite -> (Nat.add_0_l q).
      rewrite -> fold_unfold_fib_O.
      rewrite -> fold_unfold_fib_1.
      rewrite -> (Nat.mul_0_l (fib q)).
      rewrite -> (Nat.mul_1_l (fib (S q))).
      rewrite -> (Nat.add_0_r (fib (S q))).
      reflexivity.
    + intro q.
      rewrite -> (plus_Sn_m p' q).
      rewrite -> (plus_n_Sm p' q).
      rewrite -> (IHp' (S q)).
      rewrite -> (fold_unfold_fib_SS q).
      rewrite -> (fold_unfold_fib_SS p').
      Search (_ * (_ + _)).
      rewrite -> (Nat.mul_add_distr_l (fib (S p')) (fib (S q)) (fib q)).
      Check Nat.mul_add_distr_r.
      rewrite -> (Nat.mul_add_distr_r (fib (S p')) (fib p') (fib (S q))).
      Check Nat.add_assoc.
      rewrite <- (Nat.add_assoc
                    (fib (S p') * fib (S q))
                    (fib (S p') * fib q)
                    (fib p' * fib (S q))).
      rewrite -> (Nat.add_comm  (fib (S p') * fib q)
                                (fib p' * fib (S q))).
      Check  (Nat.add_assoc
                    (fib (S p') * fib (S q))
                    (fib p' * fib (S q))
                    (fib (S p') * fib q)).
      exact  (Nat.add_assoc
                    (fib (S p') * fib (S q))
                    (fib p' * fib (S q))
                    (fib (S p') * fib q)).
Qed.

(* ********** *)

Definition specification_of_mystery_function_18 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  mf 2 = 1
  /\
  forall n''' : nat,
    mf n''' + mf (S (S (S n'''))) = 2 * mf (S (S n''')).

Definition unit_test_for_mystery_function_18 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 2 =n= 1) && (mf 3 =n= 2) && (mf 4 =n= 3).

Definition mystery_function_18 := fib.

Compute (unit_test_for_mystery_function_18 mystery_function_18).

Theorem there_is_at_least_one_mystery_function_18 :
  specification_of_mystery_function_18 mystery_function_18.
Proof.
  unfold specification_of_mystery_function_18, mystery_function_18.
  split.
  - rewrite -> fold_unfold_fib_O.
    reflexivity.
  - split.
    -- rewrite -> fold_unfold_fib_1.
       reflexivity.
    -- split.
       --- rewrite -> (fold_unfold_fib_S 1).
           rewrite -> fold_unfold_fib_O.
           rewrite -> fold_unfold_fib_1.
           Search (_ + 0 = _).
           rewrite -> (Nat.add_0_r 1).
           reflexivity.
       --- intro p.
           induction p as [| p' IHp'].
           rewrite -> fold_unfold_fib_O.
           rewrite -> (Nat.add_0_l (fib 3)).
           rewrite -> (fold_unfold_fib_SS 1).
           rewrite -> (fold_unfold_fib_SS 0).
           rewrite -> (fold_unfold_fib_O).
           rewrite -> (fold_unfold_fib_1).
           rewrite -> (Nat.add_0_r 1).
           rewrite -> (Nat.add_1_r 1).
           Search (_ * 1).
           rewrite -> (Nat.mul_1_r 2).
           reflexivity.
           rewrite -> (fold_unfold_fib_S (S (S (S p'))) ).
           rewrite -> (fold_unfold_fib_S (S p')).
           Search (_ + (_ + _)).
           rewrite -> (Nat.add_shuffle3 (fib (S (S (S p')))) (fib (S p')) (fib p') ).
           rewrite -> (Nat.add_comm (fib (S (S (S p')))) (fib p')  ).
           rewrite -> IHp'.
           rewrite -> (fold_unfold_fib_S (S (S p'))).
           Search (_ + (_ + _)).
           rewrite -> (Nat.add_assoc (fib (S p')) (fib (S p')) (2 * fib (S (S p'))) ).
           Search (_ + _ = _ + _).
           rewrite -> (Nat.add_comm (fib (S (S p'))) (fib (S p'))).
           Search (_ * ( _ + _ )).
           rewrite -> (Nat.mul_add_distr_l 2 (fib (S p')) (fib (S (S p'))) ).
           Check (Nat.mul_succ_l 1 (fib (S p'))).
           rewrite -> (Nat.mul_succ_l 1 (fib (S p'))).
           Search (1 * _ = _).
           Check (Nat.mul_1_l (fib (S p'))).
           rewrite -> (Nat.mul_1_l (fib (S p'))).
           reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_03 (mf : nat -> nat -> nat) :=
  mf 0 0 = 0
  /\
  (forall i j: nat, mf (S i) j = S (mf i j))
  /\
  (forall i j: nat, S (mf i j) = mf i (S j)).

Definition unit_test_for_mystery_function_03 (mf: nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 1 0 =n= 1) && (mf 0 1 =n= 1) && (mf 1 1 =n= 2) && (mf 2 0 =n= 2).

Definition mystery_function_03 := Nat.add.

Compute (unit_test_for_mystery_function_03 mystery_function_03).

Theorem there_is_at_least_one_mystery_function_03 :
  specification_of_mystery_function_03 mystery_function_03.
Proof.
  unfold specification_of_mystery_function_03, mystery_function_03.
  split.
  - Search (_ + 0 = _).
    rewrite (Nat.add_0_r 0).
    reflexivity.
  - split.
    -- intros i j.
       rewrite -> (plus_Snm_nSm i j).
       Search (S _ = _).
       rewrite <- (plus_n_Sm i j).
       reflexivity.
    -- Search (S _ = _).
       intros i j.
       exact (plus_n_Sm i j).
Qed.

(* ********** *)

Definition specification_of_mystery_function_42 (mf : nat -> nat) :=
  mf 1 = 42
  /\
  forall i j : nat,
    mf (i + j) = mf i + mf j.

Definition unit_test_for_mystery_function_42 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 42) && (mf 2 =n= 84) && (mf 3 =n= 126).

Definition mystery_function_42 (n: nat) : nat := Nat.mul 42 n.

Compute (unit_test_for_mystery_function_42 mystery_function_42).

Theorem there_is_at_least_one_mystery_function_42 :
  specification_of_mystery_function_42 mystery_function_42.
Proof.
  unfold specification_of_mystery_function_42, mystery_function_42.
  split.
  - Search (_ * 1 = _).
    rewrite (Nat.mul_1_r 42).
    reflexivity.
  - intros i j.
    Search (_ * (_ + _) = _ * _ + _ * _).
    rewrite -> (Nat.mul_add_distr_l 42 i j).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_07 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf 0 j = j)
  /\
  (forall i : nat, mf i 0 = i)
  /\
  (forall i j k : nat, mf (i + k) (j + k) = (mf i j) + k).

Definition unit_test_for_mystery_function_07 (mf: nat -> nat -> nat) :=
  (mf 0 0 =n= 0) && (mf 0 1 =n= 1) && (mf 2 0 =n= 2) && (mf 5 3 =n= 5).

Definition mystery_function_07 := Nat.max.

Compute (unit_test_for_mystery_function_07 mystery_function_07).

Theorem there_is_at_least_one_mystery_function_07 :
  specification_of_mystery_function_07 mystery_function_07.
Proof.
  unfold specification_of_mystery_function_07, mystery_function_07.
  split.
  - intro j.
    exact (Nat.max_0_l j).
  - split.
    -- intro i.
       exact (Nat.max_0_r i).
    -- intros i j k.
       Search Nat.max.
       exact (Nat.add_max_distr_r i j k).
Qed.

(* ********** *)

Definition specification_of_mystery_function_08 (mf : nat -> nat -> bool) :=
  (forall j : nat, mf 0 j = true)
  /\
  (forall i : nat, mf (S i) 0 = false)
  /\
  (forall i j : nat, mf (S i) (S j) = mf i j).

Definition unit_test_for_mystery_function_08 (mf: nat -> nat -> bool) :=
  (mf 0 0 =b= true) && (mf 0 1 =b= true) && (mf 2 0 =b= false) && (mf 5 3 =b= false).

Definition mystery_function_08 := Nat.leb.

Compute (unit_test_for_mystery_function_08 mystery_function_08).

Lemma fold_unfold_leb_S :
  forall i j: nat,
    Nat.leb (S i) (S j) = (Nat.leb i j).
Proof.
  fold_unfold_tactic Nat.leb.
Qed.

Theorem there_is_at_least_one_mystery_function_08 :
  specification_of_mystery_function_08 mystery_function_08.
Proof.
  unfold specification_of_mystery_function_08, mystery_function_08.
  split.
  - intro j.
    Search Nat.leb.
    rewrite -> (leb_correct 0 j).
    reflexivity.
    exact (Nat.le_0_l j).
  - split.
    -- intro i.
       Search Nat.leb.
       rewrite -> (leb_correct_conv).
       reflexivity.
       Search (0 < _).
       exact (Nat.lt_0_succ i).
    -- intros i j.
       rewrite -> (fold_unfold_leb_S i j).
       reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_23 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 0
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

Definition unit_test_for_mystery_function_23 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 0) && (mf 2 =n= 1) && (mf 10 =n= 5).

Definition mystery_function_23 (n: nat) : nat := n / 2.

Compute (unit_test_for_mystery_function_23 mystery_function_23).

Theorem there_is_at_least_one_mystery_function_23 :
  specification_of_mystery_function_23 mystery_function_23.
Proof.
  unfold specification_of_mystery_function_23, mystery_function_23.
  split.
  - Search Nat.div.
    rewrite -> (Nat.div_small 0 2).
    reflexivity.
    Search (0 < _).
    exact Nat.lt_0_2.
  - split.
    -- rewrite -> (Nat.div_small 1 2).
       reflexivity.
       Search (1 < _).
       exact Nat.lt_1_2.
    -- intro n.
       rewrite <- (Nat.add_1_r (n / 2)).
       rewrite <- (Nat.add_1_r n).
       rewrite <- (Nat.add_1_r (n + 1)).
       Search (_ + _ + _ = _ + (_ + _)).
       rewrite -> (plus_assoc_reverse n 1 1).
       Search (_ * 1 = _).
       rewrite <- (Nat.mul_1_r (1 + 1)).
       Search (1 + 1).
       rewrite <- BinInt.ZL0.
       rewrite (Nat.mul_comm 2 1).
       Search ((_ + _)/_).
       rewrite -> (Nat.div_add n 1 2).
       reflexivity.
       exact (Nat.neq_succ_0 1).
Qed.

(* ********** *)

Definition specification_of_mystery_function_24 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  mf 1 = 1
  /\
  forall n'' : nat,
    mf (S (S n'')) = S (mf n'').

Definition unit_test_for_mystery_function_24 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 1) && (mf 3 =n= 2) && (mf 10 =n= 5).

Definition mystery_function_24 (n: nat) : nat := (n + 1) / 2.

Compute (unit_test_for_mystery_function_24 mystery_function_24).

Theorem there_is_at_least_one_mystery_function_24 :
  specification_of_mystery_function_24 mystery_function_24.
Proof.
  unfold specification_of_mystery_function_24, mystery_function_24.
  split.
  - Search (0 + _ = _).
    rewrite -> (Nat.add_0_l 1).
    rewrite -> (Nat.div_small 1 2).
    reflexivity.
    exact Nat.lt_1_2.
  - split.
    + rewrite <- BinInt.ZL0.
      Search (_ / _ = _).
      rewrite -> (Nat.div_same 2).
      reflexivity.
      exact (Nat.neq_succ_0 1).
    + intro n.
      rewrite <- (Nat.add_1_r ((n + 1) / 2)).
      rewrite <- (Nat.add_1_r ((S n))).
      rewrite -> (plus_assoc_reverse (S n) 1 1).
      rewrite <- (Nat.mul_1_r (1 + 1)).
      rewrite <- BinInt.ZL0.
      rewrite (Nat.mul_comm 2 1).
      rewrite -> (Nat.div_add (S n) 1 2).
      rewrite <- (Nat.add_1_r n).
      reflexivity.
      exact (Nat.neq_succ_0 1).
Qed.

(* ********** *)

Definition specification_of_mystery_function_13 (mf : nat -> nat) :=
  (forall q : nat, mf (2 * q) = q)
  /\
  (forall q : nat, mf (S (2 * q)) = q).

Definition unit_test_for_mystery_function_13 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 2 =n= 1) && (mf 3 =n= 1) && (mf 10 =n= 5).

Definition mystery_function_13 (n: nat) : nat := n / 2.

Compute (unit_test_for_mystery_function_13 mystery_function_13).

Theorem there_is_at_least_one_mystery_function_13 :
  specification_of_mystery_function_13 mystery_function_13.
Proof.
  unfold specification_of_mystery_function_13, mystery_function_13.
  split.
  - intro q.
    Search (_ * _  = _ * _ ).
    rewrite -> (Nat.mul_comm 2 q).
    Search (_ * _ / _).
    rewrite -> (Nat.div_mul q 2).
    reflexivity.
    Search (_ <> 0).
    exact (Nat.neq_succ_0 1).
  - intro q.
    rewrite <- (Nat.div2_div (S (2 * q))).
    Search (2 * _).
    exact (Nat.div2_succ_double q).
Qed.

(* ********** *)

Definition specification_of_mystery_function_25 (mf : nat -> nat) :=
  mf 0 = 0
  /\
  (forall q : nat,
      mf (2 * (S q)) = S (mf (S q)))
  /\
  mf 1 = 0
  /\
  (forall q : nat,
      mf (S (2 * (S q))) = S (mf (S q))).

Definition unit_test_for_mystery_function_25 (mf: nat -> nat) :=
  (mf 0 =n= 0) && (mf 1 =n= 0) && (mf 2 =n= 1) && (mf 10 =n= 3).

Definition mystery_function_25 := Nat.log2.

Compute (unit_test_for_mystery_function_25 mystery_function_25).

Theorem there_is_at_least_one_mystery_function_25 :
  specification_of_mystery_function_25 mystery_function_25.
Proof.
  unfold specification_of_mystery_function_25, mystery_function_25.
  split.
  - Search Nat.log2.
    rewrite -> (Nat.log2_nonpos 0).
    reflexivity.
    Search (_ <= 0).
    rewrite -> (Nat.le_0_r 0).
    reflexivity.
  - split.
    + intro q.
      Search (Nat.log2 (2 * _) = _).
      rewrite -> (Nat.log2_double (S q)).
      reflexivity.
      Search (0 < S _).
      exact (Nat.lt_0_succ q).
    + split.
      -- Search Nat.log2.
         exact (Nat.log2_1).
      -- intro q.
         Search (S (Nat.log2 _)).
         Search (S _).
         rewrite <- (Nat.add_1_r (2 * S q)).
         rewrite -> (Nat.log2_succ_double (S q)).
         reflexivity.
         exact (Nat.lt_0_succ q).
Qed.

(* ****** *)

Definition specification_of_mystery_function_20 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = S (mf i j)).

Definition unit_test_for_mystery_function_20 (mf : nat -> nat -> nat) :=
  (mf O 1 =n= 1) && (mf 1 O =n= 1) && (mf 1 1 =n= 2) && (mf 2 1 =n= 3).

Definition mystery_function_20 (n : nat) (m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_20 mystery_function_20).

Theorem there_is_at_least_one_mystery_function_20 :
  specification_of_mystery_function_20 mystery_function_20.
Proof.
  unfold specification_of_mystery_function_20, mystery_function_20.
  split.
  - Search (0 + _).
    intro j.
    rewrite -> (Nat.add_0_l j).
    reflexivity.
  - intros i j.
    Search (S _ + _).
    rewrite (plus_Sn_m i j).
    reflexivity.
Qed.

Theorem there_is_at_most_one_mystery_function_20 :
  forall (mf20a mf20b : nat -> nat -> nat),
    specification_of_mystery_function_20 mf20a ->
    specification_of_mystery_function_20 mf20b ->
    forall (i j : nat),
      mf20a i j = mf20b i j.
Proof.
  intros mf20a mf20b.
  unfold specification_of_mystery_function_20.
  intro S1.
  destruct S1 as [SaO SaS].
  intro S2.
  destruct S2 as [SbO SbS].
  intros i j.
  induction i as [i | IHi ].
  - rewrite -> (SaO j).
    rewrite -> (SbO j).
    reflexivity.
  - rewrite -> (SaS IHi j).
    rewrite -> (SbS IHi j).
    Search (S _ = S _).
    rewrite -> IHIHi.
    reflexivity.
Qed.
 
(* ****** *)

Definition specification_of_mystery_function_21 (mf : nat -> nat -> nat) :=
  (forall j : nat, mf O j = j)
  /\
  (forall i j : nat, mf (S i) j = mf i (S j)).

Definition unit_test_for_mystery_function_21 (mf : nat -> nat -> nat) :=
  (mf O 1 =n= 1) && (mf 1 O =n= 1) && (mf 1 1 =n= 2) && (mf 2 1 =n= 3).

Definition mystery_function_21 (n : nat) (m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_21 mystery_function_21).

Theorem there_is_at_least_one_mystery_function_21 :
  specification_of_mystery_function_21 mystery_function_21.
Proof.
  unfold specification_of_mystery_function_21, mystery_function_21.
  split.
  - intro j.
    rewrite -> (Nat.add_0_l j).
    reflexivity.
  - intros i j.
    Search (S _ + _).
    rewrite (Nat.add_succ_comm i j).
    reflexivity.
Qed.

(* ****** *)

Definition specification_of_mystery_function_22 (mf : nat -> nat -> nat) :=
  forall i j : nat,
    mf O j = j
    /\
    mf (S i) j = mf i (S j).

Definition unit_test_for_mystery_function_22 (mf : nat -> nat -> nat) :=
  (mf O 1 =n= 1) && (mf 1 O =n= 1) && (mf 1 1 =n= 2) && (mf 2 1 =n= 3).

Definition mystery_function_22 (n : nat) (m : nat) : nat :=
  n + m.

Compute (unit_test_for_mystery_function_22 mystery_function_22).

Theorem there_is_at_least_one_mystery_function_22 :
  specification_of_mystery_function_22 mystery_function_22.
Proof.
  unfold specification_of_mystery_function_22, mystery_function_22.
  intros i j.
  split.
  - rewrite -> (Nat.add_0_l j).
    reflexivity.
  - Search (S _ + _).
    rewrite (Nat.add_succ_comm i j).
    reflexivity.
Qed.


(* ********** *)

(* Binary trees of natural numbers: *)

Inductive tree : Type :=
  | Leaf : nat -> tree
  | Node : tree -> tree -> tree.

Definition specification_of_mystery_function_19 (mf : tree -> tree) :=
  (forall n : nat,
     mf (Leaf n) = Leaf n)
  /\
  (forall (n : nat) (t : tree),
     mf (Node (Leaf n) t) = Node (Leaf n) (mf t))
  /\
  (forall t11 t12 t2 : tree,
     mf (Node (Node t11 t12) t2) = mf (Node t11 (Node t12 t2))).

(* You might not manage to prove
   that at most one function satisfies this specification (why?),
   but consider whether the following function does.
   Assuming it does, what does this function do?
   And what is the issue here?
*)

Fixpoint mystery_function_19_aux (t a : tree) : tree :=
  match t with
  | Leaf n =>
     Node (Leaf n) a
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19_aux t2 a)
  end.

Fixpoint mystery_function_19 (t : tree) : tree :=
  match t with
  | Leaf n =>
     Leaf n
  | Node t1 t2 =>
     mystery_function_19_aux t1 (mystery_function_19 t2)
  end.

(* recursive definition, yet the specification of mf19 is not recursive because the tree has changed *)

(* Find rightmost Leaf n *)

Lemma fold_unfold_19_leaf :
  forall n : nat,
  (mystery_function_19 (Leaf n)) = Leaf n.
Proof.
  fold_unfold_tactic mystery_function_19.
Qed.


Lemma fold_unfold_19_case2 :
  forall (n : nat) (t : tree),
    mystery_function_19  (Node (Leaf n) t) = Node (Leaf n) (mystery_function_19 t).
Proof.
  fold_unfold_tactic mystery_function_19.
Qed.

Lemma fold_unfold_19_node :
  forall t11 t12 t2 : tree,
  mystery_function_19 (Node (Node t11 t12) t2) = mystery_function_19 (Node t11 (Node t12 t2)).
Proof.
  fold_unfold_tactic mystery_function_19.
Qed.

Theorem there_is_at_least_one_mystery_function_19 :
  specification_of_mystery_function_19 mystery_function_19.
Proof.
  unfold specification_of_mystery_function_19.
  split.
  - intro n.
    rewrite -> (fold_unfold_19_leaf n).
    reflexivity.
  - split.
    + intros n t.
      Check (fold_unfold_19_case2 n t).
      rewrite -> (fold_unfold_19_case2 n t).
      reflexivity.
    + intros t11 t12 t2.
      rewrite -> (fold_unfold_19_node t11 t12 t2).
      reflexivity.
Qed.

Theorem there_is_at_most_one_mystery_function_19 :
  forall (mf19a mf19b : tree -> tree),
    specification_of_mystery_function_19 mf19a ->
    specification_of_mystery_function_19 mf19b ->
    forall (t : tree),
    mf19a t = mf19b t.
Proof.
  intros mf19a mf19b.
  unfold specification_of_mystery_function_19.
  intros [Sa_Leaf [Sa_Case2 Sa_Node]]
         [Sb_Leaf [Sb_Case2 Sb_Node]].
  intro t.
  induction t as [ n | t1 IHt1 t2 IHt2].
  - Check (Sa_Leaf n).
    rewrite -> (Sa_Leaf n).
    rewrite -> (Sb_Leaf n).
    reflexivity.
  - destruct t1 as [n1 | t11 t12].
    + Check (Sa_Case2 n1 t2).
      rewrite -> (Sa_Case2 n1 t2).
      rewrite -> (Sb_Case2 n1 t2).
      rewrite -> IHt2.
      reflexivity.
    + Check (Sa_Node t11 t12 t2).
      rewrite -> (Sa_Node t11 t12 t2).
      rewrite -> (Sb_Node t11 t12 t2).
Abort.

(* ********** *)

Definition specification_of_mystery_function_05 (mf : nat -> nat) :=
  mf 0 = 1
  /\
  forall i j : nat,
    mf (S (i + j)) = 2 * mf i * mf j.

Definition unit_test_for_mystery_function_05 (mf : nat -> nat) :=
  (mf 0 =n= 1) &&
  (mf 1 =n= 2) &&
  (mf 2 =n= 4) &&
  (mf 3 =n= 8) &&
  (mf 4 =n= 16) &&
  (mf 5 =n= 32).

Definition mystery_function_05 (n : nat) : nat :=
  Nat.pow 2 n.

Compute (unit_test_for_mystery_function_05 mystery_function_05).

Theorem there_is_at_least_one_mystery_function_05 :
  specification_of_mystery_function_05 mystery_function_05.
Proof.
  unfold specification_of_mystery_function_05, mystery_function_05.
  split.
  - Search (_ ^ 0 = 1).
    exact (Nat.pow_0_r 2).
  - intros i j.
    Search (Nat.pow).
    Check (Nat.pow_succ_r' 2 (i + j)).
    rewrite -> (Nat.pow_succ_r' 2 (i + j)).
    Search (_ ^ (_ + _ )).
    Check (Nat.pow_add_r 2 i j).
    rewrite -> (Nat.pow_add_r 2 i j).
    Search (_ * (_ * _) = _ * _ * _).
    Check (Nat.mul_assoc 2 (2 ^ i) (2 ^ j)).
    rewrite -> (Nat.mul_assoc 2 (2 ^ i) (2 ^ j)).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_06 (mf : nat -> nat) :=
  mf 0 = 2
  /\
  forall i j : nat,
    mf (S (i + j)) = mf i * mf j.

Definition unit_test_for_mystery_function_06 (mf : nat -> nat) :=
  (mf 0 =n= 2) &&
  (mf 1 =n= 4) &&
  (mf 2 =n= 8) &&
  (mf 3 =n= 16) &&
  (mf 4 =n= 32) &&
  (mf 5 =n= 64).

Definition mystery_function_06 (n : nat) : nat :=
  Nat.pow 2 (n + 1).

Compute (unit_test_for_mystery_function_06 mystery_function_06).

Theorem there_is_at_least_one_mystery_function_06 :
  specification_of_mystery_function_06 mystery_function_06.
Proof.
  unfold specification_of_mystery_function_06, mystery_function_06.
  split.

  - Search (0 + _ = _).
    Check (Nat.add_0_l 1).
    rewrite -> (Nat.add_0_l 1).
    Search (_ ^ 1 = _).
    Check (Nat.pow_1_r 2).
    exact (Nat.pow_1_r 2).

  - intros i j.
    Search (_ ^ (_ + _ )).
    Check (Nat.pow_add_r 2 (S (i + j)) 1).
    rewrite -> (Nat.pow_add_r 2 (S (i + j)) 1).
    Search (_ ^ (S _)).
    Check (Nat.pow_succ_r' 2 (i + j)).
    rewrite -> (Nat.pow_succ_r' 2 (i + j)).
    Check (Nat.pow_add_r 2 i j).
    rewrite -> (Nat.pow_add_r 2 i j).
    Search (_ ^ (_ + _)).
    rewrite -> (Nat.pow_add_r 2 i 1).
    rewrite -> (Nat.pow_add_r 2 j 1).
    rewrite -> (Nat.pow_1_r 2).
    Search (_ * _ * _).
    rewrite -> (Nat.mul_assoc 2 (2 ^ i) (2 ^ j)).
    Check (Nat.mul_comm (2 ^ i) 2).
    rewrite -> (Nat.mul_comm (2 ^ i) 2).
    Search (_ * _ * _).
    Check (Nat.mul_assoc (2 * 2 ^ i) (2 ^ j) 2).
    rewrite -> (Nat.mul_assoc (2 * 2 ^ i) (2 ^ j) 2).
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_mystery_function_09 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = xorb (mf i) (mf j).

Definition unit_test_for_mystery_function_09 (mf : nat -> bool) :=
  (mf 0 =b= false) &&
  (mf 1 =b= true) &&
  (mf 2 =b= false) &&
  (mf 3 =b= true).

Fixpoint oddp (n : nat) : bool :=
  match n with
  | O => false
  | S n' => negb (oddp n')
  end.

Lemma fold_unfold_oddp_O :
  oddp O = false.
Proof.
  fold_unfold_tactic oddp.
Qed.

Lemma fold_unfold_oddp_S  :
  forall n',
    oddp (S n') = negb (oddp n').
Proof.
  fold_unfold_tactic oddp.
Qed.

Corollary fold_unfold_oddp_1 :
  oddp 1 = true.
Proof.
  rewrite -> (fold_unfold_oddp_S 0).
  rewrite -> fold_unfold_oddp_O.
  reflexivity.
Qed.

Definition mystery_function_09 (n : nat) :=
  oddp n.

Compute (unit_test_for_mystery_function_09 mystery_function_09).

Lemma eureka_lemma_09 :
  forall i j : nat,
    oddp (i + j) = xorb (oddp i) (oddp j).
Proof.
  induction i as [ | i' IHi'].
  - intro j.
    Search (0 + _ = _).
    rewrite -> (Nat.add_0_l j).
    rewrite -> (fold_unfold_oddp_O).
    Search (xorb false _ = _).
    rewrite -> (xorb_false_l (oddp j)).
    reflexivity.
  - intro j.
    Search ((S _) + _ = S (_ + _)).
    Check (Nat.add_succ_l i' j).
    rewrite -> (Nat.add_succ_l i' j).
    Check (fold_unfold_oddp_S (i' + j)).
    rewrite -> (fold_unfold_oddp_S (i' + j)).
    rewrite -> (IHi' j).
    rewrite -> (fold_unfold_oddp_S i').
    Search (negb (xorb _ _)).
    Check (negb_xorb_l (oddp i') (oddp j)).
    exact (negb_xorb_l (oddp i') (oddp j)).
Qed.

Theorem there_is_at_least_one_mystery_function_09 :
  specification_of_mystery_function_09 mystery_function_09.
Proof.
  unfold specification_of_mystery_function_09, mystery_function_09.
  split.
  - exact fold_unfold_oddp_O.

  - split.
    -- exact fold_unfold_oddp_1.
    -- exact eureka_lemma_09.
Qed.

(* ********** *)

Definition specification_of_mystery_function_10 (mf : nat -> bool) :=
  mf 0 = false
  /\
  mf 1 = true
  /\
  forall i j : nat,
    mf (i + j) = (mf i =b= mf j).

(* mf (1 + 0) = false, contradiction! *)

Theorem there_are_zero_mystery_function_10 :
  forall f : nat -> bool,
    specification_of_mystery_function_10 f ->
    exists n : nat,
      f n <> f n.
Proof.
  intro f.
  unfold specification_of_mystery_function_10.
  intros [S_O [S_1 S_other]].
  exists 1.
  Check (Nat.add_0_r).
  rewrite <- (Nat.add_0_r 1) at 1.
  rewrite -> (S_other 1 0).
  rewrite -> S_1 at 2.
  rewrite -> S_O.
  rewrite -> S_1.
  unfold not.
  intro H_absurd.
  Search (_ =b= _).
  Check (eqb_prop true false).
  Check (eqb_prop true false H_absurd).
  apply (eqb_prop true false) in H_absurd.
  discriminate H_absurd.
Qed.

(* ********** *)

Definition specification_of_mystery_function_12 (mf : nat -> nat) :=
  mf 1 = 1
  /\
  forall i : nat,
    mf (S (S i)) = (S (S i)) * mf (S i).

(* vacuous: this should have 2 base cases since (S (S i)), but 0 is not defined *)

Theorem there_are_zero_mystery_function_12 :
  forall f : nat -> bool,
    specification_of_mystery_function_10 f ->
    exists n : nat,
      f n = false.
Proof.
  intro f.
  unfold specification_of_mystery_function_10.
  intros SO.
  destruct SO as [S1 S2].
  exists 0.
  exact S1.
Qed.

(* ********** *)

Definition specification_of_mystery_function_14 (mf : nat -> bool) :=
  (forall q : nat, mf (2 * q) = true)
  /\
  (forall q : nat, mf (S (2 * q)) = false).


Definition mystery_function_14 (n : nat) : bool :=
  match n mod 2 with
  | O => true
  | S _ => false
  end.

Theorem there_is_at_least_one_mystery_function_14 :
  specification_of_mystery_function_14 mystery_function_14.
Proof.
  unfold specification_of_mystery_function_14, mystery_function_14.
  split.
  - intro q.
Qed.


(* ********** *)

(* Simple examples of specifications: *)

(* ***** *)

Definition specification_of_the_factorial_function (fac : nat -> nat) :=
  fac 0 = 1
  /\
  forall n' : nat, fac (S n') = S n' * fac n'.

(* ***** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

(* ********** *)

(* end of week-05_mystery-functions.v *)
