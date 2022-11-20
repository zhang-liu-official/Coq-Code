(* 7_soundness-and-completeness-of-equality-predicates-revisited.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 03 Oct 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

Definition is_a_sound_and_complete_equality_predicate (V : Type) (V_eqb : V -> V -> bool) :=
  forall v1 v2 : V,
    V_eqb v1 v2 = true <-> v1 = v2.

(* ********** *)

Check Bool.eqb.
(* eqb : bool -> bool -> bool *)

Definition bool_eqb (b1 b2 : bool) : bool :=
  match b1 with
  | true =>
    match b2 with
    | true =>
      true
    | false =>
      false
    end
  | false =>
    match b2 with
    | true =>
      false
    | false =>
      true
    end
  end.
(*
Lemma bool_eqb_is_reflexive :
  forall b : bool,
    bool_eqb b b = true.
Proof.
Abort.

Search (eqb _ _ = _ -> _ = _).
(* eqb_prop: forall a b : bool, eqb a b = true -> a = b *)
 *)

Proposition soundness_and_completeness_of_bool_eqb :
  is_a_sound_and_complete_equality_predicate bool bool_eqb.
Proof.
  unfold is_a_sound_and_complete_equality_predicate.
  exact eqb_true_iff.
Qed.

(* ***** *)

Proposition soundness_and_completeness_of_Bool_eqb :
  is_a_sound_and_complete_equality_predicate bool eqb.
Proof.
  exact soundness_and_completeness_of_bool_eqb.
Qed.

(* ********** *)

Check Nat.eqb.
(* Nat.eqb : nat -> nat -> bool *)

Fixpoint nat_eqb (n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O =>
      true
    | S n2' =>
      false
    end
  | S n1' =>
    match n2 with
    | O =>
      false
    | S n2' =>
      nat_eqb n1' n2'
    end
  end.

Lemma fold_unfold_nat_eqb_O :
  forall n2 : nat,
    nat_eqb 0 n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic nat_eqb.
Qed.

Lemma fold_unfold_nat_eqb_S :
  forall n1' n2 : nat,
    nat_eqb (S n1') n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      nat_eqb n1' n2'
    end.
Proof.
  fold_unfold_tactic nat_eqb.
Qed.

Search (Nat.eqb _ _ = true -> _ = _).
(* beq_nat_true: forall n m : nat, (n =? m) = true -> n = m *)

Proposition soundness_and_completeness_of_nat_eqb :
  is_a_sound_and_complete_equality_predicate nat nat_eqb.
Proof.
  exact Nat.eqb_eq.
Qed.

(* ***** *)

Lemma fold_unfold_Nat_eqb_O :
  forall n2 : nat,
    0 =? n2 =
    match n2 with
    | O =>
      true
    | S _ =>
      false
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Lemma fold_unfold_Nat_eqb_S :
  forall n1' n2 : nat,
    S n1' =? n2 =
    match n2 with
    | O =>
      false
    | S n2' =>
      n1' =? n2'
    end.
Proof.
  fold_unfold_tactic Nat.eqb.
Qed.

Proposition soundness_and_completeness_of_Nat_eqb :
  is_a_sound_and_complete_equality_predicate nat Nat.eqb.
Proof.
  exact soundness_and_completeness_of_nat_eqb.
Qed.

(* ********** *)

Definition option_eqb (V : Type) (V_eqb : V -> V -> bool) (ov1 ov2 : option V) : bool :=
  match ov1 with
  | Some v1 =>
    match ov2 with
    | Some v2 =>
      V_eqb v1 v2
    | None =>
      false
    end
  | None =>
    match ov2 with
    | Some v2 =>
      false
    | None =>
      true
    end
  end.

Proposition soundness_and_completeness_of_option_eqb :
  forall (V : Type)
         (V_eqb : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V V_eqb ->
    is_a_sound_and_complete_equality_predicate (option V) (option_eqb V V_eqb).
Proof.
  intros V V_eqb.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_both [v1 | ] [v2 | ]; unfold option_eqb.

  - destruct (H_both v1 v2) as [H_sound H_complete].
    split; intro H_v1_v2.

    -- rewrite -> (H_sound H_v1_v2).
       reflexivity.

    -- injection H_v1_v2 as H_v1_v2.
       exact (H_complete H_v1_v2).

  - split; intro H_absurd; discriminate H_absurd.

  - split; intro H_absurd; discriminate H_absurd.

  - split; reflexivity.
Qed.

(* ***** *)


Definition option_option_eqb (V : Type) (V_eqb : V -> V -> bool) (oov1 oov2 : option (option V)) : bool :=
    match oov1 with
  | Some ov1 =>
    match oov2 with
    | Some ov2 =>
      match ov1 with
      | Some v1 =>
        match ov2 with
        | Some v2 =>
          V_eqb v1 v2
        | None =>
          false
        end
      | None =>
        match ov2 with
        | Some v2 =>
          false
        | None =>
          true
        end
      end
    | None =>
      false
    end
  | None =>
    match oov2 with
    | Some ov2 =>
      false
    | None =>
      true
    end
  end.


Proposition soundness_and_completeness_of_option_option_eqb :
  forall (V : Type)
         (V_eqb : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V V_eqb ->
    is_a_sound_and_complete_equality_predicate (option (option V)) (option_option_eqb V V_eqb).
Proof.
  intros V V_eqb.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_both [[v1 | ] | ] [[v2 | ] | ]; unfold option_option_eqb.
  destruct (H_both v1 v2) as [H_sound H_complete].
  split; intro H_v1_v2.
  -- rewrite -> (H_sound H_v1_v2).
     reflexivity.
  -- injection H_v1_v2 as H_v1_v2.
     exact (H_complete H_v1_v2).
  -- split; intro H_absurd; discriminate H_absurd.

  -- split; intro H_absurd; discriminate H_absurd.

  -- split; intro H_absurd; discriminate H_absurd.

  -- split; reflexivity.

  -- split; intro H_absurd; discriminate H_absurd.

  -- split; intro H_absurd; discriminate H_absurd.

  -- split; intro H_absurd; discriminate H_absurd.

  -- split; reflexivity.

     Restart.

     intros V V_eqb H_V.
     unfold is_a_sound_and_complete_equality_predicate.
     Check (soundness_and_completeness_of_option_eqb V V_eqb H_V).
     Check (soundness_and_completeness_of_option_eqb (option V) (option_eqb V V_eqb)).
     Check (soundness_and_completeness_of_option_eqb (option V) (option_eqb V V_eqb) (soundness_and_completeness_of_option_eqb V V_eqb H_V)).
     unfold option_option_eqb.
     exact  (soundness_and_completeness_of_option_eqb (option V) (option_eqb V V_eqb) (soundness_and_completeness_of_option_eqb V V_eqb H_V)).

Qed. 
(* ********** *)

Definition pair_eqb (V W : Type) (V_eqb : V -> V -> bool) (W_eqb : W -> W -> bool) (p1 p2 : V * W) : bool :=
  match p1 with
  | (v1, w1) =>
     match p2 with
    | (v2, w2) =>
      V_eqb v1 v2 && W_eqb w1 w2
    end
  end.

Proposition soundness_and_completeness_of_pair_eqb :
  forall (V W : Type)
         (V_eqb : V -> V -> bool)
         (W_eqb : W -> W -> bool),
    is_a_sound_and_complete_equality_predicate V V_eqb ->
    is_a_sound_and_complete_equality_predicate W W_eqb ->
    forall p1 p2 : V * W,
      pair_eqb V W V_eqb W_eqb p1 p2 = true <-> p1 = p2.
Proof. 
  intros V W.
  intro V_eqb.
  intro W_eqb.
  unfold is_a_sound_and_complete_equality_predicate.
  intros H_V H_W. 
  intros p1 p2.
  destruct p1 as [v1 w1].
  destruct p2 as [v2 w2].
  destruct (H_V v1 v2) as [H_soundness_V H_completeness_V].
  destruct (H_W w1 w2) as [H_soundness_W H_completeness_W].
  unfold pair_eqb.
  split. 
  - Search (_ && _ = true). 
  intro H.
  Check (andb_true_iff).
  rewrite -> (andb_true_iff (V_eqb v1 v2) (W_eqb w1 w2) ) in H. 
  destruct H as [H_V_eqb H_W_eqb].
  rewrite -> (H_soundness_V H_V_eqb).
  rewrite -> (H_soundness_W H_W_eqb).
  reflexivity.
  - intro H. 
    injection H as H_0.
    rewrite -> (andb_true_iff (V_eqb v1 v2) (W_eqb w1 w2)).
    split.
    -- exact (H_completeness_V H_0).
    -- exact  (H_completeness_W H).
Qed. 


Definition nat_bool_eqb :=
  pair_eqb nat bool nat_eqb bool_eqb.

Proposition soundness_and_completeness_of_nat_bool_eqb :
    is_a_sound_and_complete_equality_predicate nat nat_eqb ->
    is_a_sound_and_complete_equality_predicate bool bool_eqb ->
    forall p1 p2 : nat * bool,
      nat_bool_eqb p1 p2 = true <-> p1 = p2.
Proof.
  Check (soundness_and_completeness_of_pair_eqb).
  Check (soundness_and_completeness_of_pair_eqb nat bool nat_eqb bool_eqb).
  exact (soundness_and_completeness_of_pair_eqb nat bool nat_eqb bool_eqb).
Qed.        
                              
                               (* ********** *)


Fixpoint list_eqb (V : Type) (V_eqb : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      V_eqb v1 v2 && list_eqb V V_eqb v1s' v2s'
    end
  end.

Lemma fold_unfold_list_eqb_nil :
  forall (V : Type)
         (V_eqb : V -> V -> bool)
         (v2s : list V),
    list_eqb V V_eqb nil v2s =
    match v2s with
    | nil =>
      true
    | v2 :: v2s' =>
      false
    end.
Proof.
  fold_unfold_tactic list_eqb.
Qed.

Lemma fold_unfold_list_eqb_cons :
  forall (V : Type)
         (V_eqb : V -> V -> bool)
         (v1 : V)
         (v1s' v2s : list V),
    list_eqb V V_eqb (v1 :: v1s') v2s =
    match v2s with
    | nil =>
      false
    | v2 :: v2s' =>
      V_eqb v1 v2 && list_eqb V V_eqb v1s' v2s'
    end.
Proof.
  fold_unfold_tactic list_eqb.
Qed.

Proposition soundness_and_completeness_of_list_eqb :
  forall (V : Type)
         (V_eqb : V -> V -> bool),
    is_a_sound_and_complete_equality_predicate V V_eqb ->
    is_a_sound_and_complete_equality_predicate (list V) (list_eqb V V_eqb).
Proof.
Abort.*)
(* ********** *)

(* end of week-07_soundness-and-completeness-of-equality-predicates-revisited.v *)
