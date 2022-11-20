(* 9_calder-mobiles.v *)
(* FPP 2020 - YSC3236 2020-2021, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 25 Oct 2020 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool.

(* ********** *)

Inductive binary_tree : Type :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

(* ***** *)

Fixpoint weight (t : binary_tree) : nat :=
  match t with
  | Leaf n =>
    n
  | Node t1 t2 =>
    weight t1 + weight t2
  end.

Lemma fold_unfold_weight_Leaf :
  forall n : nat,
    weight (Leaf n) = n.
Proof.
  fold_unfold_tactic weight.
Qed.

Lemma fold_unfold_weight_Node :
  forall t1 t2 : binary_tree,
    weight (Node t1 t2) = weight t1 + weight t2.
Proof.
  fold_unfold_tactic weight.
Qed.

(* ***** *)

Fixpoint balancedp (t : binary_tree) : bool :=
  match t with
  | Leaf n =>
    true
  | Node t1 t2 =>
    balancedp t1 && balancedp t2 && (weight t1 =? weight t2)
  end.

Lemma fold_unfold_balancedp_Leaf :
  forall n : nat,
    balancedp (Leaf n) =
    true.
Proof.
  fold_unfold_tactic balancedp.
Qed.

Lemma fold_unfold_balancedp_Node :
  forall t1 t2 : binary_tree,
    balancedp (Node t1 t2) =
    (balancedp t1 && balancedp t2 && (weight t1 =? weight t2)).
Proof.
  fold_unfold_tactic balancedp.
Qed.

(* ********** *)

Fixpoint wb_ds_aux (t : binary_tree) : option nat :=
  match t with
  | Leaf n =>
    Some n
  | Node t1 t2 =>
    match wb_ds_aux t1 with
    | Some w1 =>
      match wb_ds_aux t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end
  end.

Lemma fold_unfold_wb_ds_aux_Leaf :
  forall n : nat,
    wb_ds_aux (Leaf n) =
    Some n.
Proof.
  fold_unfold_tactic wb_ds_aux.
Qed.

Lemma fold_unfold_wb_ds_aux_Node :
  forall t1 t2 : binary_tree,
    wb_ds_aux (Node t1 t2) =
    match wb_ds_aux t1 with
    | Some w1 =>
      match wb_ds_aux t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic wb_ds_aux.
Qed.

Definition wb_ds (t : binary_tree) : bool :=
  match wb_ds_aux t with
  | Some _ =>
    true
  | None =>
    false
  end.

(* ********** *)

Lemma soundness_of_wb_ds_aux :
  forall (t : binary_tree)
         (w : nat),
    wb_ds_aux t = Some w ->
    balancedp t = true /\ w = weight t.
Proof.
  intro t. 
  induction t as [n | t1 IHt1 t2 IHt2]; intros w H_aux.
  - rewrite -> fold_unfold_wb_ds_aux_Leaf in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balancedp_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux]. 
  - rewrite -> fold_unfold_wb_ds_aux_Node in H_aux.
    case (wb_ds_aux t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balancedp_Node.
           rewrite -> fold_unfold_weight_Node.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           rewrite -> Bt1.
           rewrite -> Bt2.
           rewrite <- W1.
           rewrite <- W2.
           unfold andb.
           symmetry in H_aux.
           split; [exact H_w1_w2 | exact H_aux].
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
Qed.


Theorem soundness_of_wb_ds :
  forall t : binary_tree,
    wb_ds t = true ->
    balancedp t = true.
Proof.
  intros t H_t.
  Check (wb_ds t).
  unfold wb_ds in H_t.
  case (wb_ds_aux t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux t w H_aux).
    destruct (soundness_of_wb_ds_aux t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.

(* ********** *)

Lemma completeness_of_wb_ds_aux :
  forall t : binary_tree,
    (exists w : nat,
        wb_ds_aux t = Some w /\ w = weight t /\ balancedp t = true)
    \/
    (wb_ds_aux t = None /\ balancedp t = false).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_balancedp_Leaf.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + w2).
      unfold andb.
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balancedp_Node.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
Qed.

Theorem completeness_of_wb_ds :
  forall t : binary_tree,
    balancedp t = true ->
    wb_ds t = true.
Proof.
  intros t H_t.
  unfold wb_ds.
  destruct (completeness_of_wb_ds_aux t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    discriminate H_b.
Qed.

(* ********** *)

Fixpoint balanced (t : binary_tree) : Prop :=
  match t with
  | Leaf n =>
    True
  | Node t1 t2 =>
    balanced t1 /\ balanced t2 /\ weight t1 = weight t2
  end.


Lemma fold_unfold_balanced_Leaf :
  forall n : nat,
    balanced (Leaf n) =
    True.
Proof.
  fold_unfold_tactic balanced.
Qed.

Lemma fold_unfold_balanced_Node :
  forall t1 t2 : binary_tree,
    balanced (Node t1 t2) =
    (balanced t1 /\ balanced t2 /\ weight t1 = weight t2).
Proof.
  fold_unfold_tactic balanced.
Qed.

(*
 ex4a:
    Prove the soundness and the completeness of balancedp. (Hint: Lemmas andb_prop and andb_true_intro will come handy (remembering that && (the infix notation for andb) associates to the left), and so will Lemmas beq_nat_true and Nat.eqb_refl.)
 *)

(*
andb_true_intro: forall b1 b2 : bool, b1 = true /\ b2 = true -> b1 && b2 = true
andb_prop: forall a b : bool, a && b = true -> a = true /\ b = true
Nat.eqb_refl: forall x : nat, (x =? x) = true
beq_nat_true: forall n m : nat, (n =? m) = true -> n = m
 *)

Theorem soundness_of_balancedp :
  forall t : binary_tree,
    balancedp t = true ->
    balanced t.
Proof.
  intros t H_t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - rewrite -> (fold_unfold_balanced_Leaf n).
    exact I.
  - rewrite -> (fold_unfold_balanced_Node t1 t2).
    rewrite -> (fold_unfold_balancedp_Node t1 t2) in H_t.
    Check (andb_prop (balancedp t1 && balancedp t2) (weight t1 =? weight t2) H_t).
    assert (H_t' :=  (andb_prop (balancedp t1 && balancedp t2) (weight t1 =? weight t2) H_t)).
    destruct H_t' as [H_t12 H_w].
    Check (andb_prop (balancedp t1) (balancedp t2) H_t12).
    assert (H_t'' := (andb_prop (balancedp t1) (balancedp t2) H_t12)).
    destruct H_t'' as [H_t1 H_t2].
    Check (beq_nat_true (weight t1) (weight t2) H_w).
    assert (H_w' :=  (beq_nat_true (weight t1) (weight t2) H_w)).
    apply IHt1 in H_t1.
    apply IHt2 in H_t2.
    Check (conj H_t1 H_t2).
    Check (conj (conj H_t1 H_t2) H_w').
    apply and_assoc.
    exact (conj (conj H_t1 H_t2) H_w').
Qed.

Theorem completeness_of_balancedp :
  forall t : binary_tree,
    balanced t ->
    balancedp t = true.
Proof.
  intros t H_t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - rewrite -> (fold_unfold_balancedp_Leaf n).
    reflexivity.
  - rewrite -> (fold_unfold_balancedp_Node t1 t2).
    rewrite -> (fold_unfold_balanced_Node t1 t2) in H_t.
    destruct H_t as [H_t1 [H_t2 H_w]].
    Search (_ =? _).
    apply Nat.eqb_eq in H_w.
    apply IHt1 in H_t1.
    apply IHt2 in H_t2.
    rewrite -> H_t1.
    rewrite -> H_t2.
    rewrite -> H_w.
    unfold andb.
    reflexivity.
Qed.

(*
ex4b:
    Modify mutatis mutandis the statements of the soundness and the completeness of wb_ds using balanced instead of balancedp. Then prove these statements in two distinct ways.
 *)

Theorem balanced_and_balancedp_is_equivalent :
  forall t : binary_tree,
    balanced t <-> balancedp t = true.
Proof.
  intro t.
  split.
  - exact (completeness_of_balancedp t).
  - exact (soundness_of_balancedp t).
Qed.

Lemma soundness_of_wb_ds_aux' :
  forall (t : binary_tree)
         (w : nat),
    wb_ds_aux t = Some w ->
    balanced t /\ w = weight t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2]; intros w H_aux.
  - rewrite -> fold_unfold_wb_ds_aux_Leaf in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balanced_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux].
  - rewrite -> fold_unfold_wb_ds_aux_Node in H_aux.
    case (wb_ds_aux t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balanced_Node.
           rewrite -> fold_unfold_weight_Node.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           Check (beq_nat_true w1 w2 H_w1_w2).
           assert (H_weight12 := (beq_nat_true w1 w2 H_w1_w2)).
           rewrite -> W1 in H_weight12.
           rewrite -> W2 in H_weight12.
           symmetry in H_aux.
           rewrite -> W1 in H_aux.
           rewrite -> W2 in H_aux.
           Check (conj (conj Bt1 Bt2) H_weight12).
           split.
           ++ split.
              +++ exact Bt1.
              +++ split.
                  ++++ exact Bt2.
                  ++++ exact H_weight12.
           ++ exact H_aux.
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
Qed.

Theorem soundness_of_wb_ds' :
  forall t : binary_tree,
    wb_ds t = true ->
    balanced t.
Proof.
  intros t H_t.
  unfold wb_ds in H_t.
  case (wb_ds_aux t) as [w | ] eqn:H_aux.
  - Check (soundness_of_wb_ds_aux' t w H_aux).
    destruct (soundness_of_wb_ds_aux' t w H_aux) as [ly _].
    exact ly.
  - discriminate H_t.

    Restart.
    
    intros t.
    assert (H := soundness_of_wb_ds t).
    intro H_wb_ds.
    apply (balanced_and_balancedp_is_equivalent t).
    exact (H H_wb_ds).    
Qed.

Lemma completeness_of_wb_ds_aux' :
  forall t : binary_tree,
    (exists w : nat,
        wb_ds_aux t = Some w /\ w = weight t /\ balanced t)
    \/
    (wb_ds_aux t = None /\ not (balanced t)).
Proof.
  intro t.
  induction t as [n | t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_weight_Leaf.
    rewrite -> fold_unfold_balanced_Leaf.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (w1 + w2).
      split.
      * reflexivity.
      * split.
        reflexivity.
        split.
        ** exact B1.
        ** split.
           *** exact B2.
           *** exact (beq_nat_true w1 w2 H_w1_w2).
    + right.
      split.
      ++ reflexivity.
      ++ unfold not.
         apply beq_nat_false in H_w1_w2.
         unfold not in H_w1_w2.
         intros [_ [_ H3]].
         exact (H_w1_w2 H3).
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    split.
    + reflexivity.
    + unfold not.
      unfold not in B2.
      intros [_ [H2 _]].
      exact (B2 H2).
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    right.
    split.
    + reflexivity.
    + unfold not.
      unfold not in B1.
      intros [H1 [_ _]].
      exact (B1 H1).
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_weight_Node.
    rewrite -> fold_unfold_balanced_Node.
    rewrite -> Ht1.
    right.
    split.
    + reflexivity.
    + unfold not.
      unfold not in B1.
      intros [H1 [_ _]].
      exact (B1 H1).
Qed.

Theorem completeness_of_wb_ds' :
  forall t : binary_tree,
    balanced t ->
    wb_ds t = true.
Proof.
  intros t H_t.
  unfold wb_ds.
  destruct (completeness_of_wb_ds_aux' t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_aux.
    contradiction.

    Restart.

    intros t.
    assert (H := completeness_of_wb_ds t).
    intro H_balanced.
    apply (balanced_and_balancedp_is_equivalent t) in H_balanced.
    exact (H H_balanced).
Qed.

(* ********** *)

(* ********** *)

Fixpoint binary_tree_fold (V : Type) (lea : nat -> V) (nod : V -> V -> V) (t : binary_tree) : V :=
  match t with
  | Leaf n =>
    lea n
  | Node t1 t2 =>
    nod (binary_tree_fold V lea nod t1)
        (binary_tree_fold V lea nod t2)
  end.

Lemma fold_unfold_binary_tree_fold_Leaf :
  forall (V : Type)
         (lea : nat -> V)
         (nod : V -> V -> V)
         (n : nat),
    binary_tree_fold V lea nod (Leaf n) =
    lea n.
Proof.
  fold_unfold_tactic binary_tree_fold.
Qed.

Lemma fold_unfold_binary_tree_fold_Node :
  forall (V : Type)
         (lea : nat -> V)
         (nod : V -> V -> V)
         (t1 t2 : binary_tree),
    binary_tree_fold V lea nod (Node t1 t2) =
    nod (binary_tree_fold V lea nod t1)
        (binary_tree_fold V lea nod t2).
Proof.
  fold_unfold_tactic binary_tree_fold.
Qed.

(* Implement ws_ds using binary_tree_fold *)

Definition wb_ds_alt (t : binary_tree) : bool :=
  match binary_tree_fold (option nat)
                         (fun w => Some w)
                         (fun ow1 ow2 =>
                          match ow1 with
                          | Some w1 =>
                            match ow2 with
                            | Some w2 =>
                              if beq_nat w1 w2 then Some (w1 + w2) else None
                            | None => None
                            end
                          | None => None
                          end)
                         t with
  | None => false
  | Some _ => true
  end.

(* prove that this alternative implementation is equivalent to the original one *)

Proposition wb_ds_alt_and_wb_ds_are_equivalent_aux :
  forall t : binary_tree,
    wb_ds_aux t =
    binary_tree_fold (option nat)
                     (fun w : nat => Some w)
                     (fun ow1 ow2 : option nat =>
                        match ow1 with
                        | Some w1 =>
                          match ow2 with
                          | Some w2 =>
                            if beq_nat w1 w2 then Some (w1 + w2) else None
                          | None => None
                          end
                        | None => None
                        end)
                     t.
Proof.
  intro t.
  induction t as [n | t1 IHt1 t2 IHt2].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf.
    rewrite -> fold_unfold_binary_tree_fold_Leaf.
    reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node.
    rewrite -> fold_unfold_binary_tree_fold_Node.
    case (wb_ds_aux t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux t2) as [w2 | ] eqn:Ht2.
      * rewrite <- IHt1.
        rewrite <- IHt2.
        reflexivity.
      * rewrite <- IHt1.
        rewrite <- IHt2.
        reflexivity.
    + rewrite <- IHt1.
      reflexivity.
Qed.

Proposition wb_ds_alt_and_wb_ds_are_equivalent :
  forall (t: binary_tree),
    wb_ds t = wb_ds_alt t.
Proof.
  intro t.
  unfold wb_ds, wb_ds_alt.
  rewrite <- wb_ds_alt_and_wb_ds_are_equivalent_aux.
  reflexivity.
Qed.

(* ********** *)

(* Exercise 6 : Calder mobiles with weightful bars *)

(* Representation *)

Inductive binary_tree_node_weighted : Type :=
| Leaf_node_weighted : nat -> binary_tree_node_weighted
| Node_node_weighted : nat -> binary_tree_node_weighted -> binary_tree_node_weighted -> binary_tree_node_weighted.

Fixpoint weight_node_weighted (t : binary_tree_node_weighted) : nat :=
  match t with
  | Leaf_node_weighted n =>
    n
  | Node_node_weighted N t1 t2 =>
    N + weight_node_weighted t1 + weight_node_weighted t2
  end.

Lemma fold_unfold_weight_Leaf_node_weighted :
  forall n : nat,
    weight_node_weighted (Leaf_node_weighted n) = n.
Proof.
  fold_unfold_tactic weight_node_weighted.
Qed.

Lemma fold_unfold_weight_Node_node_weighted :
  forall (t1 t2 : binary_tree_node_weighted)
         (N : nat),
    weight_node_weighted (Node_node_weighted N t1 t2) = N + weight_node_weighted t1 + weight_node_weighted t2.
Proof.
  fold_unfold_tactic weight_node_weighted.
Qed.

Fixpoint balancedp_node_weighted (t : binary_tree_node_weighted) : bool :=
  match t with
  | Leaf_node_weighted n =>
    true
  | Node_node_weighted N t1 t2 =>
    balancedp_node_weighted t1 && balancedp_node_weighted t2 && (weight_node_weighted t1 =? weight_node_weighted t2)
  end.


Lemma fold_unfold_balancedp_Leaf_node_weighted :
  forall n : nat,
    balancedp_node_weighted (Leaf_node_weighted n) =
    true.
Proof.
  fold_unfold_tactic balancedp_node_weighted.
Qed.

Lemma fold_unfold_balancedp_Node_node_weighted :
  forall (t1 t2 : binary_tree_node_weighted)
         (N : nat),
    balancedp_node_weighted (Node_node_weighted N t1 t2) =
    (balancedp_node_weighted t1 && balancedp_node_weighted t2 && (weight_node_weighted t1 =? weight_node_weighted t2)).
Proof.
  fold_unfold_tactic balancedp_node_weighted.
Qed.

(* Soundness and completeness *)


Fixpoint wb_ds_aux_node_weighted (t : binary_tree_node_weighted) : option nat :=
  match t with
  | Leaf_node_weighted n =>
    Some n
  | Node_node_weighted N t1 t2 =>
    match wb_ds_aux_node_weighted t1 with
    | Some w1 =>
      match wb_ds_aux_node_weighted t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (N + w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end
  end.

Lemma fold_unfold_wb_ds_aux_Leaf_node_weighted :
  forall n : nat,
    wb_ds_aux_node_weighted (Leaf_node_weighted n) =
    Some n.
Proof.
  fold_unfold_tactic wb_ds_aux_node_weighted.
Qed.

Lemma fold_unfold_wb_ds_aux_Node_node_weighted :
  forall (t1 t2 : binary_tree_node_weighted)
         (N : nat),
    wb_ds_aux_node_weighted (Node_node_weighted N t1 t2) =
    match wb_ds_aux_node_weighted t1 with
    | Some w1 =>
      match wb_ds_aux_node_weighted t2 with
      | Some w2 =>
        if beq_nat w1 w2
        then Some (N + w1 + w2)
        else None
      | None =>
        None
      end
    | None =>
      None
    end.
Proof.
  fold_unfold_tactic wb_ds_aux_node_weighted.
Qed.

Definition wb_ds_node_weighted (t : binary_tree_node_weighted) : bool :=
  match wb_ds_aux_node_weighted t with
  | Some _ =>
    true
  | None =>
    false
  end.

(* ********** *)

Lemma soundness_of_wb_ds_aux_node_weighted :
  forall (t : binary_tree_node_weighted)
         (w : nat),
    wb_ds_aux_node_weighted t = Some w ->
    balancedp_node_weighted t = true /\ w = weight_node_weighted t.
Proof.
  intro t.
  induction t as [n |N  t1 IHt1 t2 IHt2]; intros w H_aux.
  - rewrite -> fold_unfold_wb_ds_aux_Leaf_node_weighted in H_aux.
    injection H_aux as H_aux.
    rewrite -> fold_unfold_balancedp_Leaf_node_weighted.
    rewrite -> fold_unfold_weight_Leaf_node_weighted.
    symmetry in H_aux.
    split; [reflexivity | exact H_aux].
  - rewrite -> fold_unfold_wb_ds_aux_Node_node_weighted in H_aux.
    case (wb_ds_aux_node_weighted t1) as [w1 | ] eqn:Ht1.
    + case (wb_ds_aux_node_weighted t2) as [w2 | ] eqn:Ht2.
      * case (w1 =? w2) eqn:H_w1_w2.
        ** injection H_aux as H_aux.
           rewrite -> fold_unfold_balancedp_Node_node_weighted.
           rewrite -> fold_unfold_weight_Node_node_weighted.
           Check (IHt1 w1 (eq_refl (Some w1))).
           destruct (IHt1 w1 (eq_refl (Some w1))) as [Bt1 W1].
           destruct (IHt2 w2 (eq_refl (Some w2))) as [Bt2 W2].
           rewrite -> Bt1.
           rewrite -> Bt2.
           rewrite <- W1.
           rewrite <- W2.
           unfold andb.
           symmetry in H_aux.
           split; [exact H_w1_w2 | exact H_aux].
        ** discriminate H_aux.
      * discriminate H_aux.
    + discriminate H_aux.
Qed.

Theorem soundness_of_wb_ds_node_weighted :
  forall (t : binary_tree_node_weighted),
    wb_ds_node_weighted t = true ->
    balancedp_node_weighted t = true.
Proof.
  intros t H_t.
  unfold wb_ds_node_weighted in H_t.
  case (wb_ds_aux_node_weighted t) as [w | ] eqn:H_aux.
  + Check (soundness_of_wb_ds_aux_node_weighted t w H_aux).
    destruct (soundness_of_wb_ds_aux_node_weighted t w H_aux) as [ly _].
    exact ly.
  + discriminate H_t.
Qed.

(* ********** *)

Lemma completeness_of_wb_ds_aux_node_weighted :
  forall t : binary_tree_node_weighted,
    (exists w : nat,
        wb_ds_aux_node_weighted t = Some w /\ w = weight_node_weighted t /\ balancedp_node_weighted t = true)
    \/
    (wb_ds_aux_node_weighted t = None /\ balancedp_node_weighted t = false).
Proof.
  intro t.
  induction t as [n | N t1 [[w1 [Ht1 [W1 B1]]] | [Ht1 B1]] t2 [[w2 [Ht2 [W2 B2]]] | [Ht2 B2]]].
  - rewrite -> fold_unfold_wb_ds_aux_Leaf_node_weighted.
    rewrite -> fold_unfold_weight_Leaf_node_weighted.
    rewrite -> fold_unfold_balancedp_Leaf_node_weighted.
    left.
    exists n.
    split; [reflexivity | (split; reflexivity)].
  - rewrite -> fold_unfold_wb_ds_aux_Node_node_weighted.
    rewrite -> fold_unfold_weight_Node_node_weighted.
    rewrite -> fold_unfold_balancedp_Node_node_weighted.
    rewrite -> Ht1.
    rewrite -> Ht2.
    rewrite <- W1.
    rewrite <- W2.
    rewrite -> B1.
    rewrite -> B2.
    case (w1 =? w2) eqn:H_w1_w2.
    + left.
      exists (N + w1 + w2).
      unfold andb.
      split; [reflexivity | (split; reflexivity)].
    + right.
      unfold andb.
      split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node_node_weighted.
    rewrite -> fold_unfold_weight_Node_node_weighted.
    rewrite -> fold_unfold_balancedp_Node_node_weighted.
    rewrite -> Ht1.
    rewrite -> Ht2.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node_node_weighted.
    rewrite -> fold_unfold_weight_Node_node_weighted.
    rewrite -> fold_unfold_balancedp_Node_node_weighted.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    rewrite -> B2.
    unfold andb.
    split; reflexivity.
  - rewrite -> fold_unfold_wb_ds_aux_Node_node_weighted.
    rewrite -> fold_unfold_weight_Node_node_weighted.
    rewrite -> fold_unfold_balancedp_Node_node_weighted.
    rewrite -> Ht1.
    right.
    rewrite -> B1.
    unfold andb.
    split; reflexivity.
Qed.

Theorem completeness_of_wb_ds_node_weighted :
  forall t : binary_tree_node_weighted,
    balancedp_node_weighted t = true ->
    wb_ds_node_weighted t = true.
Proof.
  intros t H_t.
  unfold wb_ds_node_weighted.
  destruct (completeness_of_wb_ds_aux_node_weighted t) as [[w [H_aux [H_w H_b]]] | [H_aux H_b]].
  - rewrite -> H_aux.
    reflexivity.
  - rewrite -> H_t in H_b.
    discriminate H_b.
Qed.


(* ********** *)

Fixpoint balanced_node_weighted (t : binary_tree_node_weighted) : Prop :=
  match t with
  | Leaf_node_weighted n =>
    True
  | Node_node_weighted N t1 t2 =>
    balanced_node_weighted t1 /\ balanced_node_weighted t2 /\ weight_node_weighted t1 = weight_node_weighted t2
  end.


Lemma fold_unfold_balanced_Leaf_node_weighted :
  forall n : nat,
    balanced_node_weighted (Leaf_node_weighted n) =
    True.
Proof.
  fold_unfold_tactic balanced_node_weighted.
Qed.

Lemma fold_unfold_balanced_Node_node_weighted :
  forall (t1 t2 : binary_tree_node_weighted)
         (N : nat),
    balanced_node_weighted (Node_node_weighted N t1 t2) =
    (balanced_node_weighted t1 /\ balanced_node_weighted t2 /\ weight_node_weighted t1 = weight_node_weighted t2).
Proof.
  fold_unfold_tactic balanced_node_weighted.
Qed.

Theorem soundness_of_balancedp_node_weighted :
  forall t : binary_tree_node_weighted,
    balancedp_node_weighted t = true ->
    balanced_node_weighted t.
Proof.
  intros t H_t.
  induction t as [n | N t1 IHt1 t2 IHt2].
  - rewrite -> (fold_unfold_balanced_Leaf_node_weighted n).
    exact I.
  - rewrite -> (fold_unfold_balanced_Node_node_weighted t1 t2).
    rewrite -> (fold_unfold_balancedp_Node_node_weighted t1 t2) in H_t.
    Check (andb_prop (balancedp_node_weighted t1 && balancedp_node_weighted t2) (weight_node_weighted t1 =? weight_node_weighted t2) H_t).
    assert (H_t' :=  (andb_prop (balancedp_node_weighted t1 && balancedp_node_weighted t2) (weight_node_weighted t1 =? weight_node_weighted t2) H_t)).
    destruct H_t' as [H_t12 H_w].
    Check (andb_prop (balancedp_node_weighted t1) (balancedp_node_weighted t2) H_t12).
    assert (H_t'' := (andb_prop (balancedp_node_weighted t1) (balancedp_node_weighted t2) H_t12)).
    destruct H_t'' as [H_t1 H_t2].
    Check (beq_nat_true (weight_node_weighted t1) (weight_node_weighted t2) H_w).
    assert (H_w' :=  (beq_nat_true (weight_node_weighted t1) (weight_node_weighted t2) H_w)).
    apply IHt1 in H_t1.
    apply IHt2 in H_t2.
    Check (conj H_t1 H_t2).
    Check (conj (conj H_t1 H_t2) H_w').
    apply and_assoc.
    exact (conj (conj H_t1 H_t2) H_w').
Qed.

Theorem completeness_of_balancedp_node_weighted :
  forall t : binary_tree_node_weighted,
    balanced_node_weighted t ->
    balancedp_node_weighted t = true.
Proof.
  intros t H_t.
  induction t as [n | N t1 IHt1 t2 IHt2].
  - rewrite -> (fold_unfold_balancedp_Leaf_node_weighted n).
    reflexivity.
  - rewrite -> (fold_unfold_balancedp_Node_node_weighted t1 t2).
    rewrite -> (fold_unfold_balanced_Node_node_weighted t1 t2) in H_t.
    destruct H_t as [H_t1 [H_t2 H_w]].
    Search (_ =? _).
    apply Nat.eqb_eq in H_w.
    apply IHt1 in H_t1.
    apply IHt2 in H_t2.
    rewrite -> H_t1.
    rewrite -> H_t2.
    rewrite -> H_w.
    unfold andb.
    reflexivity.
Qed.

(* ********** *)

(* End of week-10_calder-mobiles.v *)
