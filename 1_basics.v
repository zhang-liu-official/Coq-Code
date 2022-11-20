(* 1_basics_of_functional-programming-in-Coq.v *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Liu Zhang <zhangliu@u.yale-nus.edu.sg>*)
(* Version of 15 Aug 2020 *)

(* ********** *)

Require Import Arith Bool.

Check (2 =? 3).
Compute (2 =? 3).

(* Alternatively we can define our own notation: *)

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* Exercise 1 *)

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
  &&
  (candidate 1000 5 =n= 1005)
  &&
  (candidate 7 0 =n= 7)
  &&
  (candidate 54 5 =n= 59)
  .

Fixpoint add_v1 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => S (add_v1 i' j)
  end.

Compute (test_add add_v1).

Fixpoint add_v2 (i j : nat) : nat :=
  match i with
    | O => j
    | S i' => add_v2 i' (S j)
  end.

Compute (test_add add_v2).

Definition add_v3 (i j : nat) : nat :=
  let fix visit n :=
    match n with
      | O => j
      | S n' => S (visit n')
    end
  in visit i.

Compute (test_add add_v3).

(* ***** *)

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
  (candidate 7 6 =n= 42).

Fixpoint mul_v1 (i j : nat) : nat :=
  match i with
    | O => O
    | S i' => j + (mul_v1 i' j)
  end.

Compute (test_mul mul_v1).

Fixpoint mul_v2 (i j : nat) : nat :=
  match i with
  | O => 0
  | S i' => add_v1 j (mul_v1 i' j)
  end.


Compute (test_mul mul_v2).

(* ***** *)

Definition test_power (candidate: nat -> nat -> nat) : bool :=
  (candidate 2 0 =n= 1)
  &&
  (candidate 2 1 =n= 2)
  &&
  (candidate 2 2 =n= 4)
  &&
  (candidate 2 3 =n= 8)
  &&
  (candidate 2 4 =n= 16)
  &&
  (candidate 2 5 =n= 32)
  &&
  (candidate 3 3 =n= 27)
  &&
  (candidate 4 3 =n= 64)
  &&
  (candidate 5 7 =n= 78125)
  &&
  (candidate 8 4 =n= 4096). 

Fixpoint power_v1 (x n : nat) : nat :=
  match n with
  | O => 1
  | S n' => x * (power_v1 x n')
  end.
(*
Fixpoint power_v1' (x n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mul_v1 x (power_v1 x n')
  end.
*)

Definition power_v2 (x n : nat) : nat :=
  let fix pow x n a :=
      match n with
      | O => a
      | S n' => pow x n' (a * x)
      end
  in
  pow x n 1.

Compute (test_power power_v1).

Compute (test_power power_v2).

(* ***** *)

Definition test_fac (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 1)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 2)
  &&
  (candidate 3 =n= 6)
  &&
  (candidate 4 =n= 24)
  &&
  (candidate 5 =n= 120)
  &&
  (candidate 6 =n= 720).

Fixpoint fac_v1 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (fac_v1 n')
  end.

Definition fac_v2 (n : nat) : nat :=
  let fix fac n a :=
      match n with
      | O => a
      | S n' => fac n' (a * n)
      end
  in
  fac n 1.

(*
Fixpoint fac_v1 (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mul_v1 n (fac_v1 n')
  end.
 *)

Compute (test_fac fac_v1).
Compute (test_fac fac_v2).

(* ***** *)

Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =n= 0)
  &&
  (candidate 1 =n= 1)
  &&
  (candidate 2 =n= 1)
  &&
  (candidate 3 =n= 2)
  &&
  (candidate 4 =n= 3)
  &&
  (candidate 5 =n= 5)
  &&
  (candidate 6 =n= 8)
  &&
  (candidate 7 =n= 13)
  &&
  (candidate 8 =n= 21)
  &&
  (candidate 9 =n= 34)
  &&
  (candidate 10 =n= 55).

Fixpoint fib_v1 (n : nat) : nat :=
  match n with
  | O => O
  | S n' => match n' with
            | O => 1
            | S n'' => fib_v1 n'' + fib_v1 n'
            end
  end.

Definition fib_v2 (n : nat) : nat :=
  let fix fib n a b :=
      match n with
      | O => a
      | S n' => match n' with
                | O => b
                | _ => fib n' b (a+b)
                end 
      end
  in 
  fib n 0 1. 

Compute (test_fib fib_v1).
Compute (test_fib fib_v2).


(* ***** *)

Definition test_even (candidate: nat -> bool) : bool :=
  (candidate 0)
  &&
  negb (candidate 1)
  &&
  (candidate 2)
  &&
  negb (candidate 3).

Fixpoint even_v1 (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => negb (even_v1 n')
  end.

Definition even_v2 (n : nat) : bool :=
  let fix even n a :=
      match n with
      | 0 => a 
      | S n' => even n' (negb a)
      end
  in
  even n true.  
  
Compute (test_even even_v1).
Compute (test_even even_v2).

(* ***** *)

Definition test_odd (candidate: nat -> bool) : bool :=
  negb (candidate 0)
  &&
  (candidate 1)
  &&
  negb (candidate 2)
  &&
  (candidate 3).

Fixpoint odd_v1 (n : nat) : bool :=
  match n with
  | 0 => false
  | S n' => negb (odd_v1 n')
  end.

Definition odd_v2 (n : nat) : bool :=
  let fix odd n a :=
      match n with
      | 0 => a 
      | S n' => odd n' (negb a)
      end
  in
  odd n false.  

Compute (test_odd odd_v1).
Compute (test_odd odd_v2).

(* Exercise 2 *)

Inductive binary_tree : Type :=
  Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

Fixpoint beq_binary_tree (t1 t2 : binary_tree) : bool :=
  match t1 with
    Leaf n1 =>
    match t2 with
      Leaf n2 =>
      n1 =n= n2
    | Node t21 t22 =>
      false
    end
  | Node t11 t12 =>
    match t2 with
      Leaf n2 =>
      false
    | Node t21 t22 =>
      (beq_binary_tree t11 t21) && (beq_binary_tree t12 t22)
    end
  end.

Notation "A =bt= B" :=
  (beq_binary_tree A B) (at level 70, right associativity).

(* ***** *)

Definition test_number_of_leaves (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))) =n= 4)
  &&
  (candidate (Node (Node (Node (Leaf 1) (Leaf 2)) (Leaf 5)) (Node (Leaf 3) (Leaf 4))) =n= 5).

Fixpoint number_of_leaves_v0 (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    1
  | Node t1 t2 =>
    (number_of_leaves_v0 t1) + (number_of_leaves_v0 t2)
  end.

Compute (test_number_of_leaves number_of_leaves_v0).

(* ***** *)

Definition test_number_of_nodes (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 0)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 1)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))) =n= 3)
  &&
  (candidate (Node (Node (Node (Leaf 1) (Leaf 2)) (Leaf 5)) (Node (Leaf 3) (Leaf 4))) =n= 4).

Fixpoint number_of_nodes_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => 0
  | Node t1 t2 =>
    S (number_of_nodes_v0 t1) + (number_of_nodes_v0 t2)
  end.
      
Compute (test_number_of_nodes number_of_nodes_v0).

(* ***** *)

Definition is_smaller_than (m_init n_init : nat) : bool :=
  let fix visit (m n : nat) : bool :=
      match m with
      | 0 => true
      | S m' => match n with
                | 0 => false
                | S n' => visit m' n'
                end
      end
  in visit m_init n_init.

Definition test_smallest_leaf (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 5) (Leaf 3)) =n= 3)
  &&
  (candidate (Node (Node (Leaf 2) (Leaf 4)) (Leaf 3)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 4) (Leaf 3)) (Node (Leaf 2) (Leaf 1))) =n= 1).

Fixpoint smallest_leaf_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => n
  | Node t1 t2 =>
    match is_smaller_than (smallest_leaf_v0 t1) (smallest_leaf_v0 t2) with
    | true =>
      smallest_leaf_v0 t1
    | false =>
      smallest_leaf_v0 t2
    end
  end.

Compute (test_smallest_leaf smallest_leaf_v0).

(* ***** *)

Definition test_weight (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 3)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =n= 6)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))) =n= 10).

Fixpoint weight_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => n
  | Node t1 t2 =>
    (weight_v0 t1) + (weight_v0 t2)
  end.

Compute (test_weight weight_v0).

(* ***** *)

Definition test_height (candidate: binary_tree -> nat) : bool :=
  (candidate (Leaf 1) =n= 0)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 1)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))) =n= 2).

Fixpoint height_v0 (t : binary_tree) : nat :=
  match t with
  | Leaf n => O
  | Node t1 t2 =>
    match is_smaller_than (height_v0 t1) (height_v0 t2) with
    | true =>
      S (height_v0 t2)
    | false =>
      S (height_v0 t1)
    end
  end.

Compute (test_height height_v0).


(* ***** *)


Definition test_balance (candidate: binary_tree -> bool) : bool :=
  (candidate (Leaf 1))
  &&
  negb (candidate (Node (Leaf 1) (Leaf 2)))
  &&
  negb (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)))
  &&
  negb (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))))
  &&
  negb (candidate (Node (Node (Leaf 2) (Leaf 2)) (Node (Leaf 1) (Leaf 3))))
  &&
  negb (candidate (Node (Node (Leaf 8) (Leaf 2)) (Node (Leaf 5) (Leaf 5))))
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 1)) (Leaf 2)))
  &&
  (candidate (Node (Node (Leaf 3) (Leaf 3)) (Node (Leaf 3) (Leaf 3))))
  &&
  (candidate (Node (Node (Leaf 4) (Leaf 4)) (Node (Leaf 4) (Node (Leaf 2) (Leaf 2)))))
  &&
  (candidate (Node (Leaf 10) (Node (Leaf 5) (Leaf 5)))). 
  

Definition balance_v0 (t : binary_tree) : bool :=
  let fix visit t := 
      match t with
      | Leaf n => (true, n)
      | Node t1 t2 =>
        let (b1, n1) := visit t1 in
        if b1
        then let (b2, n2) := visit t2 in
             if b2
             then match n1 =? n2 with
                  | true => (true, n1+n2)
                  | false => (false, 0) 
                  end
             else (false, 0)
        else (false, 0)
      end
  in
  let (b, n) := visit t in
  b. 
  

Compute (test_balance balance_v0).

Fixpoint balance_v1 (t: binary_tree) : bool :=
  match t with
  | Leaf n => true
  | Node t1 t2 =>
    match (weight_v0 t1) =n= (weight_v0 t2) with
    | true => (balance_v1 t1) && (balance_v1 t2)
    | false => false
    end
  end.

Compute (test_balance balance_v1).


(* ***** *)

Definition test_balance (candidate: binary_tree -> bool) : bool :=
  (candidate (Leaf 1))
  &&
  negb (candidate (Node (Leaf 1) (Leaf 2)))
  &&
  negb (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)))
  &&
  negb (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))))
  &&
  negb (candidate (Node (Node (Leaf 2) (Leaf 2)) (Node (Leaf 1) (Leaf 3))))
  &&
  negb (candidate (Node (Node (Leaf 8) (Leaf 2)) (Node (Leaf 5) (Leaf 5))))
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 1)) (Leaf 2)))
  &&
  (candidate (Node (Node (Leaf 3) (Leaf 3)) (Node (Leaf 3) (Leaf 3))))
  &&
  (candidate (Node (Node (Leaf 4) (Leaf 4)) (Node (Leaf 4) (Node (Leaf 2) (Leaf 2)))))
  &&
  (candidate (Node (Leaf 10) (Node (Leaf 5) (Leaf 5)))). 
  

Definition balance_v0 (t : binary_tree) : bool :=
  let fix visit t := 
      match t with
      | Leaf n => (true, n)
      | Node t1 t2 =>
        let (b1, n1) := visit t1 in
        if b1
        then let (b2, n2) := visit t2 in
             if b2
             then match n1 =? n2 with
                  | true => (true, n1+n2)
                  | false => (false, 0) 
                  end
             else (false, 0)
        else (false, 0)
      end
  in
  let (b, n) := visit t in
  b. 
  

Compute (test_balance balance_v0).

(* ***** *)

Definition test_mirror (candidate: binary_tree -> binary_tree) : bool :=
  (candidate (Leaf 1) =bt= (Leaf 1))
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =bt= (Node (Leaf 2) (Leaf 1)))
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =bt= (Node (Leaf 3) (Node (Leaf 2) (Leaf 1))))
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))) =bt= (Node (Node (Leaf 4) (Leaf 3)) (Node (Leaf 2) (Leaf 1)))).

Fixpoint mirror_v0 (t : binary_tree) : binary_tree :=
  match t with
  | Leaf n => Leaf n
  | Node t1 t2 =>
    Node (mirror_v0 t2) (mirror_v0 t1)
  end.

Compute (test_mirror mirror_v0).

(* Exercise 3 *)

Inductive binary_tree' :=
| Leaf' : binary_tree'
| Node' : binary_tree' -> nat -> binary_tree' -> binary_tree'.

Definition test_number_of_leaves' (candidate: binary_tree' -> nat) : bool :=
  (candidate Leaf' =n= 1)
  &&
  (candidate (Node' (Leaf') 1 (Leaf')) =n= 2)
  &&
  (candidate (Node' (Node' (Leaf') 1 (Leaf')) 2 (Leaf')) =n= 3)
  &&
  (candidate (Node' (Node' (Leaf') 2 (Leaf')) 3 (Node' (Leaf') 1 (Leaf'))) =n= 4)
  .

Fixpoint number_of_leaves' (t : binary_tree') : nat :=
  match t with
    Leaf' =>
    1
  | Node' t1 n t2 =>
    (number_of_leaves' t1) + (number_of_leaves' t2)
  end.

Compute (test_number_of_leaves' number_of_leaves').

(* ***** *)

Definition test_number_of_nodes' (candidate: binary_tree' -> nat) : bool :=
  (candidate Leaf' =n= 0)
  &&
  (candidate (Node' (Leaf') 1 (Leaf')) =n= 1)
  &&
  (candidate (Node' (Node' (Leaf') 1 (Leaf')) 2 (Leaf')) =n= 2)
  &&
  (candidate (Node' (Node' (Leaf') 2 (Leaf')) 3 (Node' (Leaf') 1 (Leaf'))) =n= 3)
  .

Fixpoint number_of_nodes' (t : binary_tree') : nat :=
  match t with
  | Leaf' => 0
  | Node' t1 n t2 =>
    S (number_of_nodes' t1) + (number_of_nodes' t2)
  end.

Compute (test_number_of_nodes' number_of_nodes').

(* Exercise 4 *)

Inductive binary_tree'' :=
| Leaf'' : nat -> binary_tree''
| Node'' : binary_tree'' -> nat -> binary_tree'' -> binary_tree''.

Definition test_number_of_leaves'' (candidate: binary_tree'' -> nat) : bool :=
  (candidate (Leaf'' 1) =n= 1)
  &&
  (candidate (Node'' (Leaf'' 1) 10 (Leaf'' 2)) =n= 2)
  &&
  (candidate (Node'' (Node'' (Leaf'' 1) 10 (Leaf'' 2)) 20 (Leaf'' 3)) =n= 3)
  &&
  (candidate (Node'' (Node'' (Leaf'' 1) 20 (Leaf'' 2)) 30 (Node'' (Leaf'' 3) 10 (Leaf'' 4))) =n= 4)
  .

Fixpoint number_of_leaves'' (t : binary_tree'') : nat :=
  match t with
    Leaf'' n =>
    1
  | Node'' t1 n t2 =>
    (number_of_leaves'' t1) + (number_of_leaves'' t2)
  end.

Compute (test_number_of_leaves'' number_of_leaves'').

(* ***** *)

Definition test_number_of_nodes'' (candidate: binary_tree'' -> nat) : bool :=
  (candidate (Leaf'' 1) =n= 0)
  &&
  (candidate (Node'' (Leaf'' 1) 10 (Leaf'' 2)) =n= 1)
  &&
  (candidate (Node'' (Node'' (Leaf'' 1) 10 (Leaf'' 2)) 20 (Leaf'' 3)) =n= 2)
  &&
  (candidate (Node'' (Node'' (Leaf'' 1) 20 (Leaf'' 2)) 30 (Node'' (Leaf'' 3) 10 (Leaf'' 4))) =n= 3).

Fixpoint number_of_nodes'' (t : binary_tree'') : nat :=
  match t with
  | Leaf'' n => 0
  | Node'' t1 n t2 =>
    S (number_of_nodes'' t1) + (number_of_nodes'' t2)
  end.

Compute (test_number_of_nodes'' number_of_nodes'').

(* end of week-01_functional-programming-in-Coq.v *)
