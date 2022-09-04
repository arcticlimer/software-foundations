Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(* Grading Scripts use it *)
From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.

(* if we don't add a Proof block for each example, then these
are handled by coq as "nested proofs" *)
Example negate_true: negb true = false.
Proof. simpl. reflexivity. Qed.
Example negate_false: negb false = true.
(* Proof block can also be written like this *)
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true    
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Conditional expressions *)
Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

Definition nandb (b1:bool) (b2:bool) : bool :=
  negb (andb b1 b2).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := 
  andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(* Modules can be defined and they have their own scope *)
Module Playground.
  Definition b : rgb := blue.
End Playground.
(* This does not clashes with Playground.b *)
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.

(* Tuples *)
Module TuplePlayground.
  Inductive bit : Type :=
    | B0
    | B1.
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  Check (bits B1 B0 B1 B0) : nybble.
  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
  Example all_zero1: (all_zero (bits B1 B0 B1 B0)) = false.
  Proof. simpl. reflexivity. Qed.
  Example all_zero2: (all_zero (bits B0 B0 B0 B0)) = true.
  Proof. simpl. reflexivity. Qed.
End TuplePlayground.

Module NatPlayground.
  (* We are using church notation inside this module, 
     but we can use number literals in global scope 
     and Coq will convert them to church notation for us. *)
  Inductive nat : Type :=
    | O
    | S (n : nat).

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  Example pred1: (pred (S (S O))) = (S O).
  Proof. simpl. reflexivity. Qed.

  (* Recursive functions are defined using "Fixpoint" *)
  Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end. 

  Definition odd (n:nat) : bool :=
    negb (even n).
  Example test_odd1: odd (S O) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_odd2: odd (S (S (S (S O)))) = false.
  Proof. simpl. reflexivity. Qed.
End NatPlayground.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  Example test_mult1: mult 2 3 = 6.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'
    end.
  Example test_minus1: minus 2 3 = 0.
  Proof. simpl. reflexivity. Qed.
  Example test_minus2: minus 5 3 = 2.
  Proof. simpl. reflexivity. Qed.

  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
  Example test_exp1: exp 2 8 = 256.
  Proof. simpl. reflexivity. Qed.

  Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S O => n
    | S n' => mult n (factorial n')
    end.
  Example test_factorial1: (factorial 3) = 6.
  Proof. simpl. reflexivity. Qed.
  Example test_factorial2: (factorial 5) = (mult 10 12).
  Proof. simpl. reflexivity. Qed.
End NatPlayground2.

