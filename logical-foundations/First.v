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
Proof. simpl. reflexivity. Qed.