Set Implicit Arguments.
Require Import Omega.


Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : B) : B :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : B) : B :=
match x with
  | O => I
  | I => O
end.

Goal forall (X Y : B), Or (Or (Not (And X Y)) (And (Not X) Y)) (And (Not X) (Not Y)) = 
 Not (And X Y).
Proof.
 intros X Y. destruct X, Y; simpl; reflexivity.
Qed.

Goal forall (X Y Z : B),
 And (And (Not (And (And (Not X) Y) (Not Z))) (Not (And (And (X) (Y)) (Z) ))) (And (And X (Not Y)) (Not Z))
 = And (Not (Or Z Y)) X.
Proof.
 intros X Y Z. destruct X, Y, Z; simpl; reflexivity.
Qed.