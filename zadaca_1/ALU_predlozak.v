Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Omega.

(* Bit *)

Inductive B : Type :=
  | O : B
  | I : B.

(* Osnovne logicke operacije *)

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

(* Osnovne aritmeticke operacije *)

Definition Add (x y c : B) : B :=
  match x, y with
    | O, O => c
    | I, I => c
    | _, _ => Not c
  end.

Definition Car (x y c : B) : B :=
  match x, y with
    | O, O => O
    | I, I => I
    | _, _ => c
  end.

(* Bit list - aritmeticke i logicke operacije *)

Fixpoint AndL (x y : list B) : list B :=
  match x, y with
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => And x y :: AndL xs ys
  end.

Fixpoint OrL (x y : list B) : list B :=
  match x, y with
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => Or x y :: OrL xs ys
  end.

Fixpoint NotL (x : list B) : list B :=
  match x with
    | [] => []
    | x :: xs => Not x :: NotL xs
  end.

Fixpoint AddLr (x y : list B) (c : B) : list B :=
  match x, y with
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => Add x y c :: AddLr xs ys (Car x y c)
  end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

Fixpoint IncLr (x : list B) (c : B) : list B :=
  match x with
    | [] => []
    | x :: xs => Add x I c :: IncLr xs (Car x I c)
  end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* ALU *)

Definition flag_z (f : B) (x : list B) : list B :=
 match f with
 | I => repeat O (length x)
 | O => x
 end.

Definition flag_n (f : B) (x : list B) : list B :=
 match f with
 | I => NotL x
 | O => x
 end.

Definition flag_f (f : B) (x y : list B) : list B :=
 match f with
 | I => AddL x y
 | O => AndL x y
 end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B :=
 flag_n no (flag_f f (flag_n nx (flag_z zx x)) (flag_n ny (flag_z zy y))).

(* Teoremi *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof.
 intros H. simpl. rewrite H.
 assert (P : forall (n:nat), AddL (repeat O n) (repeat O n) = repeat O n).
 { intros n. unfold AddL.
   assert (P2 : forall (b:B) (m:nat), repeat b m ++ [b] = b :: repeat b m).
    { intros bb mm. induction mm.
      - simpl. reflexivity.
      - simpl. rewrite IHmm. reflexivity. }
   assert (P1 : forall (b:B) (n:nat), rev (repeat b n) = repeat b n).
   { intros b m. induction m.
     - reflexivity.
     - simpl.
     rewrite IHm. rewrite P2. reflexivity. }
   rewrite P1. induction n.
   - simpl. reflexivity.
   - simpl. rewrite IHn. rewrite P2. reflexivity. }
  rewrite P. reflexivity.
Qed.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof. Abort.

Lemma ALU_x (x y : list B) :
  length x = length y -> ALU x y O O I I O O = x.
Proof. Abort.

Lemma ALU_y (x y : list B) :
  length x = length y -> ALU x y I I O O O O = y.
Proof. Abort.

Lemma ALU_Not_x (x y : list B) :
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. Abort.

Lemma ALU_Not_y (x y : list B) :
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. Abort.

Lemma ALU_Add (x y : list B) :
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. Abort.

Lemma ALU_And (x y : list B) :
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof.
 intros H. simpl. reflexivity.
Qed.

Lemma ALU_Or (x y : list B) :
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof.
 intros H. simpl.
Abort.

Lemma ALU_one (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
 intros [A1 [A2 A3]]. simpl.
Abort.







