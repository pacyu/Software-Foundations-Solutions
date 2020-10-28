Inductive N : Type :=
| O : N
| S : N -> N.


Fixpoint plus (x y : N) : N :=
  match x with
  | O => y
  | S x' => S (plus x' y)
  end.


Fixpoint mult (x y : N) : N :=
  match x with
  | O => O
  | S x' => plus y (mult x' y)
  end.

(* Fixpoint minus (x y : N) : N :=
  match x with
  | *)

Lemma plus_x_O (x : N) : plus x O = x.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_x_Sy (x y : N) : plus x (S y) = S (plus x y).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma mult_x_O (x : N) : mult x O = O.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_comm (x y : N) : plus x y = plus y x.
Proof.
  induction x.
  - simpl. rewrite plus_x_O. reflexivity.
  - simpl. rewrite IHx. rewrite plus_x_Sy. reflexivity.
Qed.

Lemma plus_asso (x y b : N) : plus x (plus y b) = plus (plus x y) b.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma plus_asso_l (x y b : N) : plus x (plus y b) = plus y (plus x b).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. rewrite plus_x_Sy. reflexivity.
Qed.

Lemma mult_x_Sy (x y : N) : mult x (S y) = plus x (mult x y).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. rewrite plus_asso_l. reflexivity.
Qed.

Lemma mult_comm (x y : N) : mult x y = mult y x.
Proof.
  induction x.
  - simpl. rewrite mult_x_O. reflexivity.
  - simpl. rewrite mult_x_Sy. rewrite IHx. reflexivity.
Qed.

Lemma mult_right_unitary : forall n : N, mult n (S O) = n.
Proof.
  induction n.
  + simpl. reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

Lemma mult_left_unitary : forall n : N, mult (S O) n = n.
Proof.
  intro n.
  rewrite mult_comm.
  rewrite mult_right_unitary.
  reflexivity.
Qed.
