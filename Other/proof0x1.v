Inductive N : Type :=
  | O : N
  | S : N -> N.

Fixpoint plus (n m : N) :=
  match n with
  | O => m
  | S n' => S (n' + m)
  end
  where "n' + m" := (plus n' m).

Lemma plus_n_O (n : N) : n + O = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_n_Sm (n m : N) : n + (S m) = S (n + m).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma plus_comm (n m : N) : n + m = m + n.
Proof.
  induction n.
  - simpl. rewrite plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma plus_n_m_x (n m x : N): n + (m + x) = n + m + x.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint mult (n m : N) :=
  match n with
  | O => O
  | S n' => m + (n' * m)
  end
  where "n' * m" := (mult n' m).

Lemma mult_n_O (n : N) : n * O = O.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma mult_n_Sm (n m : N) : n * (S m) = n * m + n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_m_x. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma mult_comm (n m : N) : n * m = m * n.
Proof.
  induction n.
  - simpl. rewrite mult_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite mult_n_Sm. rewrite plus_comm. reflexivity.
Qed.

Definition e : N := S O.

Lemma mult_n_e (n : N) : n * e = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mult_unitary_comm : forall n : N, e * n = n.
Proof.
  intro n.
  rewrite mult_comm.
  rewrite mult_n_e.
  reflexivity.
Qed.
