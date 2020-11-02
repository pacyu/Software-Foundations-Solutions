Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n.
  - simpl.
    induction m.
    + simpl. reflexivity.
    + simpl. rewrite <- IHm. reflexivity.
  - simpl.
    induction m.
    + simpl. rewrite <- plus_n_O. reflexivity.
    + simpl. rewrite <- plus_n_Sm. rewrite IHm. reflexivity.
Qed.
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n.
  - simpl. reflexivity.
  - { induction m.
      + simpl.
        rewrite <- plus_n_O.
        reflexivity.
      + { induction p.
          - rewrite <- plus_n_O.
            rewrite <- plus_n_O.
            reflexivity.
          - rewrite <- plus_n_Sm.
            rewrite <- plus_n_Sm.
            rewrite <- plus_n_Sm.
            rewrite IHp.
            reflexivity. } }
Qed. 
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  rewrite plus_assoc. rewrite H. rewrite plus_assoc. reflexivity.
Qed.
Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  