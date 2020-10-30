Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + S m.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    induction m.
    + rewrite IHn. reflexivity.
    + rewrite IHn. reflexivity.
Qed.
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