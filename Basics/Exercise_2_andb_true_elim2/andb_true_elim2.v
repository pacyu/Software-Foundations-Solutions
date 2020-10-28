Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros b c. destruct b eqn: Eb.
    - destruct c eqn: Ec.
        + simpl. reflexivity.
        + intro H. rewrite <- H. simpl. reflexivity.
    - destruct c eqn: Ec.
        + intro H. rewrite <- H. simpl. reflexivity.
        + intro H. rewrite <- H. simpl. reflexivity.
Qed.  