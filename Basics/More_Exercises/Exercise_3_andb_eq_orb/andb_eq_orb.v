Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b eqn: Eb.
  - destruct c eqn: Ec.
    + simpl. reflexivity.
    + simpl. rewrite <- Ec. rewrite <- Eb. intro H. rewrite -> H. reflexivity.
  - destruct c eqn: Ec.
    + simpl. rewrite <- Ec. rewrite <- Eb. intro H. rewrite -> H. reflexivity.
    + simpl. reflexivity.
Qed.