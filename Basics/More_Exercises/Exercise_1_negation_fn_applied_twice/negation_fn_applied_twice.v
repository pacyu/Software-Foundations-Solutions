Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H.
  destruct b eqn: Eb.
  - rewrite H. rewrite H. simpl. reflexivity.
  - rewrite H. rewrite H. simpl. reflexivity.
Qed. 
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.