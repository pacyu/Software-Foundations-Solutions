Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' En'].
  - simpl. reflexivity.
  - rewrite En'. simpl.
    induction n' as [|n'' En''].
    { simpl. reflexivity. }
    { rewrite <- En'. rewrite IHn'. } 