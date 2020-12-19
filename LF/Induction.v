From LF Require Export Basics.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

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

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' En'].
  - simpl. reflexivity.
  - rewrite En'. simpl. rewrite negb_involutive. reflexivity.
Qed.

Definition manual_grade_for_destruct_induction : option (nat×string) := None.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem: Addition is commutative.
Proof:
  Definition manual_grade_for_plus_comm_informal : option (nat×string) := None.
Qed.

Theorem: true = n =? n for any n.
Proof: By induction on n.
    + First, suppose n = 0. We must show that
        0 =? 0 is true.
      This follows directly from the reflexivity.
    + Next, suppose n = S n'. We must show that
        S n' = S n'.
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
  induction m as [| m'].
  - induction n as [|n'].
    + reflexivity.
    + simpl. rewrite <- IHn'. simpl. reflexivity.
  - induction n as [|n'].
    + simpl. rewrite IHm'. simpl. reflexivity.
    + simpl. rewrite IHm'. rewrite <- IHn'.
      simpl. rewrite IHm'. rewrite plus_swap. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intro n.
  assert (H: n <= n).
  { reflexivity. }
  
Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem mult_1_l : forall n:nat, 1 × n = n.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) × p = (n × p) + (m × p).
Proof.
  (* FILL IN HERE *) Admitted.
Theorem mult_assoc : forall n m p : nat,
  n × (m × p) = (n × m) × p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.