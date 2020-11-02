Check leb.
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  (* FILL IN HERE *) Admitted.
Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.
Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true → (p + n) <=? (p + m) = true.
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