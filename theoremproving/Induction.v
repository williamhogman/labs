From LF Require Export Basics.

Theorem plus_n_O : forall n: nat, n = n + 0.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
  induction n. reflexivity.
  simpl. assumption.
Qed.


Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
  induction n.
  - trivial.
  - simpl. assumption.
Qed.

Theorem plus_n_Sm: forall n m: nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,  double n = n + n.
  induction n.
  - simpl. trivial.
  - simpl. rewrite -> IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.


Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n.
  - trivial.
  - rewrite -> IHn.  simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
                         rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  assert (H: n + m = m + n). { rewrite plus_comm. reflexivity. }.
  rewrite H.
  rewrite plus_assoc.
  reflexivity. Qed.

Theorem mult_n_0 : forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n. trivial. simpl. assumption.
Qed.

Theorem mult_n_Sm: forall n m : nat,
  n * S m = n + n * m.
Proof.
  intros n m.
  induction n.
  - rewrite <- mult_n_Sm. trivial.
  - simpl. rewrite -> IHn. rewrite plus_swap. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction m.
  - simpl. rewrite -> mult_n_0. trivial.
  - simpl. rewrite -> mult_n_Sm. rewrite IHm. trivial.
Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n.
  induction n as [|n' IHn].
  - (* n = 0 *)
    reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p.
  - trivial.
  - simpl. assumption.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [][].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  - (* n = 0 *) reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - (* n = 0 *) reflexivity.
  - (* n = S n' *)
    simpl.
    rewrite -> IHn.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  induction n.
  trivial.
  simpl. assumption.
Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  replace (n + m) with (m + n).
  rewrite plus_assoc.
  reflexivity.
  rewrite plus_comm.
  reflexivity.
Qed.
