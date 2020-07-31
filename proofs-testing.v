Require Import Arith.

Theorem AdditiveAssociativity : forall n m k : nat, n + (m + k) = (n + m) + k.
Proof.
  intros n m k.
  induction n.
  simpl. reflexivity.
  simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem AdditiveCommutativity : forall n m : nat, n + m = m + n.
Proof.
  induction n. induction m. reflexivity.
  simpl. rewrite <- IHm. simpl. reflexivity.
  simpl. induction m. rewrite -> IHn. simpl. reflexivity.
  simpl. rewrite -> IHn. simpl. rewrite <- IHm. rewrite IHn. reflexivity.
Qed.

Theorem IdAdd : forall n : nat, n + 0 = n.
Proof.
  intros n. rewrite AdditiveCommutativity. simpl. reflexivity.
Qed.


Lemma l0 : forall n m : nat, n + m = n -> m = 0.
Proof.
  induction n. simpl. trivial. simpl. auto.
  Qed.



Lemma l2 : forall n m k : nat, n + m + k = n + (m + k).
Proof.
  intros n m k.
  rewrite AdditiveAssociativity. reflexivity.
Qed.

Lemma l3 : forall n m k j : nat, n + m + k + j = n + (m + k) + j.
Proof.
  intros n m j k.
  rewrite AdditiveAssociativity. reflexivity.
Qed.




Theorem Distributive : forall n m k : nat, n * (m + k) = n * m + n * k.
Proof.
  intros n m k.
  induction n. simpl. reflexivity.
  simpl. rewrite -> IHn. simpl. rewrite AdditiveAssociativity. rewrite AdditiveAssociativity.
  rewrite l3. rewrite l3. rewrite (AdditiveCommutativity k (n*m)).
  rewrite AdditiveAssociativity. reflexivity.
Qed.

Theorem MultiplicativeCommutativity : forall n m : nat, n * m = m * n.
Proof.
  induction n.
  induction m. reflexivity. simpl. rewrite <- IHm. simpl. reflexivity.
  induction m. simpl. rewrite IHn. simpl. reflexivity.
  simpl. rewrite <- IHm. simpl. rewrite IHn. simpl. rewrite AdditiveAssociativity.
  rewrite AdditiveAssociativity. rewrite IHn. rewrite (AdditiveCommutativity m n).
  reflexivity.
Qed.



Theorem LeftCancelAddFwd : forall n m k : nat, n + m = n + k -> m = k.
Proof.
  intros n m k.
  induction n. simpl. trivial. auto.
Qed.

Theorem LeftCancelAddBack : forall n m k : nat, m = k -> n + m = n + k.
Proof.
  intros n m k.
  induction n. simpl. trivial. simpl. auto.
Qed.

Theorem LeftCancelAdd : forall n m k : nat, m = k <-> n + m = n + k.
Proof.
  split.
  induction n. simpl. trivial. simpl. auto.
  induction n. simpl. trivial. auto.
Qed.



Theorem MultiplicativeAssociativity : forall n m k : nat, n * (m * k) = (n *m ) * k.
Proof.
  intros n m k.
  induction n. simpl. reflexivity.
  simpl. rewrite -> IHn. rewrite (MultiplicativeCommutativity (m + n*m) k).
  rewrite Distributive. rewrite <- IHn.
  rewrite (MultiplicativeCommutativity m k). rewrite <- LeftCancelAdd.
  rewrite (MultiplicativeCommutativity k m). rewrite IHn. rewrite MultiplicativeCommutativity.
  reflexivity.
Qed.
