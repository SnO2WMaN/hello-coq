Section Nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Fixpoint plus (n : nat) (m : nat) :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Compute plus (S (S (S O))) (S (S O)).
Compute plus (S (S (S O))) O.
Notation "x + y" := (plus x y)
  (at level 50, left associativity): nat_scope.
Check ((0 + 1) + 1).

Fixpoint mult (n : nat) (m : nat) :=
  match n with
    | O => O
    | S n' => m + (mult n' m)
  end.
Compute mult 4 2.

Fixpoint eqb (n m : nat) :=
  match n with
  | O =>
    match m with
      | O => true
      | S m' => false
      end
  | S n' =>
    match m with
      | O => false
      | S m' => eqb n' m'
      end
  end.
Notation "x =? y" := (eqb x y)
  (at level 50, left associativity): nat_scope.

Fixpoint leb (n m : nat) :=
  match n with
  | O => true
  | S n' =>
    match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x <=? y" := (leb x y)
  (at level 50, left associativity): nat_scope.

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_n_0 : forall n:nat, n + 0 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem plus_id : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_transitive: forall n m: nat, n + m = m + n.
Proof.
  induction m as [|m' ihm].
  - apply plus_n_0.
  - give_up.
Admitted.

Theorem mult_0_n : forall n : nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_n_0 : forall n : nat, n * 0 = 0.
Proof.
  induction n as  [| n' IH].
  - reflexivity.
  - simpl.
    apply IH.
Qed.

Theorem mult_n_0_m_0 : forall n m : nat,
  (n * 0) + (m * 0) = 0.
Proof.
    intros n m.
    rewrite (mult_n_0 n).
    rewrite (mult_n_0 m).
    reflexivity.
Qed.

Theorem plus_q_neq_0_firsttry: forall n:nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'].
    - reflexivity.
    - reflexivity.
Qed.

End Nat.
