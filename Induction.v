From LF Require Export Basics.
Require Import Coq.Init.Datatypes.

Theorem add_r_0_firsttry: forall n : nat,
    n+0 = n.
Proof. intros n. induction n .
       - reflexivity.
       - simpl. rewrite IHn . reflexivity.
      Qed.

Theorem add_r_0_secondtry : forall n : nat,
    n+0 = n.
Proof. intros n. induction n as [|n' Ihn'].
       -  reflexivity.
       - simpl. rewrite Ihn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
    minus n n = 0.
Proof. intros n. induction n as [|n' Ihn'].
       - reflexivity.
       - simpl. rewrite Ihn'. reflexivity.
Qed.

Theorem mul_0_r : forall n : nat,
    n * 0 = 0.
Proof. induction n as [|n' Ihn'].
       - reflexivity.
       - simpl. rewrite Ihn'. reflexivity.
Qed.
Theorem succ_add : forall n m : nat,
    S (n + m) = n + S (m).
Proof. induction n as [|n' Ihn'].
       - reflexivity.
       - simpl. intros m. rewrite Ihn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    n + m = m + n.
Proof. induction n as [|n' Ihn'].
       - simpl. intros m. rewrite add_r_0_secondtry. reflexivity.
       - simpl. intros m. rewrite Ihn'. rewrite succ_add. reflexivity.
Qed.

Theorem add_comm : forall n m p : nat,
    n + (m + p) = (n + m ) + p.
Proof. induction p as [|p' Ihp'].
       - rewrite add_r_0_secondtry. rewrite add_r_0_secondtry. reflexivity.
       - rewrite <- succ_add. rewrite <- succ_add. rewrite <- succ_add. rewrite Ihp'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
    |  O => O
    | S n' => S (S (double n'))
end.

Lemma double_plus : forall n, double n = n + n.
  Proof. induction n as [| n' Ihn'].
         - reflexivity.
         - simpl. rewrite <- succ_add. rewrite Ihn'. reflexivity.
Qed.
