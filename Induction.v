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
Theorem add_comm: forall n m : nat,
    n + m = m + n.
Proof.
  induction m as [|m' Ihm'].
  - rewrite add_r_0_firsttry. simpl. reflexivity.
  - simpl. rewrite <- succ_add. rewrite Ihm'. reflexivity.
Qed.
Theorem add_assoc : forall n m p : nat,
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

Theorem even_S : forall n :nat,
    even (S n) = Basics.negb (even n).
Proof. induction n as [|n' Ihn'].
       - simpl. reflexivity.
       - rewrite Ihn'. simpl. rewrite negation_fn_applied_twice.  reflexivity. intros x. reflexivity.
Qed.

(* Proof within proofs *)

Theorem mult_0_plus' : forall n m : nat,
    (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { rewrite add_r_0_secondtry. rewrite add_r_0_firsttry. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry: forall n m p q: nat,
    (n+m) + (p+q) = (m +n ) + (p+q).
Proof. intros n m p q.
       assert (H: n+m = m+n).
       { rewrite add_comm. reflexivity. }
       rewrite H. reflexivity.
Qed.

(* formal vs. informal proofs *)
(* informal proofs are algorithms
 Formal proofs are code*)

Theorem leb_refl : forall n : nat,
    (n <=? n) = Basics.true.
Proof. induction n as [| n' Ihn'].
       - simpl. reflexivity.
       - simpl. rewrite Ihn'. reflexivity.
Qed.
Theorem zero_neqb_S : forall n:nat,
    O =? (S n) = Basics.false.
Proof.  simpl. reflexivity.
 Qed.

Theorem andb_false_r : forall b : Basics.bool,
    Basics.andb b Basics.false = Basics.false.
Proof.
intros b. destruct b.
 - simpl.  reflexivity.
 - simpl.  reflexivity.
Qed.

Theorem S_negb_0 : forall n : nat,
    (S n) =? 0 = Basics.false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_1 : forall n:nat, 1 * n = n.
Proof. intros. simpl. rewrite add_r_0_firsttry. reflexivity.
Qed.
Theorem a113_spec : forall b c : Basics.bool,
    Basics.orb ( Basics.andb b c )
        (Basics.orb (Basics.negb b)
        (Basics.negb c)) = Basics.true.
Proof. intros b c. destruct b.
       - simpl. destruct c.
         + simpl. reflexivity.
         + simpl. reflexivity.
       - simpl. reflexivity.
Qed.
Theorem mult_plus_distr_r : forall n m p : nat,
    (n+m) * p = (n*p) + (m*p).
Proof. induction n as [| n' Ihn'].
       - simpl. reflexivity.
       - simpl. intros m p. rewrite Ihn'. rewrite add_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m ) * p.
Proof. induction n as [| n' Ihn'].
       - simpl. reflexivity.
       - simpl. intros m p . rewrite Ihn'. rewrite mult_plus_distr_r. reflexivity.
Qed.



Check incr  z.
Check bin_to_nat(z).
Compute incr z.
Compute bin_to_nat(B1 z).
Theorem bin_to_nat_pres_incr: forall b : bin,
    bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  induction b as [ | b1' Ihb1' | b2' Ihb2' ].
  - simpl. reflexivity.
  - simpl. rewrite <- succ_add. rewrite add_r_0_firsttry. reflexivity.
  - simpl. rewrite succ_add. rewrite Ihb2'. rewrite mult_plus_distr_r. simpl. rewrite <- succ_add. rewrite <- succ_add. rewrite add_r_0_firsttry. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : Basics.bin :=
  match n with
    | O => z
    | S n' => incr (nat_to_bin n')
end.

Compute nat_to_bin (S O).
Lemma atimes_n: forall a n: nat, a * n + n = ( a + 1 )*n.
Proof. intros a n. rewrite  mult_plus_distr_r. rewrite mult_1_1. reflexivity.
Qed.
Lemma succ_nat_incr_bin : forall b : Basics.bin,
   bin_to_nat ( incr b ) = S (bin_to_nat b ).
Proof. intro b. induction b as [| b1' Ihb1 | b2' Ihb2'].
       - simpl. reflexivity.
       - simpl. rewrite <- succ_add. rewrite add_r_0_firsttry. reflexivity.
       - simpl. rewrite succ_add. rewrite Ihb2'. rewrite  <- succ_add. rewrite succ_add.
             rewrite atimes_n.  rewrite <- succ_add. rewrite add_r_0_firsttry. reflexivity.
Qed.
Lemma incr_bin_succ_nat : forall n : nat,
    nat_to_bin (S n) = incr  (nat_to_bin n).
Proof. induction n as [|n' Ihn'].
      - simpl. reflexivity.
      - simpl. rewrite <- Ihn'. reflexivity.
Qed.
Theorem nat_bin_nat : forall n: nat, (bin_to_nat(nat_to_bin   n) )= n.
Proof. induction n as [| n' Ihn'].
       - simpl. reflexivity.
       - simpl. rewrite succ_nat_incr_bin. rewrite Ihn'. reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S ( S (double n) ).

Proof. simpl. reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
  match b with
      | z => z
      | _ =>  B0 b
  end.


Example double_bin_zero : double_bin z = z.
Proof. simpl. reflexivity.
Qed.
Lemma double_incr_bin : forall b:bin,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof. induction b as [| b0' Ihb0' | b1' Ihb1'].
       -  simpl. reflexivity.
       - simpl. reflexivity.
       - simpl. reflexivity.
Qed.

Theorem bin_nat_bin_fails: forall b, nat_to_bin (bin_to_nat b) = b.
Proof. Abort.

Fixpoint normalize (b: bin) : bin :=
  match b with
    | z => z
    | B1 b' => B1 (normalize b')
    | B0  b' => match (normalize b') with
                | z => z
                | bi => B0 bi
              end
    end.

Example normalize_000: normalize (B0(B0(z))) = z.
Proof. simpl. reflexivity. Qed.
Lemma double_mul_2 : forall n: nat,
    double n = n * 2.
Proof. induction  n as [|n' Ihn'].
       - simpl. reflexivity.
       - simpl. rewrite Ihn'. reflexivity.
Qed.
Lemma add_twice_double: forall n:nat,
    n + n = double n.
Proof. induction n as [|n' Ihn'].
       - simpl.  reflexivity.
       - rewrite <- succ_add. rewrite add_comm. rewrite <- succ_add. rewrite Ihn'. rewrite  double_incr. reflexivity.
Qed.
Lemma bin_to_nat_B0: forall b: bin,
    bin_to_nat (B0 b) = double (bin_to_nat (b)).
Proof. simpl. induction b as [| b1' Ihb1' | b2' Ihb2'].
       - simpl. reflexivity.
       - simpl. simpl add_assoc. rewrite Ihb1'. rewrite <- double_mul_2. reflexivity.
       - simpl. rewrite <- double_mul_2. reflexivity.
Qed.
Lemma double_to_double_bin: forall n: nat,
    nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof. induction n as [|n' Ihn'].
       - simpl. reflexivity.
       - rewrite double_incr. simpl. rewrite Ihn'. rewrite double_incr_bin. reflexivity.
Qed.

Lemma double_to_double_bin_incr : forall n : nat,
    nat_to_bin(double n + 1) = incr (double_bin (nat_to_bin n)).
Proof. induction n as [|n' Ihn'].
       - simpl. reflexivity.
       - rewrite incr_bin_succ_nat. rewrite double_incr_bin. simpl. rewrite <- Ihn'. reflexivity.
Qed.

Lemma incr_double_bin_B1: forall b: bin,
    incr (double_bin b) = B1 b.
Proof. intro b. induction b as [|b1 Ihb1 | b2 Ihb2].
       - simpl. reflexivity.
       - simpl.  reflexivity.
       - simpl. reflexivity.
Qed.

  Theorem bin_nat_bin : forall b , nat_to_bin (bin_to_nat b) = normalize b.

Proof. induction b as [| b1' Ihb1' | b2' Ihb2'].
       - simpl. reflexivity.
       - simpl. rewrite <- double_mul_2. rewrite double_to_double_bin. rewrite Ihb1'.
        destruct (normalize b1').
        {
          - simpl. reflexivity.
        }
        {
          - simpl. reflexivity.
        }
        {
          - simpl. reflexivity.
        }
      - simpl. rewrite <- double_mul_2 . rewrite double_to_double_bin_incr. rewrite Ihb2'. rewrite incr_double_bin_B1. reflexivity.
Qed.
