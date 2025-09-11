From LF Require Export Induction.

Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check 3.
Check S (S ( S O )).

Check (pair 3 5): natprod.


Definition fst (p: natprod) : nat :=
  match p with
    | pair x _ => x
  end.


Definition snd (p: natprod) : Datatypes.nat :=
  match p with
    | pair _ x => x
  end.

Compute (fst (pair 3 5)).

Notation "( x , y  )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p:natprod): Datatypes.nat :=
  match p with
    | (x,y) => x
  end.
Definition snd' (p:natprod): Datatypes.nat :=
  match p with
    | (x,y) => y
  end.

Definition swap_pair (p:natprod):natprod :=
  match p with
    | (x,y) => (y,x)
  end.

 Theorem surjective_pairing' : forall (n m : Datatypes.nat),
     (n,m) = (fst (n,m) , snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p: natprod),
    p = (fst p, snd p).
Proof. simpl.
       Abort.

Theorem surjective_pairing : forall (p: natprod),
    p = (fst p, snd p).
Proof. intros p. destruct p as [n m]. simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p)  = swap_pair p.

Proof. intros.  destruct p. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p:natprod),
    fst (swap_pair p) = snd p.
Proof. intros p. destruct p. simpl. reflexivity. Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                      (at level 60, right associativity).
(*atlevel 60 tells Coq how to parenthesize expressions that involve both :: and some other infix operator*)
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist1 := 1 :: (2 :: ( 3 :: nil )).
Definition mylist3 := [1;2;3].
Check O.
Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.
