From LF Require Export Induction.

Module NatList.

Inductive natprod : Type :=
| pair (n1 n2 : Datatypes.nat).


Check (pair 3 5): natprod.


Definition fst (p: natprod) : Datatypes.nat :=
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
