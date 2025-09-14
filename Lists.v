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

Fixpoint length (l:natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.


Fixpoint app (l1 l2 : natlist): natlist :=
    match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Example test_appl: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. simpl. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l: natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.


Definition tl  (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_t1 : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | 0 :: l' => nonzeros l'
    | ll :: l' =>  ll:: (nonzeros l')
  end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | nil => nil
    | ll :: l' =>  if (odd ll)  then ll:: (oddmembers l') else (oddmembers l')
  end.
Example test_oddmembers:
  oddmembers [ 0;1;0;2;3;0;0 ] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | _,nil => l1
    | nil, _ => l2
    | (l'::ll'),(l''::ll'') => l'::l'':: (alternate ll' ll'')
  end.

Example test_alternate1 :
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2 :
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3 :
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4 :
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v :nat ) (s: bag) : nat :=
  match s with
    | nil => O
    | l:: ll => if (eqb l v) then S (count v ll) else count v ll
  end.
Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2 : count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum  (l1 l2 : bag) : bag :=
  alternate l1 l2 .
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s : bag) : bag:=
  v :: s .

Example test_add1 : count 1 (add 1 [1;4;1])  = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2 : count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v:nat) (s:bag) : bool :=
  match s with
    | nil => false
    | l::ll => if (eqb l v) then true else member v ll
  end.


Example test_member1 : member 1 [1;4;1]  = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | l :: ll => if (eqb l v) then ll else l:: (remove_one v ll)
  end.

Example test_remove_one1 :
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4])= 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2:bag) bool :=
