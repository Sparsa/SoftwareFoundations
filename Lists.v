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
    | l:: ll => match (eqb l v) with
                 | true =>  S (count v ll)
                 | false => count v ll
              end
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

Fixpoint remove_all (v: nat)   (s:bag) : bag  :=
  match s with
    | nil => nil
    | l :: ll => if (eqb v l) then (remove_all v ll) else l:: (remove_all v  ll)
 end.

Example test_remove_all1:
  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl.  reflexivity. Qed.

Example test_remove_all2:
  count 5 (remove_all 5 [2;1;4;1])= 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3:
  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4:
  count 5 (remove_all 5 [ 2;1;5;4;5;1;4;5;1;4 ]) = 0.
Proof. simpl. reflexivity. Qed.


Fixpoint included (s1:bag) (s2:bag): bool:=
  match s1 with
    | nil => true
    | l :: ll => if (member l s2) then (included ll (remove_one l s2)) else false
 end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_included2 : included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Lemma eqb_refl : forall n : nat ,
    (eqb n n )  = true.
Proof. induction n as [|n' ihn'].
       - simpl. reflexivity.
       - simpl. rewrite ihn'. reflexivity.
Qed.


Theorem add_inc_count: forall n: nat, forall l : bag,
    count n (add n l) = S (count n l).
Proof. intros n l. simpl. rewrite eqb_refl. reflexivity.
       Qed.


Definition manual_grade_for_add_inc_count : option (nat * string) := None.

Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - reflexivity.
  - reflexivity. Qed.

Theorem app_asoc: forall l1 l2 l3 : natlist,
    (l1 ++ l2 ) ++ l3  = l1 ++ (l2 ++ l3).
Proof. intros l1 l2 l3. induction l1 as [| n l1' Ihl1'].
       - simpl. reflexivity.
       - simpl. rewrite Ihl1'. reflexivity.
Qed.

Theorem repeat_plus : forall c1 c2 n : nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof. intros c1 c2 n.
       induction c1 as [|c1' Ihc1'].
       - simpl.  reflexivity.
       - simpl.
         rewrite <- Ihc1'.
         reflexivity.
      Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => rev t ++ [h]
  end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2 : rev nil = nil.
Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
Proof. intros l.
       induction l as [| n l' Ihl'].
       - reflexivity.
       - simpl. rewrite <- Ihl'. Abort.

Theorem app_length_S: forall l n,
    length (l++ [n]) = S (length l).
Proof. intros l n.
       induction l as [| n' l' Ihl'].
       - simpl. reflexivity.
       - simpl. rewrite <- Ihl'. reflexivity.
Qed.


Theorem ref_length : forall l : natlist,
    length (rev l) = length l.

Proof. intros l. induction l as [| n' l' Ihl'].
       -  simpl. reflexivity.
       - simpl. rewrite -> app_length_S. rewrite -> Ihl'. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n' l' Ihl'].
  - simpl. reflexivity.
  - simpl. rewrite <- Ihl'. reflexivity. Qed.

Search rev.
Search (_ + _ = _ + _).
Search (_ = _) .
Search (_ + _ = _ + _) inside Induction.
Search (?x + ?y = ?y + ?x).

Theorem app_nil_r : forall l : natlist,
    l ++ [] = l.
  Proof.
    induction l as [|n' l' Ihl'].
    - simpl. reflexivity.
    - simpl. rewrite -> Ihl'. reflexivity. Qed.

Search (_ ++ _ ++ _ = _ ++ _ ++ _).

Theorem rev_app_distr: forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.

Proof. intros l1 l2.
       induction l1 as [|n' l' ihl'].
       - simpl. rewrite app_nil_r. reflexivity.
       - simpl. rewrite -> ihl'.  rewrite <- app_asoc. reflexivity. Qed.
