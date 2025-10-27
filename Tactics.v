From LF Require Export Poly.

Theorem silly1 : forall (n m : nat),
    n = m ->
    n = m.
  Proof. intros n m eq.
         apply eq. Qed.
  Theorem silly2 : forall (n m o p : nat),
      n = m ->
      (n = m -> [n;o] = [m;p]) ->
      [n;o] = [m;p].
    Proof. intros n m o p eq1 eq2.
           apply eq2. apply eq1. Qed.

    Theorem silly2a : forall (n m : nat),
        (n,n) = (m,m) ->
        (forall (q r : nat) , (q,q) = (r,r) -> [q] = [r]) ->
        [n] = [m].
    Proof.
      intros n m eq1 eq2.
      apply eq2.
      apply eq1.
      Qed.

    Theorem silly_ex : forall p,
        (forall n, even n = true -> even (S n) = false) ->
        (forall n, even n = false -> odd n = true) ->
        even p = true ->
        odd (S p) = true.
      Proof.
        intros n eq1 eq2 eq3.
        apply eq2.
        apply eq1.
        apply eq3.
        Qed.

      
      Theorem silly3 : forall (n m : nat),
          n = m ->
          m = n.
      Proof.
        intros n m H.
        symmetry. apply H. Qed.

      Search rev.
      Theorem rev_exercise : forall (l l' : list nat),
          l = rev l' ->
          l' = rev l.
      Proof. intros l l' eq1 .
             rewrite eq1.
             symmetry.
             apply rev_involutive.
             Qed.

      (* rewrite is applied when you want to replace a section of the proof with an equivalent mode but apply means you can apply a theorem result   *)


Example trans_eq_example : forall (a b c d e f : nat),
          [a;b] = [c;d] ->
          [c;d] = [e;f] ->
          [a;b] = [e;f].
             
Proof. intros a b c d e f eq1 eq2.
       rewrite -> eq1. apply eq2. Qed.

Theorem trans_eq : forall (X : Type) (x y z: X),
    x = y -> y = z -> x = z.
  Proof. intros X x y z eq1 eq2.
         rewrite -> eq1.
         rewrite -> eq2.
         reflexivity. Qed.
  Example trans_eq_example' : forall ( a b c d e f : nat ),
      [a;b] = [c;d] ->
      [c;d] = [e;f] ->
      [a;b] = [e;f].
  Proof.
    intros a b c d e f eq1 eq2.
    apply trans_eq with (y :=[c;d]).
    apply eq1. apply eq2.
    Qed.

  
  
        
Example trans_eq_exercise : forall (n m o p  : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2.
  Qed.

Theorem S_injective : forall (n m : nat),
    S n = S m ->
    n = m.
  Proof.
    intros n m H1.
    assert (H2 : n = pred (S n)). {reflexivity.}
    rewrite H2. rewrite H1. simpl. reflexivity.
Qed.
  
  
Theorem S_injective' : forall (n m : nat),
    S n = S m ->
    n = m.
  Proof.
    intros n m H. 
    injection H as Hmn.
    apply Hmn.
  Qed.
  

  Theorem injuection_ex1 : forall (n m o : nat),
      [n;m] = [o;o] ->
      n = m.
    Proof.
      intros n m o H.
      injection H as H1 H2.
      rewrite H1. rewrite H2. reflexivity.
      Qed.

    
      
Theorem injection_ex1 : forall (n m o : nat),
    [n ;m] = [o;o] ->
    n = m.
  Proof.
    intros n m o H.
    injection H as H1 H2.
    rewrite H1. rewrite H2. reflexivity.
  Qed.

  Example injection_ex3 : forall (X : Type) ( x y z : X  ) ( l j : list X ),
      x :: y :: l = z :: j ->
      j = z::l ->
      x = y.
  Proof.
    intros X x y z l j.
    intros H1 H2.
    injection H1 as Hii Hi2. 
    rewrite H2 in Hi2. rewrite <- Hii in Hi2. symmetry. injection Hi2 as Hmm. rewrite Hmm. reflexivity.
    Qed.

  
    
Theorem discriminate_ex1 : forall (n m : nat) ,
    false = true ->
    n = m.
Proof.
  intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
    S n = 0 ->
    2 + 2 = 5.
Proof. intros n H.
       discriminate H. Qed.

Example discriminate_ex3:
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof. intros X x y z l j. intros H.
       discriminate H. Qed.

Theorem eqb_0_l : forall n,
    0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - intros H. discriminate H. Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) ( x  y : A ),
    x = y -> f x = f y.
Proof. intros A B f x y. intros H.
       rewrite H. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H.
       Qed.
Theorem eq_implies_succ_equal' : forall ( n m : nat ),
    n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H.
       Qed.

(*tactics on hypothesis*)

Theorem S_inj : forall (n m : nat) (b : bool),
    ((S n) =? (S m)) = b  ->
    ( n =? m  ) = b.
Proof.  intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
    (n = m -> p = q) ->
    m = n ->
    q = p.
Proof. intros n m p q H1 H2.
       symmetry in H2.
       apply  H1 in H2. symmetry in H2. apply H2. Qed.

(* Specialize *)
(* combination of assert and apply *)

Theorem specialize_example: forall n,
    (forall m, m * n = 0)
      -> n = 0.
  Proof. intros n H.
         specialize H with (m := 1).
         rewrite mult_1_1 in H.
         apply H. Qed.

Example trans_eq_example''' : forall (a b c d e f: nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].

Proof. intros a b c d e f H1 H2.
       specialize trans_eq with (y:=[c;d]) as H.
       apply H. apply H1. apply H2. Qed.

Theorem double_injective_FAILED: forall n m,
    double n = double m ->
    n = m.
Proof.
  intros n m. induction n as [| n' Ihn'].
  - (*n = O*) simpl. intros eq.  destruct m as [| m'] eqn:E.
    + (*m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m'*) f_equal.
      Abort.

Theorem double_injection : forall n m ,
    double n = double m ->
    n = m.
  Proof.
    intros n. induction n as [|n' Ihn'].
    - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
      + (* m = O*) reflexivity.
      +  (* m = S m' *) discriminate eq.
    - (* n = S n' *) intros m eq. destruct m as [| m'] eqn:E.
      + discriminate eq.
        + f_equal.
    apply Ihn'. simpl in eq. injection eq as goal. apply goal. Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
  Proof. intros n.
         induction n as [|n' Ihn'].
         - destruct m as [|m'] eqn:E.
           + reflexivity.
           + discriminate.
         - destruct m as [|m'] eqn:E.
           + discriminate.
           + f_equal. simpl in Ihn'. simpl. intros h1. apply  Ihn' in h1. f_equal. apply h1. Qed.

Search plus. 
  
Theorem plus_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof. intros n. induction n as [| n' Ihn'].
       - destruct m as [| m' ].
         + reflexivity.
         + simpl. discriminate.
       - destruct m as [| m'].
         + discriminate.
         + intros H.  simpl in H. rewrite succ_plus in H. rewrite succ_plus in H. simpl in H. 
           specialize f_equal with (f:=S) (A:=nat) (B:=nat) as H'. injection H as Hnm. 
           f_equal. apply Ihn'. apply Hnm. Qed.


           
       
Theorem double_injective_take2_Failed : forall n m,
    double n = double m ->
    n = m.

  Proof. intros n m. induction m as [| m' Ihm'].
         - (* m = 0  *) simpl. intros eq. destruct n as [| n'] eqn:E.
           + reflexivity.
           + discriminate eq.
        - intros eq. destruct n as [| n'] eqn:E.
          + discriminate eq.
          + f_equal.
            Abort.

  Theorem double_injective_take2 : forall n m,
      double n = double m ->
      n = m.
  Proof.
    intros n m.
    generalize dependent n.
    induction m as [| m' IHm'].
    - simpl. intros n eq. destruct n.
      + reflexivity.
      + discriminate eq.

    - intros n eq. destruct n as [|n'] eqn:E.
      + discriminate eq.
      + f_equal.
        apply IHm'. injection eq as goal. apply goal. Qed.

Search add_0_r.


Lemma sub_add_leb: forall n m, n <=? m = true -> (m-n)+n = m.
  Proof.
    intros n.
    induction n as [| n' IHn'].
    - intros m H. rewrite
