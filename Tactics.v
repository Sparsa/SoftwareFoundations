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
Proof. intros n m p q H.
