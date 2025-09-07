From Stdlib Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool): bool :=
  match b with
    | true => false
    | false => true
  end.
Definition andb (a b:bool) : bool :=
  match a with
    | true => b
    | false => false
  end.
Definition orb (a b:bool) : bool :=
  match a with
    | true => true
    | false => b
  end.
Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(*notation*)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true  = true.
Proof. simpl. reflexivity. Qed.

Definition negb' (b:bool) : bool :=
  if b then false
              else true.
Definition andb' (a b:bool): bool :=
  if negb' a then false
                  else if negb' b then false
                                         else true.
Definition orb' (a b : bool) : bool :=
  if a then true else b.

Inductive bw : Type:=
  | bw_black
      | bw_white.
Definition invert (x:bw) : bw :=
  if x then bw_white
  else bw_black.
Compute (invert bw_black).
Compute (invert bw_white).

Definition nandb (b1 b2 : bool) : bool :=
  negb (andb b1 b2).
Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3 : (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(*Types*)
Check true.

Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

(* new types from old *)

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type:=
  | black
  | white
  | primary (p : rgb).
Definition monochrome (c:color): bool :=
  match c with
    | black => true
    | white => true
    | primary p => false
  end.
Definition isred (c:color): bool:=
  match c with
    | primary red => true
    | _ => false
  end.

(*module*)
Module Playground.
  Definition foo: rgb := blue.
End Playground.

Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo: bool.

Module TuplePlayground.

Inductive bit : Type:=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0) : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).
End TuplePlayground.

Module NatPlayground.

Inductive nat: Type:=
  | O
  | S (n:nat).

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

Definition pred (n:nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.
Check (S (S (S (S O )))).
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S (n') ) => n'
  end.


End NatPlayground.
Fixpoint even (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S ( S ( n' ) ) => even n'
  end.
Definition odd (n:nat) : bool :=
    negb (even n).


Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2 : odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n m :nat) : nat :=
  match n with
    | 0 => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    |  O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n,m with
    | O , _ => O
    | S _, O => n
    | S n' , S m' => minus n' m'
  end.
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 12 10).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                    (at level 50, left associativity)
                    : nat_scope.
Notation "x - y " := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
(* Notation "x * y" := (mult x y)
                      (at level 50, left associativity)
                    : nat_scope. *)
Check ((0+1) + 1) : nat.
Fixpoint eqb (n m : nat) : bool :=
  match n with
    | O => match m with
            | O => true
            | S m' => false
          end
    | S n' => match m with
               | O => false
               | S m' => eqb n' m'
            end
    end.
Fixpoint leb ( m n : nat ) : bool :=
  match m with
    | O =>  true
    | S m' => match n with
            | O =>  false
            | S n' => leb m' n'
            end
    end.

Example test_leb1 : leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2 : leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3 : leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3' : (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  match (n =? m) with
    | true => false
    | false => (n <=? m)
  end.

Notation "x <? y" := (ltb x y) (at level 70): nat_scope.

Example test_ltb1 : (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2 : (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3 : (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.



Theorem plus_0_n'' : forall n : nat , 0  + n = n.
Proof. intros m. reflexivity. Qed.
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example: forall n m :nat,
    n = m ->
    n+n = m + m.
Proof. intros n m. intros H. simpl. rewrite H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat ,
    n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H1. intros H2. rewrite H1. rewrite H2 . reflexivity. Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0: forall p q : nat,
    (p *   0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  rewrite <- plus_O_n.
  reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n+1) =? 0 = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0: forall n : nat,
    (n+1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn: E.
 - reflexivity.
 - reflexivity. Qed.
(*The annotation as [|n'] is called an intro pattern. And it tells Coq what variable names to introduce
 for each partition. The first component is empty because the first value
 in the decomposition is 0 and doesn't require any varaible name, on the other hand
 The second part of the decomposition is n = S n' i.e., n can be a successor of n'
 In this case the new variable name required here is n' The eqn:E tells you to name the equation
 associated with the variable. If you don't provide the eqn:E part then Coq goal will not show you
 what case you are now solving and ofcourse what are the assumptions and what to use in case
you are planning to use the assumption during rewrite.. '-' are known as bullets and it basically
 demarks the end of one proof and beginning of another. If you dont use bullets coq expects you to write one proof afte another. But for the sake of readabilit and maintainability, it is suggested that you use the bullets.*)
Theorem andb_commutative: forall b c : bool , andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - destruct c eqn:Ec.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Theorem andb3_exchange:
  forall b c d: bool, andb (andb b c) d = andb (andb b d) c.
Proof. intros b c d. destruct b eqn:Eb.
       - destruct c eqn:Ec.
         {
           destruct d eqn:Ed.
           - reflexivity.
           - reflexivity.
         }
         {
           destruct d eqn:Ed.
           - reflexivity.
           - reflexivity.
         }
       - destruct c eqn:Ec.
         {
           destruct d eqn:Ed.
           - reflexivity.
           - reflexivity.
         }
         {
           destruct d eqn:Ed.
           - reflexivity.
           - reflexivity.
         }
         Qed.
Theorem andb_true_elim2: forall b c : bool,
    andb b c = true -> c = true.
Proof. intros b c.
       destruct c eqn:Ec.
       {
         destruct b eqn: Eb.
         - simpl. reflexivity.
         - intros. reflexivity.
       }
       {
         destruct b eqn: Eb.
         - simpl. intros H1. rewrite H1. reflexivity.
         - simpl. intros H1. rewrite H1. reflexivity.
       }
Qed.
(* case analysis is so common, that coq has a short hand of the following
 intros x y. destruct y as [|y] eqn:E
 We cn perform case analysis on a variable when introducing it by using an intro pattern instead of a variable name.*)
Theorem plus_1_neq_0' : forall n: nat,
    (n+1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.
(* Note that the decomposition of the tye depends on the consturctors of the type. The number of different constructors will have number of different variable names. *)
Theorem andb_commutative'' :
  forall b c , andb b c = andb c b.
Proof.
  intros [] []. (* because you are introducing two different variables *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n+1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.
 (*fixpoint and structural recursion*)
Fixpoint plus' (n m :nat): nat :=
  match n with
    | 0 => m
    | S n' => S (plus' n' m)
  end.
Check even 2.
Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool) , f (f b) = b.
  Proof.
    intros f. intros x. intros b. rewrite x. rewrite x. reflexivity. Qed.

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
    (forall (x:bool), f x = negb x) ->
    forall (b: bool), f ( f b ) = b.
Proof.
  intros f. intros x. intros b.
  rewrite x. rewrite x.
  destruct b.
  -  simpl. reflexivity.
  - simpl. reflexivity.
  Qed.
Theorem false_or:
  forall (b:bool),
    orb false b = b.
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.
Theorem or_true :
  forall (b: bool),
    orb true b = true.
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.
Theorem and_false:
  forall (b: bool),
    andb false b = false.
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.

Theorem and_var:
  forall (b : bool),
    andb true b = b.
Proof.
 intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.
Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
  Proof.
    intros b. intros c.
    destruct b eqn:Eb.
    - rewrite and_var. rewrite or_true. intros H1. rewrite H1. reflexivity.
    - rewrite false_or. rewrite and_false. intros H1. rewrite H1. reflexivity.
  Qed.
Inductive nat :=
  | Z
  | S (n : nat).
Definition one := S Z.
Definition two := S one.
Definition three := S two.

Fixpoint plus (a  b: nat) :=
  match a with
    | Z => b
    | S a' => S (plus a' b)
    end.
Example one_plus_two:
  plus one two = three.
Proof. simpl. reflexivity.
Qed.


Theorem n_plus_z:
  forall n,
    plus n Z = n.

Proof.
intros n. induction n.
- simpl. reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.
Lemma succ_plus:
forall a b,
   plus a (S b)=S (plus a b) .
Proof.
intros a b. induction a.
- simpl. reflexivity.
- simpl. rewrite IHa. reflexivity.
Qed.

Theorem add_comm :
forall a b  ,
plus a  b = plus b  a.
    
Proof.
  intros a b. induction a.
  - simpl. rewrite n_plus_z. reflexivity.
  - simpl. rewrite succ_plus. rewrite IHa. reflexivity.
Qed.

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.
Inductive modifier : Type :=
  | Plus | Natural | Minus.
Inductive grade : Type :=
  Grade (l:letter) (m:modifier).
Inductive comparison : Type :=
  | Eq
  | Lt
  | Gt.
Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A|B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, (A|B|C) => Lt
    | D, D => Eq
    | D, _ => Gt
    | F, (A|B|C|D) => Lt
    | F, F => Eq
  end.
Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.

Theorem letter_comparison_eq :
  forall l, letter_comparison l l = Eq.

Proof. intros l.
       destruct l.
       - reflexivity.
       - reflexivity.
       - reflexivity.
       - reflexivity.
       - reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier): comparison :=
  match m1, m2 with
    | Plus, Plus => Eq
    | Plus, _ => Gt
    | Natural, Plus => Lt
    | Natural, Natural => Eq
    | Natural, Minus => Gt
    | Minus, (Plus | Natural) => Lt
    | Minus, Minus => Eq
  end.
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
    | (Grade l1 m1), (Grade l2 m2) => match letter_comparison l1 l2 with
                                       | Lt => Lt
                                       | Eq => modifier_comparison m1 m2
                                       | Gt => Gt
                                    end
  end.
Example test_grade_comparisoin1:
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2:
  (grade_comparison (Grade F Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3:
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4:
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Definition lower_letter (l:letter) : letter :=
  match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F
  end.
Theorem lower_letter_lowers: forall (l :letter),
    letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    destruct l.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl.
  Abort.


Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof. simpl. reflexivity.
Qed.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l  = Lt.
  Proof.
    intros l. destruct l.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - rewrite lower_letter_F_is_F. simpl. intros. rewrite H. reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
    | Grade l m => match m with
                    | Plus => Grade l Natural
                    | Natural => Grade l Minus
                    | Minus => match l with
                                | A => Grade B Plus
                                | B => Grade C Plus
                                | C => Grade D Plus
                                | D => Grade F Plus
                                | F => Grade l m
                              end
                    end
  end.



Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
  simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
  simpl. reflexivity. Qed.
Theorem lower_grade_F_Minus: lower_grade (Grade F Minus) = (Grade F Minus).
  Proof. simpl. reflexivity.
         Qed.
Theorem lower_modifier:
  forall (l: letter),
    forall (m : modifier),
    letter_comparison F l = Lt ->
    grade_comparison ( lower_grade (Grade l m) ) (Grade l m) = Lt.
Proof.
  intros l. destruct m.
  - simpl. rewrite letter_comparison_eq. intro h. reflexivity.
  - simpl. rewrite letter_comparison_eq. intro h. reflexivity.
  - destruct l.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. intro h. rewrite h. reflexivity.
  Qed.




Theorem lower_grade_lowers:
  forall (g: grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
  Proof. intros g . destruct g eqn:Eg.
           - simpl. destruct m.
               + simpl. rewrite letter_comparison_eq. intro h. reflexivity.
               + intro h. simpl. rewrite letter_comparison_eq.  reflexivity.
               + intro h. destruct l.
                  * simpl. reflexivity.
                  * simpl. reflexivity.
                  * simpl. reflexivity.
                  * simpl. reflexivity.
                  * simpl. rewrite h. reflexivity.
  Qed.

(*Require Import ZArith.*)
Locate "_ <? _".


  (* Late day policy *)
  Definition apply_late_policy (late_days: Datatypes.nat) ( g: grade ) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

  Theorem apply_late_policy_unfold:
    forall (late_days: Datatypes.nat) (g : grade),
      (apply_late_policy late_days g)
        =
          (if late_days <? 9 then g else
             if late_days <? 17 then lower_grade g
              else if late_days <? 21 then lower_grade (lower_grade g)
                else lower_grade (lower_grade (lower_grade g))).
  Proof. intros. reflexivity.
Qed.


Theorem no_penalty_for_mostly_on_time:
  forall (late_days: Datatypes.nat) ( g: grade ),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof. intros l. intros g. rewrite apply_late_policy_unfold. intros h1. rewrite h1. reflexivity.
Qed.

Theorem grade_lowered_once:
  forall (late_days: Datatypes.nat) (g: grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof. intros l. intros g. rewrite apply_late_policy_unfold. intros h1. rewrite h1. intros h2. rewrite h2. reflexivity.
Qed.

End LateDays.

Inductive bin: Type :=
  | z
  | B0 (n:bin)
  | B1 (n:bin).

Fixpoint incr (m:bin):bin:=
  match m with
    | z => B1 ( z )
    | B0 (n') => B1 (n')
    | B1 ( n'  ) => B0 ( incr n' )
    end.
Fixpoint bin_to_nat (m:bin) : Datatypes.nat :=
  match m with
    | z => O
    | B1 (n' ) => (bin_to_nat (n') *2 ) + 1
    | B0 (n' ) => bin_to_nat (n') * 2
  end.

Example test_bin_incr1: (incr (B1 (z)) ) = B0 (B1 z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (incr (B0 (B1 z))) = B1 (B1 z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3: (incr (B1 (B1 z))) = B0 (B0 ( B1 z )).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4: bin_to_nat (B0 (B1 z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5:
  bin_to_nat (incr (B1 z)) = 1 + bin_to_nat (B1 z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6:
  bin_to_nat (incr (incr (B1 z))) = 2 + bin_to_nat (B1 z).
Proof. simpl. reflexivity. Qed.
