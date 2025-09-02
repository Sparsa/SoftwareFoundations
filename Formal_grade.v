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

Require Import ZArith.
Locate "_<?_".


  (* Late day policy *)
  Definition apply_late_policy (late_days: nat) ( g: grade ) : grade :=
    if late_days <? 9 then g
    else if late_days <? 17 then lower_grade g
    else if late_days <? 21 then lower_grade (lower_grade g)
    else lower_grade (lower_grade (lower_grade g)).

  Theorem apply_late_policy_unfold:
    forall (late_days: nat) (g : grade),
      (apply_late_policy late_days g)
        =
          (if late_days <? 9 then g else
             if late_days <? 17 then lower_grade g
              else if late_days <? 21 then lower_grade (lower_grade g)
                else lower_grade (lower_grade (lower_grade g))).
  Proof. intros. reflexivity.
Qed.


Theorem no_penalty_for_mostly_on_time:
  forall (late_days: nat) ( g: grade ),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof. intros l. intros g. rewrite apply_late_policy_unfold. intros h1. rewrite h1. reflexivity.
Qed.

Theorem grade_lowered_once:
  forall (late_days: nat) (g: grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof. intros l. intros g. rewrite apply_late_policy_unfold. intros h1. rewrite h1. intros h2. rewrite h2. reflexivity.
Qed.
