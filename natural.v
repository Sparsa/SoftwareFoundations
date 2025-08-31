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