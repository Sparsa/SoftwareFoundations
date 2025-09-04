Inductive bin: Type :lied=
  | z
  | B0 (n:bin)
  | B1 (n:bin).

Fixpoint incr (m:bin):bin:=
  match m with
    | z => B1 ( z )
    | B0 (n') => B1 (n')
    | B1 ( n'  ) => B0 ( incr n' )
    end.
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
    | z => O
    | B1 (n' ) => bin_to_nat (n')*2 + 1
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
