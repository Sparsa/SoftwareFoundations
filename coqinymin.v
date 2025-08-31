From Stdlib Require Export String.
Definition x := 10.

Definition inc_nat (x:nat) : nat := x + 1.
Compute (1 + 1).

Inductive day : Type := 
    | Monday
    | Tuesday
    | Wednesday
    | Thursday
    | Friday
    | Saturday
    | Sunday.
    
Definition next_working_day (d: day) : day := 
match d with 
    | Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
    end.
   
    Compute (next_working_day Friday).
    Compute (next_working_day (next_working_day Saturday)).

Example test_next_working_day:
    (next_working_day (next_working_day Saturday)) = Tuesday.
    
Proof. simpl. reflexivity. Qed.

(* Booleans*)
Inductive Bool : Type := 
| True
| False.

Definition negb (b : Boo) : Bool :=
    match b with
    | True => False
    | False => True
    end.

Definition andb (b_1: Bool) ( b_2 : Bool) : Bool := 
    match b_1 with
    | True => b_2
    | False => False
    end.
    
Definition orb (b_1: Bool) (b_2: Bool) : Bool :=
    match b_1 with
    | True => True
    | False => b_2
    end.

