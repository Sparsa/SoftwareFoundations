From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

Check (cons nat 2 (cons nat 1 (nil nat)))
        : list nat.

Fixpoint repeat (X:Type) (x : X) (count : nat) : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count')
    end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. simpl.  reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).

Proof.  simpl. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble: Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m:mumble)
  | e (x : X).

(*Check d (b a 5) : grumble mumble.*)
Check d mumble (b a 5) :  grumble mumble.
Check d bool (b a 5) : grumble bool.
Check e bool true : grumble bool .
Check e mumble (b c 0) : grumble mumble.
(*Check e bool (b c 0): grumble bool.*)
Check c : mumble.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
    | 0 => nil X
    | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
        : forall X : Type, X -> nat -> list X.
Check repeat
        : forall X : Type, X -> nat -> list X.

Fixpoint repeat'' X x count : list X :=
  match count with
    | 0 => nil _
    | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.

Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X:Type} (x: X) (count : nat):
  list X :=
  match count with
    | 0 => nil
    | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
    | nil => nil
    | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X:Type} (l:list X) : nat:=
  match l with
    | nil => 0
    | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl. reflexivity. Qed.

Example test_rev2 :
  rev (cons true nil ) = cons true nil.
Proof. simpl. reflexivity. Qed.

Example test_length1 :  length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. simpl. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Notation " x :: y " := (cons x y)
                        (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Definition list123''' := [1;2;3].
Theorem app_nil_r : forall (X:Type), forall l:list X,
    l ++ [] = l.
Proof. intros X. induction l as [| l' Ihl'].
       - simpl. reflexivity.
       - simpl. rewrite IHIhl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
    l ++ m ++ n = (l ++ m ) ++ n.
Proof. intros A. intros l m n. induction l as [| l' Ihl'].
      - simpl. reflexivity.
      - simpl. rewrite IHIhl'. reflexivity.
Qed.

Lemma app_length: forall (X:Type) (l1 l2 : list X),
    length (l1 ++ l2 ) = length l1 + length l2.
Proof.
  intros X. intros l1 l2.
  induction l1 as [|n1 l1' Ihl1'].
  - simpl. reflexivity.
  - simpl. rewrite Ihl1'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. intros X. intros l1 l2. induction l1 as  [|n l1' Ihl1'].
       - simpl. rewrite app_nil_r. reflexivity.
       - simpl. rewrite Ihl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof. intros X. intros l. induction l as [|n l' Ihl'].
       - simpl. reflexivity.
       - simpl. rewrite rev_app_distr. rewrite Ihl'. simpl. reflexivity.
Qed.
(*Polymorpic Pairs*)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y) .

Arguments pair {X} {Y}. (* this is how you give the arguments *)

Notation "( x , y )" := (pair x y).

Notation " X * Y " := (prod X Y): type_scope.

(* type notation tells coq that this abbreviation should only be used when parsing types not when parsing expressions *)


Definition fst {X Y : Type} (p : X * Y):  X:=
  match p with
    | (x, y) => x
  end.

Definition snd {X Y :Type} (p : X * Y) : Y :=
  match p with
    | (x,y) => y
  end.

Fixpoint combine {X Y: Type} (lx : list X) (ly : list Y)
                 : list (X * Y) :=
  match lx, ly with
    | [] , _ => []
    | _ , [] => []
    | x :: tx, y :: ty => (x,y):: (combine tx ty)
end.

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y: Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
    | [] => ([],[])
    | (x,y)::ls => (x:: (fst (split ls)), y::(snd (split ls)))
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

(*polymorhpic options*)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x:X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X:Type} (l : list X) (n:nat)
                   : option X:=
  match l with
    | nil => None
    | a :: l' => match n with
                 | 0 => Some a
                 | S n' => nth_error l' n'
              end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.


Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | n :: ln => Some n
  end.

Check @hd_error : forall X : Type, list X -> option X.
Example test_hd_error1 : hd_error [1;2]  = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof. simpl. reflexivity. Qed.

(* functions as data *)

Definition doit3times {X: Type} (f : X -> X) (n: X) : X :=
  f (f (f n)).

Check @doit3times: forall X: Type, (X -> X) -> X -> X.

Definition minustwo (n: nat) : nat :=
  n - 2.
Compute minustwo 5.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. simpl. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. simpl. reflexivity. Qed.

(*Filter*)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) :=
  match l with
    | [] => []
    | h :: t =>
        if test h then h :: (filter test t)
        else filter test t
  end.

Example test_filter1 : filter even [1;2;3;4] = [2;4].
Proof. simpl. reflexivity. Qed.

Definition length_is_1 {X: Type} (l : list X) : bool :=
  (length l ) =? 1.
Example test_fileter2:
  filter length_is_1 [[1;2]; [3]; [4]; [5;6;7]; []; [8]] = [ [3 ] ; [4] ;[8]].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1 : countoddmembers' [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers'2 : countoddmembers' [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers'3 : countoddmembers' nil = 0.
Proof. simpl. reflexivity. Qed.

(* Annymous functions *)
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. simpl. reflexivity. Qed.

Example test_filter2':
  filter (fun l => (length l) =? 1) [[1;2];[3];[4];[5;6;7];[];[8]] = [ [3];[4];[8] ].
Proof. reflexivity. Qed.
Compute  gt  7 2.
Definition filter_even_gt7 (l: list nat) : list nat :=
  filter (fun l => (even l) && ( ltb 7 l)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition  {X:Type} (f : X -> bool)  (lx : list X) : (list X * list X) :=
  (filter f lx, filter (fun x => negb (f x)) lx). 
Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5],[2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
    | [] => []
    | h :: t => (f h ) :: (map f t)
  end.

Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity. Qed.

Example test_map2 : map odd [2;1;2;5] = [false ; true; false; true].
Proof. simpl. reflexivity. Qed.

Lemma map_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof. intros X Y. intros f. intros l1 l2. induction l1 as [|n l' Ihl'].
       - simpl. reflexivity.
       - simpl. rewrite Ihl'. reflexivity. Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l: list X),
    map f (rev l) = rev (map f l).
Proof. intros X Y. induction l as [| n l' Ihl].
       - simpl. reflexivity.
       - simpl. rewrite <- Ihl. rewrite map_distr. simpl. reflexivity. Qed. 

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l: list X) : list Y :=
  match l with
    | [] => []
    | x::lx => (f x) ++ (flat_map f lx)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
           = [1;1;1;5;5;5;4;4;4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} ( f : X -> Y ) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) ( b: Y)
              : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. simpl. reflexivity. Qed.

Example fold_example2:
  fold mult [1;2;3;4] 1 = 24.
Proof. simpl. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [ 1;2;3;4 ].
Proof. simpl. reflexivity. Qed.

Example fold_example4 :
  fold (fun l n => length l + n ) [[1];[];[2;3;2];[4]] 0 = 5.
Proof. reflexivity. Qed.

Compute even 4.
Compute fold (fun l n => (orb (even l) n ))  [1;2;3;5] false.
Example fold_example_one_even:
  fold (fun l n => (orb (even l) n ))  [1;2;3;5] false = true.
Proof. reflexivity. Qed.

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.

Example constfun_example1: ftrue 0 = true.
Proof. simpl. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. simpl. reflexivity.  Qed.

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3: nat -> nat.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

  Definition fold_length {X:Type} (l:list X) : nat :=
    fold (fun _ n => S n) l 0.
  Example test_fold_length1: fold_length [4;7;0] = 3.
  Proof. reflexivity. Qed.

  Lemma fold_length_sum : forall X (l: list X) (n:X),
      fold_length(n::l) = S (fold_length l).
    Proof. intros X. intros l. intros n.
           unfold fold_length. simpl. reflexivity. Qed.
  Theorem fold_length_correct : forall X (l:list X),
      fold_length l = length l.
  Proof. intros X. intros l. induction l as [|n l' Ihl'].
         - simpl. reflexivity.
         - simpl. rewrite fold_length_sum. rewrite Ihl'. reflexivity. Qed. 
  Definition fold_map {X Y :Type} ( f : X -> Y ) (l: list X) : list Y :=
    fold (fun a b => (f a) :: b) l [].
  Lemma foldmap_one : forall {X Y : Type} (f : X -> Y) (l: list X) (n: X),
      fold_map f (n::l) = (f n) :: (fold_map f l).
  Proof. intros X Y f. intros l. intros n. induction l as [| x l' Ihl'].
         - reflexivity.
         - reflexivity. Qed. 
  Theorem fold_map_correct : forall {X Y : Type} (f : X -> Y) (l:list X),
      fold_map f l = map f l.
    Proof. intros X Y. intros f. intros l.
           induction l as [|n l' Ihl'].
           - reflexivity.
           - simpl. rewrite foldmap_one. rewrite Ihl'. reflexivity. Qed.
    
Definition manual_grade_for_fold_map : option (nat * string) := None.

                                                       
Definition prod_curry {X Y Z : Type}
                      (f : X * Y -> Z) (x : X) (y: Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type}
                        (f : X -> Y -> Z) ( p : X * Y ) : Z :=
  f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                          (f : X -> Y -> Z)
                          x y,
    prod_curry (prod_uncurry f) x y = f x y.
  Proof. intros X Y Z f x y. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                          (f : (X * Y) -> Z) ( p: X * Y ),
    prod_uncurry (prod_curry f) p = f p.
  Proof. intros X Y Z f p. destruct p. 
         - reflexivity. Qed.
  Theorem nth_error_informal: forall (X : Type)
                                (l : list X)
                                (n : nat),
      length l = n -> @nth_error X l n = None.
  Proof. intros X l n. intros H. induction l as [| x l' Ihl'].
         - reflexivity.
         - rewrite <- H. simpl in H.  Admitted.                     

(* Church neumerals *)

  Module Church.

  Definition cnat := forall X : Type, (X -> X) -> X -> X.

  Definition one : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f x.

  Definition two : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f ( f x ).

  Definition zero : cnat :=
    fun (X : Type) ( f : X -> X ) (x : X) => x.
  Definition three : cnat := @doit3times.

  Definition zero' : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => zero.
  Definition one' : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
  Definition two' : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

  Example zero_church_peano : zero nat S O = 0.
  Proof. reflexivity. Qed.
  Example one_church_peano : one nat S O = 1.
  Proof. reflexivity. Qed.
  Example two_church_peano: two nat S O = 2.
  Proof. reflexivity. Qed.

   
  Definition scc (n: cnat) : cnat :=
    fun (X: Type) (f: X->X) (x:X) => f (n X f x).
    
     Example scc_1: scc zero = one.
  Proof.  reflexivity. Qed.

  Example scc_2 : scc one = two.
  Proof. reflexivity. Qed.

  Example scc_3 : scc two = three.
  Proof. reflexivity. Qed.

  Definition plus (n m : cnat) : cnat :=
   fun (X:Type) (f : X -> X) (x:X) => n X f (m X f x).

  Example plus_1: plus zero one = one.
  Proof. reflexivity. Qed.
  Example plus_2: plus two three = plus three two.
  Proof. reflexivity. Qed.
  Example plus_3 :
    plus (plus two two) three = plus one (plus three three).
  Proof. reflexivity. Qed.

  Definition mult (n m : cnat) : cnat :=
    fun (X:Type) (f: X -> X) (x:X) => n X (m X f) x .
  
  Example mult_1 : mult one one = one.
  Proof. reflexivity. Qed.
  Example mult_2 : mult zero (plus three three) = zero.
  Proof. reflexivity. Qed.
  Example mult_3 : mult two three = plus three three.
  Proof. reflexivity. Qed.

  Definition exp (n m : cnat) : cnat :=
    fun (X:Type) => m (X->X) (n X). 
(*    fun (X:Type) (f : X -> X) (x:X) => n X (mult m X f) x. *)
  Example exp_1 : exp two two = plus two two.
  Proof. reflexivity. Qed.

  Example exp_2 : exp three zero = one.
  Proof. reflexivity. Qed.
  Example exp_3 : exp three two = plus (mult two (mult two two )) one.
  Proof. reflexivity. Qed.

  End Church.
  End Exercises.
                                  
