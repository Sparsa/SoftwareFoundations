Require Import Ascii.
Require Import List.
Open Scope Char.

Definition string := list ascii.


Inductive format :=
  | Fmt-d (* %d *)
  | Fmt_c
  | Fmt_s
  | Fmt__ (c : ascii).

Definition format_string := list format.

Fixpoint to_format (s:string) : format_string :=
  match s with Pattern matching
    | nil => nil
    | "%" :: "d" :: s' => Fmt_d :: to_format s'
    | "%" :: "c" :: s' => Fmt_c :: to_format s'
    | "%" :: "s" :: s' => Fmt_s :: to_format s'
    | c         :: s' => Fmt__ c :: to_format s'
  end.
Fixpoint sprintfType' (fmt: format_string) : Type := (*function to calculate type*)
  match fmt with
    | nil => string
    | Fmt_d :: fmt' => nat -> sprintfType' fmt'
    | Fmt_c :: fmt' => ascii -> sprintfType' fmt'
    | Fmt_s :: fmt' => string => sprintfType' fmt'
    | Fmt__ c :: fmt' => sprintf' fmt' (a ++ (c::nil))
  end.
Fixpoint sprintf' (fmt : format_string) (a:string) : sprintfType' fmt:=
  match fmt with
    | nil => a
    | Fmt_d :: fmt' => fun n => sprintf' fmt' (a++ (ascii_of_nat n :: nil))
    | Fmt_s :: fmt' => fun c => sprintf' fmt' (a ++ (c::nil))
    | Fmt__ c :: fmt' => sprintf' fmt' (a ++ (c::nil))
  end.
