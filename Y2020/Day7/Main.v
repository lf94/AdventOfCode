Require Import Coq.NArith.NArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope N_scope.

Inductive Bag : Type :=
| bag (amount : N) (color : string) (holding : list Bag).

Fixpoint _t
(b : Bag)
(f : Bag -> bool)
(r : bool)
: bool
:=
match b with | bag amount color b' =>
  match f b with
  | true => true
  | false => fold_left (fun r e => orb r (_t e f r)) b' false
  end
end.

Definition is_target_bag (b : Bag) : bool :=
match b with | bag amount color _ => N.eqb amount 2 end.

Compute map (fun e => _t e is_target_bag false)
  [bag 0 "shiny orange" [
    bag 3 "dim cyan" [bag 2 "yes yes" nil];
    bag 1 "mirrored beige" nil;
    bag 5 "pale orange" nil
  ]].