Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint _bubble_sort {A : Type}
(f : A -> A -> bool)
(default : A)
(list_length : nat) (unsorted  : list A) (result : list A) : list A
:= match list_length with
| 0 => result
| S n =>
  let max := fold_left (fun r e => if f r e then e else r) unsorted default in
  match (partition (fun e => f e max) unsorted) with
  | (unsorted', sorted) => _bubble_sort f default n unsorted' (List.app sorted result)
  end
end.

Definition bubble_sort {A : Type} (f : A -> A -> bool) (default: A) (l : list A) : list A :=
_bubble_sort f default (List.length l) l nil.