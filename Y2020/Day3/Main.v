Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Import ListNotations.

Require Import Input.

Local Open Scope list_scope.

Inductive Space : Type :=
| Open
| Tree.

Inductive Step : Type :=
| North
| East
| South
| West.

Definition Hill := list (list Space).

Definition hill := map (fun l => 
  map (fun a => match a with
  | "#"%char => Tree
  | "."%char => Open
  | _ => Open
  end) l
) (map list_ascii_of_string puzzle_input).

Fixpoint _slide
(queue : list Step)
(posx : nat)
(posy : nat)
(r : list (nat * nat))
: list (nat * nat) :=
match queue with
| nil => r
| cons direction queue' =>
  match direction with
  | South => _slide queue' posx (posy + 1) (r ++ [(posx, posy + 1)])
  | East => _slide queue' (posx + 1) posy (r ++ [(posx + 1, posy)])
  | North => _slide queue' posx (posy - 1) (r ++ [(posx, posy - 1)])
  | West => _slide queue' (posx - 1) posy (r ++ [(posx - 1, posy)])
  end
end.

Definition slide_iters (h : Hill) (steps : list Step) : nat :=
div ((List.length h) - 1) (fold_right (fun s r => match s with
| North => r - 1
| South => r + 1
| _ => r
end) 0 steps).

Definition enum {A : Type} (l : list A) : (list (nat * A)) :=
combine (seq 0 (List.length l)) l.

Definition denum {A : Type} {B : Type} (l : list (A * B)) :=
(snd (split l)).

Definition slide (h : Hill) (steps : list Step) : N :=
fold_right (fun space r => match space with
| Open => r
| Tree => N.add r 1
end) 0%N
(map (fun p => match p with | (x, y) =>
  let plane := (nth y h [])
  in nth (x mod (List.length plane)) plane Open
end)
(denum (filter (fun p => match p with | (n, (x, y)) =>
  (n + 1) mod (List.length steps) =? 0 end)
(enum (_slide 
  (flat_map (fun i => i) (repeat steps (slide_iters hill steps)))
  0 0 []
))))).

Definition slopes := [
  [East; South];
  [East; East; East; South];
  [East; East; East; East; East; South];
  [East; East; East; East; East; East; East; South];
  [East; South; South]
].

(* Part 2 - modified part 1, just less messy. *)

Compute fold_right (fun n r => N.mul n r) 1%N
(map (fun steps =>
  slide hill steps
) slopes).

