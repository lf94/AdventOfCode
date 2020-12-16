Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Import ListNotations.

Require Import Local.Y2020.Day6.Input.
Require Import Local.Utils.Sorting.

Local Open Scope string_scope.

Definition Question := ascii.
Definition IndividualResponses := list Question.
Definition GroupResponses := list IndividualResponses.
Definition Responses := list GroupResponses.

Fixpoint group_responses_of_list_string (l : list string)
(r1 : GroupResponses)
(r2 : Responses)
: Responses :=
match l with
| nil => (List.app r2 [r1])
| cons s l' => match s with
  | EmptyString => group_responses_of_list_string l' nil (List.app r2 [r1])
  | line => group_responses_of_list_string l' (List.app r1 [(list_ascii_of_string line)]) r2
  end
end.

Definition group_responses := group_responses_of_list_string puzzle_input [] [].
Compute group_responses.

(* Part 1 - Count the number of questions anyone answered in each group. *)

Definition find_questions_anyone_answered := map (fun group =>
  fold_left (fun s1 i =>
    (fold_left (fun s2 ans =>
      if existsb (fun e => Ascii.eqb ans e) s2
      then s2 else (ans :: s2)
    ) i s1)
  ) group []
) group_responses.

Compute find_questions_anyone_answered.

Compute fold_left (fun r e => r + 1) (flat_map (fun i => i) find_questions_anyone_answered) 0.

(* Part 2 - Count the number of questions everyone answered yes in each group. *)

(* Sort all the responses per group and record the number of participants. *)

Definition find_questions_everyone_answered := map (fun group : GroupResponses =>
  (List.length group, (bubble_sort Nat.ltb 0
  (map (fun i => nat_of_ascii i) (flat_map (fun i => i) group))))
) group_responses.

Compute find_questions_everyone_answered.

(* Count each response and if it appears the number of participants, it's been answered by everyone. *)

Definition fqea2 := map (fun g => match g with | (p, rs) =>
  if Nat.eqb p 1
  then (0, 0, List.length rs)
  else fold_left (fun r e => match r with | (c, n, t) =>
    if Nat.eqb e c
    then (c, n + 1, if Nat.eqb p (n + 1) then t + 1 else t)
    else (e, 1, t)
  end) rs (0, 1, 0)
end) find_questions_everyone_answered.

Compute fqea2.

Compute fold_left (fun r e => match e with | (c, p, t) =>
  r + t
  end
) fqea2 0.

