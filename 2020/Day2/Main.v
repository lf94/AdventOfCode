Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Import ListNotations.

Require Import Input.

Inductive Policy : Type :=
| password (min : nat) (max : nat) (c : ascii) (s : string).

Fixpoint _split (d : ascii) (s : string) (sp : string) (r : list string) : list string :=
match s with
| EmptyString => r ++ [sp]
| String c s' => if negb (Ascii.eqb c d)
  then _split d s' (sp ++ (string_of_list_ascii [c])) r
  else _split d s' "" (r ++ [sp])
end.

Definition split (d : ascii) (s : string) : list string :=
  _split d s "" [].

Fixpoint _N_of_string (s : list ascii) (r : nat) : nat :=
match s with
| nil => r
| cons c s' =>
  _N_of_string s'
  ((r * 10) + ((nat_of_ascii c) - (nat_of_ascii "0"%char)))
end.

Definition N_of_string (s : string) : nat :=
  _N_of_string (list_ascii_of_string s) 0.

Fixpoint _to_password_min_max (l : list string)
(count : nat)
(r : nat * nat) : (nat * nat) :=
match l with
| nil => r
| cons n l' => match count with
  | 0 => _to_password_min_max l' (count + 1) (N_of_string n, 0)
  | 1 => _to_password_min_max l' (count + 1) (fst r, N_of_string n)
  | _ => r
  end
end.

Definition to_password_min_max (s : string) : (nat * nat) :=
_to_password_min_max (split "-" s) 0 (0, 0).

Definition to_password_char (s : string) : ascii :=
  nth 0 (list_ascii_of_string (substring 0 1 s)) " "%char.

Fixpoint _to_policy
(l : list string) (count : nat)
(minmax : nat * nat)
(chr : ascii)
(str : string)
: option Policy :=
match l with
| nil => match minmax with | pair min max =>
    Some (password min max chr str)
  end
| cons ps l' => match count with
  | 0 => _to_policy l' (count + 1) (to_password_min_max ps) " "%char ""
  | 1 => _to_policy l' (count + 1) minmax (to_password_char ps) ""
  | 2 => _to_policy l' (count + 1) minmax chr ps
  | _ => match minmax with | pair min max =>
      Some (password min max chr str)
    end
  end
end.

Definition policy_of_string (s : string) : option Policy :=
  _to_policy (split " " s) 0 (0, 0) " "%char "".

Fixpoint count_char (c : ascii) (s : string) (count : nat) : nat :=
match s with
| EmptyString => count
| String c' s' => if (Ascii.eqb c' c)
  then count_char c s' (count + 1)
  else count_char c s' count
end.

Definition examine_policy_1 (p : Policy) : bool :=
match p with | password min max chr str =>
  let count := (count_char chr str 0) in
   (andb (negb (ltb count min)) (leb count max))
end.

Definition how_many_passwords_are_valid
(f : Policy -> bool)
(l : list Policy)
: nat :=
fold_right
(fun (el : bool) acc => if el then acc + 1 else acc) 0
(map (fun p => f p) l).

Compute how_many_passwords_are_valid
examine_policy_1
(map (fun p => match p with | None => password 0 0 " "%char "" | Some i => i end)
  (filter (fun p => match p with | None => false | _ => true end)
    (map policy_of_string puzzle_input)
  )
).

(* Part 2! *)

Definition examine_policy_2 (p : Policy) : bool :=
match p with | password pos1 pos2 chr str =>
  match (
    get (pos1 - 1) str,
    get (pos2 - 1) str
  ) with
  | (Some n, Some m) => xorb (Ascii.eqb n chr) (Ascii.eqb m chr)
  | (None, Some m) => Ascii.eqb m chr
  | (Some n, None) => Ascii.eqb n chr
  | (None, None) => false
  end
end.

Compute how_many_passwords_are_valid
examine_policy_2
(map (fun p => match p with | None => password 0 0 " "%char "" | Some i => i end)
  (filter (fun p => match p with | None => false | _ => true end)
    (map policy_of_string puzzle_input)
  )
).




