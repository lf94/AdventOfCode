Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Local Open Scope string_scope.

Fixpoint _split (d : ascii) (s : string) (sp : string) (r : list string) : list string :=
match s with
| EmptyString => r ++ [sp]
| String c s' => if negb (Ascii.eqb c d)
  then _split d s' (sp ++ (string_of_list_ascii [c])) r
  else _split d s' "" (r ++ [sp])
end.

Definition split (d : ascii) (s : string) : list string :=
  _split d s "" [].

Fixpoint _N_of_string (s : list ascii) (r : N) : N :=
match s with
| nil => r
| cons c s' =>
  _N_of_string s'
  ((r * 10) + ((N_of_ascii c) - (N_of_ascii "0"%char)))
end.

Definition N_of_string (s : string) : N :=
  _N_of_string (list_ascii_of_string s) 0%N.


Inductive RegexCommand : Type :=
| REOr
| REAnd.

Fixpoint _regex
(l : list (RegexCommand * list string))
(s : string)
(pos : nat)
(r : (bool * nat)) : (bool * nat) :=
match l with
| nil => r
| cons c l' =>
let rn := match c with
  | (REAnd, chars) => fold_left (fun r char => (match r with
    | (false, rp) => (false, pos)
    | (true, rp) => (match (index rp char s) with
      | None => (false, pos)
      | Some n => if Nat.eqb n rp
        then (true, n + 1)
        else (false, pos)
      end)
    end)) chars (fst r, pos)
  | (REOr, chars) => fold_left (fun r char => (match r with
    | (true, rp) => (true, rp)
    | (false, rp) => (match (index pos char s) with
      | None => (false, pos)
      | Some n => if Nat.eqb n pos
        then (true, pos + 1)
        else (false, pos)
      end)
    end)) chars (false, pos)
  end
in match rn with | (res, posn) =>
  _regex l' s posn rn
end
end.

Definition re_digits := 
["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"].

Definition re_af :=
["a";"b";"c";"d";"e";"f"].

Definition regex (l : list (RegexCommand * list string))
(s : string) : bool :=
fst (_regex l s 0 (true, 0)).