Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Import ListNotations.

Require Import Input.

Local Open Scope string_scope.

Inductive Measurement : Type :=
| cm (n : N)
| inch (n : N).

Record Passport : Type := mkPassport {
  byr : option N;
  iyr : option N;
  eyr : option N;
  hgt : option Measurement;
  hcl : option string;
  ecl : option string;
  pid : option string;
  cid : option string
}.

(* Parsing *)

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

Definition _parse_hgt (s : string) : option Measurement :=
match (orb
  (regex [(REOr, re_digits); (REOr, ["in"; "cm"])] s)
  (orb
    (regex ((repeat (REOr, re_digits) 2 ) ++ [(REOr, ["in"; "cm"])]) s)
    (regex ((repeat (REOr, re_digits) 3 ) ++ [(REOr, ["in"; "cm"])]) s)
  )
) with
| false => None
| true => match split "c" s with
  | [n; r] => Some (cm (N_of_string n))
  | [nm] => match split "i" s with
    | [n; r] => Some (inch (N_of_string n))
    | _ => None
    end
  | _ => None
  end
end.

Definition _parse_line (s : string) (p : Passport) : Passport := 
fold_right (fun kv rp =>
match kv with
| ["byr"; v] => mkPassport
  (Some (N_of_string v)) (iyr rp) (eyr rp) (hgt rp)
  (hcl rp) (ecl rp) (pid rp) (cid rp)
| ["iyr"; v] => mkPassport
  (byr rp) (Some (N_of_string v)) (eyr rp) (hgt rp)
  (hcl rp) (ecl rp) (pid rp) (cid rp)
| ["eyr"; v] => mkPassport
  (byr rp) (iyr rp) (Some (N_of_string v)) (hgt rp)
  (hcl rp) (ecl rp) (pid rp) (cid rp)
| ["hgt"; v] => mkPassport
  (byr rp) (iyr rp) (eyr rp) (_parse_hgt v)
  (hcl rp) (ecl rp) (pid rp) (cid rp)
| ["hcl"; v] => mkPassport
  (byr rp) (iyr rp) (eyr rp) (hgt rp)
  (Some v) (ecl rp) (pid rp) (cid rp)
| ["ecl"; v] => mkPassport
  (byr rp) (iyr rp) (eyr rp) (hgt rp)
  (hcl rp) (Some v) (pid rp) (cid rp)
| ["pid"; v] => mkPassport
  (byr rp) (iyr rp) (eyr rp) (hgt rp)
  (hcl rp) (ecl rp) (Some v) (cid rp)
| ["cid"; v] => mkPassport
  (byr rp) (iyr rp) (eyr rp) (hgt rp)
  (hcl rp) (ecl rp) (pid rp) (Some v)
| _ => rp
end
) p
(map (fun kv => split ":" kv) (split " " s)).

Fixpoint _parse (ls : list string) (p : Passport)
(lp : list Passport) : list Passport :=
match ls with
| nil => lp ++ [p]
| cons lt ls' => if String.eqb lt EmptyString
  then _parse ls' (mkPassport None None None None None None None None) (lp ++ [p])
  else _parse ls' (_parse_line lt p) lp
end.

Definition parse (l : list string) : list Passport :=
_parse l 
(mkPassport None None None None None None None None)
[].

(* Part 2 - Validation *)

Definition between (n : N) (s : N) (e : N) : bool :=
andb (negb (N.ltb n s)) (N.leb n e).

Definition validate_byr (n : N) : bool :=
between n 1920 2002.
Definition validate_iyr (n : N) : bool :=
between n 2010 2020.
Definition validate_eyr (n : N) : bool :=
between n 2020 2030.

Definition validate_hgt (h : Measurement) : bool :=
match h with
| cm n => between n 150 193
| inch n => between n 59 76
end.

Definition validate_hcl (s : string) : bool :=
andb
(Nat.eqb (String.length s) 7)
(regex (
  [(REAnd, ["#"])] ++
  (repeat (REOr, List.concat [re_digits; re_af]) 6)) s).

Definition validate_ecl (s : string) : bool :=
andb
(Nat.eqb (String.length s) 3)
(match find (fun c => String.eqb c s)
["amb"; "blu"; "brn"; "gry"; "grn"; "hzl"; "oth"]
with
| None => false
| _ => true
end).

Definition validate_pid (s : string) : bool :=
andb
(Nat.eqb 9 (String.length s))
(regex (repeat (REOr, re_digits) 9) s).

Definition passport_validate (p : Passport) : bool :=
fold_left (fun r e => andb r e)
(match p with
| mkPassport
  (Some byr) (Some iyr) (Some eyr) (Some hgt)
  (Some hcl) (Some ecl) (Some pid) _ => [
    validate_byr byr;
    validate_iyr iyr;
    validate_eyr eyr;
    validate_hgt hgt;
    validate_hcl hcl;
    validate_ecl ecl;
    validate_pid pid;
    true
  ]
| mkPassport _ _ _ _ _ _ _ _ => [false]
end) true.

(* Counting *)

Definition passports := parse puzzle_input.

Definition how_many_passports_valid (p : list Passport) : nat :=
fold_right (fun p r => match passport_validate p with
| true => r + 1
| false => r
end) 0 p.


Compute how_many_passports_valid passports.



