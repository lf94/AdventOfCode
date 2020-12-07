Require Import Coq.NArith.NArith.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope nat_scope.
Local Open Scope N_scope.

Definition puzzle_input : list N := [1788;1627;1883;1828;1924;1993;972;1840;1866;
1762;1781;1782;1520;1971;1660;1857;1867;1564;1983;1391;2002;494;1500;
1967;1702;1958;1886;1910;1838;1985;1836;2009;2005;1602;1939;1945;1609;
1582;1647;1737;1982;1931;790;745;1598;1586;1547;1951;1264;1382;1776;
1499;1977;1766;1360;1807;1991;1981;1693;634;1847;1774;1990;1409;1410;
1974;1862;1744;1827;1978;1980;2003;1491;1595;1640;1576;1887;1746;1617;
1923;1706;1964;60;1620;1959;257;1395;1854;1843;1682;1667;1639;279;1911;
1986;1575;1232;1919;1852;1509;1976;1465;2008;1953;1518;1795;1912;1269;
1835;1984;1538;2001;1954;1365;1569;1418;1844;1580;1875;1551;1861;1946;
1810;1655;1987;1549;1301;1859;1929;1254;1604;1933;1998;1661;1899;1411;
1975;1707;1966;1601;1936;1440;1942;1937;1851;1731;1257;1533;1405;1890;
1600;1970;1626;1824;1442;2006;1796;1658;1930;646;1904;1489;2004;1922;
1979;107;1833;1856;1952;1791;1728;2010;1965;1646;1522;1671;1624;1876;
1424;1802;1623;1870;1242;1591;1338;754;1826;1305;1825;1793;1872;1741;
1537;1759;1962;1773;1907;1573;1908;1903].

(* Find the two entries that sum to 2020: *)

Definition enum {A : Type} (l: list A) : list (nat * A):=
  combine (seq 0 (length l)) l.

Definition denum {A : Type} {B : Type} (l : list (A * B)) :=
(snd (split l)).

Definition denum_pair_list {A : Type} (l : (list (nat * A) * list (nat * A))) :=
(flat_map denum [fst l], flat_map denum [snd l]).

Definition remove_n_from {A : Type} (start : nat) (n : nat) (l : list A) : (list A * list A) :=
denum_pair_list (partition (fun a => match a with | pair i _ =>
  andb (negb (ltb i start)) (ltb i (start + n))
end)
(enum l)).

Definition enum_repeat_list {A : Type} (l : list A) : list (nat * list A) :=
enum (repeat l (length l)).

Definition remove_indices {A : Type} (l : list (nat * list A)) : list (list A) :=
map (fun p => match p with | pair i l => snd (remove_n_from i 1 l) end)
l.

Definition ns := remove_indices (enum_repeat_list puzzle_input).

Definition data := combine puzzle_input ns.

Definition find_sums_two (l : list (N * list N)) (t : N) :=
map (fun p => match p with | pair l r =>
  match find (fun n => (l + n) =? t) r with
  | None => None
  | Some n => Some (l, n)
  end
end) l.

Definition get_first_some (l : list (option (N * N))) : list (option (N * N)) :=
firstn 1 (filter (fun o => match o with
  | None => false
  | Some p => true
  end
) l).

Definition sum_2020 := get_first_some (find_sums_two data 2020).

(* ...and multiply them together: *)

Compute match sum_2020 with
  | nil => 0
  | cons e _ => match e with
    | None => 0
    | Some p => match p with | pair a b => a * b end
    end
  end.

(* Part 2 - Time to generalize! *)

(* Hardcoding the recursion as a first version *)

Definition find_sum_naive := fold_right (fun n1 r1 =>
  match r1 with
  | None => (fold_right (fun n2 r2 =>
      match r2 with
      | None => (fold_right (fun n3 r3 =>
          match r3 with
          | None => if (n1 + n2 + n3 =? 2020)
            then Some [n1; n2; n3]
            else None
          | Some p => Some p
          end
        ) None puzzle_input) 
      | Some p => Some p
      end
    ) None puzzle_input)
  | Some p => Some p
  end) None puzzle_input.

(* Creating a generalized recursive variant! *)

Fixpoint find_sum (t : N) (n : nat) (l : list N) (s : list N) : (option (list N)) :=
match n with
| O => if (fold_right (fun a b => a + b) 0 s) =? t
  then Some s
  else None
| S n' => fold_right (fun nn rn =>
  match rn with
    | None => find_sum t n' l (s ++ [nn])
    | Some p => Some p
  end) None l
end.

(* ...and multiply them together: *)

Compute match find_sum 2020 3 puzzle_input [] with
  | None => 0
  | Some l => fold_right (fun a b => a * b) 1 l
end.
