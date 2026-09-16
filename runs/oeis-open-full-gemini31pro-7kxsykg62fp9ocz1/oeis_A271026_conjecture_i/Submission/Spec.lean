import FormalConjectures.Util.ProblemImports

open Nat Finset

def is_A271026_w_term (R : ℕ) : Bool :=
  (Nat.sqrt (24 * R + 1)) ^ 2 = 24 * R + 1

def A271026 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun x =>
  if x^7 > n then 0 else
  Finset.sum (Finset.range (n + 1)) fun y =>
    if x^7 + y^4 > n then 0 else
    Finset.sum (Finset.range (n + 1)) fun z =>
      let S := x^7 + y^4 + z^3
      if S > n then 0 else
      let R := n - S
      if is_A271026_w_term R then 1 else 0

def A271026_exceptional_set : Set ℕ :=
  {0, 47, 61, 62, 112, 175, 448, 573, 714, 1073, 1175, 1839, 2167, 8043, 13844}

theorem oeis_A271026_conjecture_i (n : ℕ) :
  A271026 n > 0 ∧ (A271026 n = 1 ↔ n ∈ A271026_exceptional_set) := sorry

theorem oeis_A271026_conjecture_i.disproof : ¬ (type_of% @oeis_A271026_conjecture_i) := sorry
