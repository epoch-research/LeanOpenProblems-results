import FormalConjectures.Util.ProblemImports

open Finset Nat Int

def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

theorem oeis_179537_conjecture_sun_part2a_mod_n :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by
  sorry

theorem oeis_179537_conjecture_sun_part2a_mod_n.disproof : ¬ (type_of% @oeis_179537_conjecture_sun_part2a_mod_n) := by
  sorry
