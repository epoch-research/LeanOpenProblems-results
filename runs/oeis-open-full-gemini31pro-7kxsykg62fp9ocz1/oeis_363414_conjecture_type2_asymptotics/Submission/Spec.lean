import FormalConjectures.Util.ProblemImports

open Nat Finset Complex Real Filter Asymptotics ZMod Int

noncomputable def a (n : ℕ) : ℤ :=
  let P_n : Complex :=
    Finset.prod (range (n + 1))
    (fun k : ℕ ↦ (1 : Complex) + ((2 * k : ℕ) : ℝ) * Complex.I)
  Int.floor (P_n.im / 2)

def type_two_primes_conjectured : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ (p : ZMod 4) = 1}

theorem oeis_363414_conjecture_type2_asymptotics :
  ∀ p : ℕ, Nat.Prime p → p ∈ type_two_primes_conjectured →
  (fun n ↦ (padicValInt p (a n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) / ((p : ℝ) - 1)) := by sorry

theorem oeis_363414_conjecture_type2_asymptotics.disproof : ¬ (type_of% @oeis_363414_conjecture_type2_asymptotics) := by sorry
