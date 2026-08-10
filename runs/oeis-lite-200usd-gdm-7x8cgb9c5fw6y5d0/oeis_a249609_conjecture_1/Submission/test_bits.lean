import FormalConjectures.Util.ProblemImports

open Nat List

def bits_fuel : ℕ → ℕ → List Bool
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2 == 1) :: bits_fuel fuel (n / 2)

lemma bits_eq_fuel (fuel : ℕ) (n : ℕ) (hfuel : n ≤ fuel) :
    n.bits = bits_fuel fuel n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rfl
  | succ f ih =>
    rw [Nat.bits]
    dsimp [bits_fuel]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      have h_div : n / 2 ≤ f := by
        have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        omega
      exact ih (n / 2) h_div
