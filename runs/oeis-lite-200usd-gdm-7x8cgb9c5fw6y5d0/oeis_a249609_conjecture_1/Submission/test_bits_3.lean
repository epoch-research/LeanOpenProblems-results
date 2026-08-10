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
    exact Nat.zero_bits
  | succ f ih =>
    dsimp [bits_fuel]
    by_cases hn : n = 0
    · simp [hn, Nat.zero_bits]
    · simp [hn]
      have h_div : n / 2 ≤ f := by
        have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
        omega
      by_cases hmod : n % 2 = 1
      · have hn_eq : n = 2 * (n / 2) + 1 := by
          rw [← Nat.div_add_mod n 2]
          omega
        have h_bits_eq : n.bits = true :: (n / 2).bits := by
          rw [hn_eq, Nat.bit1_bits]
        rw [h_bits_eq]
        simp [hmod]
        exact ih (n / 2) h_div
      · have hmod_zero : n % 2 = 0 := by omega
        have hn_eq : n = 2 * (n / 2) := by
          rw [← Nat.div_add_mod n 2]
          omega
        have h_div_ne : n / 2 ≠ 0 := by omega
        have h_bits_eq : n.bits = false :: (n / 2).bits := by
          rw [hn_eq, Nat.bit0_bits _ h_div_ne]
        rw [h_bits_eq]
        simp [hmod_zero]
        exact ih (n / 2) h_div
