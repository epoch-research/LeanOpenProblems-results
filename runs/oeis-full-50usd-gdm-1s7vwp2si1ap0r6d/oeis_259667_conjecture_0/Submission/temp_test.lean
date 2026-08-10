import Mathlib

set_option maxRecDepth 200000

def has_two_fuel : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if n = 0 then false
    else if n % 3 = 2 then true
    else has_two_fuel fuel (n / 3)

lemma has_two_fuel_spec (fuel : ℕ) (n : ℕ) (h : has_two_fuel fuel n = true) :
    ∃ i < fuel, n / 3^i % 3 = 2 := by
  induction fuel generalizing n with
  | zero =>
    simp [has_two_fuel] at h
  | succ fuel ih =>
    simp [has_two_fuel] at h
    rcases h with ⟨h_nz, h_or⟩
    rcases h_or with h_mod | h_rec
    · use 0
      refine ⟨by omega, ?_⟩
      rw [pow_zero, Nat.div_one]
      exact h_mod
    · obtain ⟨j, hj_lt, hj_eq⟩ := ih (n / 3) h_rec
      use j + 1
      refine ⟨by omega, ?_⟩
      have h_pow_succ : 3^(j+1) = 3 * 3^j := by ring
      rw [h_pow_succ]
      rw [Nat.div_div_eq_div_mul] at hj_eq
      exact hj_eq

