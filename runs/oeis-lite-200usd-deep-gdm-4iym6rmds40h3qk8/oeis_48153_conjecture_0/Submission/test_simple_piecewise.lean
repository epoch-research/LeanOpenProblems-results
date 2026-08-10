import FormalConjectures.Util.ProblemImports

open Finset

lemma k_sq_div_simple_piecewise (n k : ℕ) (hn : 5 ≤ n) (hk : k < n) : 3 * (k^2 / n) ≥ if k ≥ n / 2 then 2 * k - n else 0 := by
  split_ifs with h
  · by_cases h_ge : 2 * k ≥ n
    · have h_div : k^2 = n * (k^2 / n) + k^2 % n := (Nat.div_add_mod (k^2) n).symm
      have h_mod_lt : k^2 % n < n := Nat.mod_lt _ (by omega)
      have h_eq : n * (3 * (k^2 / n)) ≥ n * (2 * k - n) := by
        have h_int : (((n * (3 * (k^2 / n)) : ℕ) : ℤ) ≥ (((n * (2 * k - n) : ℕ) : ℤ))) := by
          have h1 : (((n * (3 * (k^2 / n)) : ℕ) : ℤ)) = 3 * ((n : ℤ) * ((k^2 / n : ℕ) : ℤ)) := by push_cast; ring
          have h2 : (((n * (2 * k - n) : ℕ) : ℤ)) = 2 * (k : ℤ) * (n : ℤ) - (n : ℤ)^2 := by
            push_cast
            have : ((2 * k - n : ℕ) : ℤ) = 2 * (k : ℤ) - (n : ℤ) := Nat.cast_sub h_ge
            rw [this]
            ring
          rw [h1, h2]
          have h3 : (n : ℤ) * ((k^2 / n : ℕ) : ℤ) = (k : ℤ)^2 - ((k^2 % n : ℕ) : ℤ) := by
            have h_cast_div : ((k^2 : ℕ) : ℤ) = (n : ℤ) * ((k^2 / n : ℕ) : ℤ) + ((k^2 % n : ℕ) : ℤ) := by exact_mod_cast h_div
            have h_cast_sq : ((k^2 : ℕ) : ℤ) = (k : ℤ)^2 := by push_cast; rfl
            omega
          rw [h3]
          have h4 : ((k^2 % n : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast h_mod_lt
          nlinarith
        exact_mod_cast h_int
      have hn_pos : n > 0 := by omega
      exact Nat.le_of_mul_le_mul_left h_eq hn_pos
    · have : 2 * k - n = 0 := by omega
      rw [this]
      omega
  · omega
