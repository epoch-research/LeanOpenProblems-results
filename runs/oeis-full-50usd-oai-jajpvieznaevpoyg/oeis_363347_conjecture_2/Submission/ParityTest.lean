import FormalConjectures.Util.ProblemImports
example (m p : ℕ) (hpodd : p % 2 = 1) (hm4 : 4 ≤ m) (hraw : m*m - 5 = p*2) : False := by
  have hmpar : m % 2 = 0 ∨ m % 2 = 1 := Nat.mod_two_eq_zero_or_one m
  rcases hmpar with hme | hmo
  · have hm2 : (m*m) % 2 = 0 := by rw [Nat.mul_mod, hme]
    have hleft : (m*m - 5) % 2 = 1 := by omega
    have hright : (p*2) % 2 = 0 := by omega
    rw [hraw, hright] at hleft
    norm_num at hleft
  · have h4cases : m % 4 = 1 ∨ m % 4 = 3 := by omega
    have hsq4 : (m*m) % 4 = 1 := by
      rcases h4cases with h1 | h3
      · rw [Nat.mul_mod, h1]
      · rw [Nat.mul_mod, h3]
    have hleft : (m*m - 5) % 4 = 0 := by omega
    have hp4cases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    have hright : (p*2) % 4 = 2 := by
      rcases hp4cases with h1 | h3
      · rw [Nat.mul_mod, h1]
      · rw [Nat.mul_mod, h3]
    rw [hraw, hright] at hleft
    norm_num at hleft
