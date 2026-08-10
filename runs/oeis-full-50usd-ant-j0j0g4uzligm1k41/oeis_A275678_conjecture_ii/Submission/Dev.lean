import FormalConjectures.Util.ProblemImports

open Nat

-- Hard lemmas (three-square content), to be proven later.
-- L2: m ≡ 1 mod 4  →  m = 4x²+y²+z² with x ≤ z
axiom L2 : ∀ m : ℕ, m % 4 = 1 → ∃ x y z : ℕ, m = 4*x^2 + y^2 + z^2 ∧ x ≤ z
-- L3: m ≡ 2 mod 4  →  m = 4x²+y²+z² with x ≤ z
axiom L3 : ∀ m : ℕ, m % 4 = 2 → ∃ x y z : ℕ, m = 4*x^2 + y^2 + z^2 ∧ x ≤ z
-- L1: n ≡ 1 mod 4, n > 1  →  n = 4(1+4x²+y²)+z² with x ≤ z
axiom L1 : ∀ n : ℕ, n % 4 = 1 → 1 < n → ∃ x y z : ℕ, n = 4*(1 + 4*x^2 + y^2) + z^2 ∧ x ≤ z

theorem main (n : ℕ) (hn : n > 0) :
    ∃ k x y z : ℕ, n = 4^k * (1 + 4 * x^2 + y^2) + z^2 ∧ x ≤ z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- case split on n % 4
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · -- 4 ∣ n
      have hdvd : 4 ∣ n := Nat.dvd_of_mod_eq_zero h
      obtain ⟨n', rfl⟩ := hdvd
      have hn' : n' > 0 := by
        rcases Nat.eq_zero_or_pos n' with h0 | h0
        · simp [h0] at hn
        · exact h0
      have hlt : n' < 4 * n' := by omega
      obtain ⟨k, x, y, z, heq, hxz⟩ := ih n' hlt hn'
      refine ⟨k+1, x, y, 2*z, ?_, by omega⟩
      rw [heq]; ring
    · -- n ≡ 1 mod 4
      rcases Nat.lt_or_ge 1 n with hgt | hle
      · obtain ⟨x, y, z, heq, hxz⟩ := L1 n h hgt
        exact ⟨1, x, y, z, by rw [heq]; ring, hxz⟩
      · -- n ≤ 1 and n % 4 = 1 means n = 1
        interval_cases n
        exact ⟨0, 0, 0, 0, by ring, by omega⟩
    · -- n ≡ 2 mod 4
      have hn1 : n = (n-1) + 1 := by omega
      have hm : (n-1) % 4 = 1 := by omega
      obtain ⟨x, y, z, heq, hxz⟩ := L2 (n-1) hm
      refine ⟨0, x, y, z, ?_, hxz⟩
      rw [hn1, heq]; ring
    · -- n ≡ 3 mod 4
      have hn1 : n = (n-1) + 1 := by omega
      have hm : (n-1) % 4 = 2 := by omega
      obtain ⟨x, y, z, heq, hxz⟩ := L3 (n-1) hm
      refine ⟨0, x, y, z, ?_, hxz⟩
      rw [hn1, heq]; ring
