import FormalConjectures.Util.ProblemImports

open Nat Real

lemma primeCounting_eq_of_not_prime {a b : ℕ} (h_le : a ≤ b) (h_not_prime : ∀ x, a < x ∧ x ≤ b → ¬ Nat.Prime x) : Nat.primeCounting b = Nat.primeCounting a := by
  induction' b with b ih
  · simp only [Nat.le_zero.mp h_le]
  · by_cases h_eq : a = b + 1
    · rw [h_eq]
    · have h_lt : a ≤ b := by omega
      have h_not_prime_b : ∀ x, a < x ∧ x ≤ b → ¬ Nat.Prime x := by
        intro x hx
        exact h_not_prime x ⟨hx.1, hx.2.trans (by omega)⟩
      have h_ih := ih h_lt h_not_prime_b
      have h_not_prime_succ : ¬ Nat.Prime (b + 1) := by
        exact h_not_prime (b + 1) ⟨by omega, by omega⟩
      change Nat.count Nat.Prime (b + 1 + 1) = Nat.count Nat.Prime (a + 1)
      rw [Nat.count_succ_eq_count h_not_prime_succ]
      exact h_ih

theorem interval_test : Nat.primeCounting 1000006 = Nat.primeCounting 1000003 := by
  apply primeCounting_eq_of_not_prime (by norm_num)
  intro x hx
  rcases hx with ⟨hl, hu⟩
  interval_cases x <;> norm_num


theorem test_full_interval : Nat.primeCounting 22710142746748 = Nat.primeCounting 22710142746256 := by
  apply primeCounting_eq_of_not_prime (by norm_num)
  intro x hx
  rcases hx with ⟨hl, hu⟩
  interval_cases x <;> norm_num


theorem test_sq_lt_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a^2 < b^2 := by
  nlinarith




theorem test_floor_eq {x : ℝ} (h1 : (22710142746748 : ℝ) ≤ x) (h2 : x < (22710142746748 : ℝ) + 1) :
    Int.floor x = (22710142746748 : ℤ) := by
  rw [Int.floor_eq_iff]
  exact ⟨h1, h2⟩


theorem test_to_nat : Int.toNat (22710142746748 : ℤ) = 22710142746748 := by
  rfl







