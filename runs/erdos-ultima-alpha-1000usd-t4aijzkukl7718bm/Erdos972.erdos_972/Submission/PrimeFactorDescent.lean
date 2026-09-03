import FormalConjecturesUtil

/-! A descending-factor consequence of a nonprime output for slopes below two.
This does not prove that the prime-pair set is infinite. -/
namespace Erdos972PrimeFactorDescent

lemma prime_divisor_lt_of_nonprime {n p r : ℕ} (hn : 0 < n)
    (hbound : n < 2 * p) (hnp : ¬ n.Prime) (hr : r.Prime) (hrn : r ∣ n) :
    r < p := by
  obtain ⟨k, hk⟩ := hrn
  have hk0 : k ≠ 0 := by
    intro h
    simp only [h, Nat.mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    intro h
    simp only [h, Nat.mul_one] at hk
    exact hnp (hk.symm ▸ hr)
  have hk2 : 2 ≤ k := by omega
  have hle : 2 * r ≤ n := by
    rw [hk]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left r hk2
  omega

/-- If an input prime has a nonprime output at a slope in `[1,2)`, every
prime factor of its output is strictly smaller than the input. -/
theorem output_prime_factor_lt {α : ℝ} {p r : ℕ}
    (hα : 1 ≤ α) (hα2 : α < 2) (hp : p.Prime)
    (hout : ¬ (⌊α * p⌋₊).Prime) (hr : r.Prime) (hrout : r ∣ ⌊α * p⌋₊) :
    r < p := by
  have hpq : p ≤ ⌊α * p⌋₊ := Nat.le_floor (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg p))
  have hq0 : 0 < ⌊α * p⌋₊ := hp.pos.trans_le hpq
  have hfloor : (⌊α * p⌋₊ : ℝ) ≤ α * p := Nat.floor_le (by positivity)
  have hbound : ⌊α * p⌋₊ < 2 * p := by
    have hmul := mul_lt_mul_of_pos_right hα2 (Nat.cast_pos.mpr hp.pos)
    exact_mod_cast hfloor.trans_lt hmul
  exact prime_divisor_lt_of_nonprime hq0 hbound hout hr hrout

/-- This is an explicit consequence of an eventual no-pair hypothesis, not
an assertion that such a hypothesis is possible or impossible. -/
theorem eventual_descending_factors {α : ℝ} {B : ℕ}
    (hα : 1 ≤ α) (hα2 : α < 2)
    (hbad : ∀ p : ℕ, B < p → p.Prime → ¬ (⌊α * p⌋₊).Prime) :
    ∀ p : ℕ, B < p → p.Prime →
      ∀ r : ℕ, r.Prime → r ∣ ⌊α * p⌋₊ → r < p := by
  intro p hBp hp r hr hd
  exact output_prime_factor_lt hα hα2 hp (hbad p hBp hp) hr hd

#print axioms output_prime_factor_lt
#print axioms eventual_descending_factors
end Erdos972PrimeFactorDescent
