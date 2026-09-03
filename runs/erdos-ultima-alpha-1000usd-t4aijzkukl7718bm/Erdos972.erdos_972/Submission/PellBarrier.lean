import FormalConjecturesUtil

/-!
An exact obstruction to using a prime denominator alone in the
Diophantine-approximation approach. This does not settle Erdős 972.
-/

namespace Erdos972PellBarrier

lemma denominator_prime : Nat.Prime 5741 := by norm_num

lemma numerator_composite : ¬ Nat.Prime 8119 := by norm_num

lemma pell_identity : 8119 ^ 2 + 1 = 2 * 5741 ^ 2 := by norm_num

lemma sqrt_bounds : (8119 : ℝ) < Real.sqrt 2 * 5741 ∧
    Real.sqrt 2 * 5741 < 8120 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

lemma floor_sqrt_two_mul : ⌊Real.sqrt 2 * 5741⌋₊ = 8119 := by
  apply (Nat.floor_eq_iff' (by norm_num : 8119 ≠ 0)).mpr
  constructor
  · exact sqrt_bounds.1.le
  · norm_num only [Nat.cast_ofNat]
    exact sqrt_bounds.2

lemma prime_input_composite_output :
    Nat.Prime 5741 ∧ ¬ Nat.Prime ⌊Real.sqrt 2 * 5741⌋₊ := by
  rw [floor_sqrt_two_mul]
  exact ⟨denominator_prime, numerator_composite⟩

#print axioms prime_input_composite_output


lemma good_approximation :
    |Real.sqrt 2 - (8119 : ℝ) / 5741| < 1 / (5741 : ℝ) ^ 2 := by
  have hlo : (8119 : ℝ) / 5741 < Real.sqrt 2 := by
    linarith [sqrt_bounds.1]
  have hhi : Real.sqrt 2 < (8119 : ℝ) / 5741 + 1 / (5741 : ℝ) ^ 2 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  rw [abs_of_pos (sub_pos.mpr hlo)]
  linarith

/-- A prime denominator and a one-sided error below `1/p²` do not, by themselves,
force the numerator to be prime. This is not a disproof of Erdős 972. -/
theorem prime_denominator_not_sufficient :
    ¬ (∀ α : ℝ, 1 < α → Irrational α → ∀ p q : ℕ,
      p.Prime → (q : ℝ) / p < α →
      |α - (q : ℝ) / p| < 1 / (p : ℝ) ^ 2 → q.Prime) := by
  intro h
  have hα : 1 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hlo : (8119 : ℝ) / 5741 < Real.sqrt 2 := by
    linarith [sqrt_bounds.1]
  exact numerator_composite
    (h (Real.sqrt 2) hα irrational_sqrt_two 5741 8119 denominator_prime hlo
      good_approximation)

#print axioms prime_denominator_not_sufficient

end Erdos972PellBarrier
