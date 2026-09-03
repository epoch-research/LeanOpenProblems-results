import Submission.NonFanoBlowup
import Submission.AsymptoticObstruction

/-!
# A verified frequent lower bound for the non-Fano extremal number

The lower half of the oscillation criterion is proved here. The upper half
remains an explicit hypothesis: these results do not settle `Spec.lean`.
-/

open Filter Asymptotics

namespace Erdos713

private theorem doubled_polarity_normalized_lower {q : ℝ} (hq : 4 ≤ q) :
    (1 / Real.sqrt 2) * (2 * (q^2 + q + 1))^(3 / 2 : ℝ) ≤ 2 * q * (q + 1)^2 := by
  have hq0 : 0 ≤ q := by linarith
  have ht : 0 ≤ q - 4 := by linarith
  have hpos : 0 ≤ (q - 4)^5 + 20 * (q - 4)^4 + 157 * (q - 4)^3 +
      599 * (q - 4)^2 + 1093 * (q - 4) + 739 := by positivity
  have hpoly : (2 * (q^2 + q + 1))^3 ≤ 2 * (2 * q * (q + 1)^2)^2 := by
    nlinarith only [hpos]
  have hn : 0 ≤ 2 * (q^2 + q + 1) := by positivity
  have hpow : ((2 * (q^2 + q + 1))^(3 / 2 : ℝ))^2 =
      (2 * (q^2 + q + 1))^3 := by
    calc
      _ = (2 * (q^2 + q + 1))^((3 / 2 : ℝ) * 2) := by
        rw [Real.rpow_mul hn, Real.rpow_two]
      _ = _ := by norm_num
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  apply (sq_le_sq₀ (Real.rpow_nonneg hn _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  rw [hpow, mul_pow (2 * q * (q + 1)^2) (Real.sqrt 2) 2,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [hpoly]

/-- Infinitely often, the ordinary non-Fano extremal number is at least
`(1/√2) n^(3/2)`. The explicit witnesses are doubled polarity graphs. -/
theorem nonFano_extremal_frequently_ge :
    ∃ᶠ n : ℕ in atTop,
      (1 / Real.sqrt 2) * (n : ℝ)^(3 / 2 : ℝ) ≤
        (SimpleGraph.extremalNumber n nonFanoGraph : ℝ) := by
  rw [frequently_atTop]
  intro m
  let k := m + 2
  let q := 2^k
  have h4 : 4 ≤ q := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ k by dsimp [k]; omega)
    exact h
  have hm : m < q := by
    have h : k < 2^k := Nat.lt_two_pow_self
    dsimp [k, q] at *
    omega
  refine ⟨2 * (q^2 + q + 1), by omega, ?_⟩
  have hE := nonFano_extremal_lower_doubled_power_two k (by dsimp [k]; omega)
  have hE' : (2 * q * (q + 1)^2 : ℕ) ≤
      SimpleGraph.extremalNumber (2 * (q^2 + q + 1)) nonFanoGraph := hE
  have hbound := doubled_polarity_normalized_lower (q := (q : ℝ)) (by exact_mod_cast h4)
  have hbound' : (1 / Real.sqrt 2) * ((2 * (q^2 + q + 1) : ℕ) : ℝ)^(3 / 2 : ℝ) ≤
      ((2 * q * (q + 1)^2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hbound
  exact hbound'.trans (by exact_mod_cast hE')

/-- Only a frequent *unrestricted* upper bound with a smaller coefficient is
now needed for this candidate. No such upper bound is asserted here. -/
theorem nonFano_not_power_equivalent_of_frequent_upper
    {b : ℝ} (hb : 0 ≤ b) (hgap : b < 1 / Real.sqrt 2)
    (hlow : ∃ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n nonFanoGraph : ℝ) ≤ b * (n : ℝ)^(3 / 2 : ℝ)) :
    ¬ ∃ α c : ℝ, α ∈ Set.Ico 1 2 ∧ 0 < c ∧
      IsEquivalent atTop (fun n : ℕ => (SimpleGraph.extremalNumber n nonFanoGraph : ℝ))
        (fun n : ℕ => c * (n : ℝ)^α) :=
  extremalNumber_not_power_equivalent_of_frequent_gap nonFanoGraph hb hgap
    nonFano_extremal_frequently_ge hlow

end Erdos713

#print axioms Erdos713.nonFano_extremal_frequently_ge
#print axioms Erdos713.nonFano_not_power_equivalent_of_frequent_upper
