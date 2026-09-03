import FormalConjecturesUtil

/-! Analytic reductions explored for Erdős problem 713. These do not settle the conjecture. -/

open Filter Asymptotics
open scoped Topology

namespace Erdos713Exploration

-- Integer-valued sequences can have exact asymptotic equivalents with
-- arbitrary positive real exponents. Thus integrality alone is insufficient.
theorem floor_power_equivalent (a : ℝ) (ha : 0 < a) :
    IsEquivalent atTop
      (fun n : ℕ => (Nat.floor ((n : ℝ) ^ a) : ℝ))
      (fun n : ℕ => (n : ℝ) ^ a) := by
  exact isEquivalent_nat_floor.comp_tendsto
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

theorem irrational_integer_sequence :
    ∃ (a : ℝ) (f : ℕ → ℕ), a ∈ Set.Ico 1 2 ∧
      a ∉ Set.range ((↑) : ℚ → ℝ) ∧
      IsEquivalent atTop (fun n => (f n : ℝ))
        (fun n : ℕ => (n : ℝ) ^ a) := by
  refine ⟨Real.sqrt 2, fun n => Nat.floor ((n : ℝ) ^ Real.sqrt 2), ?_, ?_, ?_⟩
  · constructor
    · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  · exact irrational_sqrt_two
  · exact floor_power_equivalent _ (Real.sqrt_pos.2 (by norm_num))



theorem exponent_le_of_isBigO {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  obtain ⟨C, _, hC⟩ := h.exists_pos
  have hdiv : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (a - b) ≤ C := by
    filter_upwards [hC.bound, eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hnp
    rw [Real.rpow_sub hnpos, div_le_iff₀ (Real.rpow_pos_of_pos hnpos b)]
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] using hn
  have htop : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hba)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hn'⟩ := (hdiv.and (htop.eventually_gt_atTop C)).exists
  exact (not_lt_of_ge hn) hn'

theorem exponent_unique {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a = b :=
  le_antisymm (exponent_le_of_isBigO h.1) (exponent_le_of_isBigO h.2)

-- A rational-power Theta estimate suffices; the missing step for general
-- forbidden bipartite graphs is precisely obtaining such an estimate.
theorem rational_of_rational_power_bound {a c : ℝ} {f : ℕ → ℝ}
    (hc : c ≠ 0)
    (h : IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ) ^ a))
    (hr : ∃ r : ℚ, f =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ (r : ℝ))) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r, hr⟩ := hr
  exact ⟨r, (exponent_unique ((h.isTheta.of_const_mul_right hc).symm.trans hr)).symm⟩

theorem rationality_iff_rational_power_bound {a c : ℝ} {f : ℕ → ℝ}
    (hc : c ≠ 0)
    (h : IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ) ^ a)) :
    a ∈ Set.range ((↑) : ℚ → ℝ) ↔
      ∃ r : ℚ, f =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ (r : ℝ)) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, h.isTheta.of_const_mul_right hc⟩
  · exact rational_of_rational_power_bound hc h

end Erdos713Exploration

#print axioms Erdos713Exploration.irrational_integer_sequence
#print axioms Erdos713Exploration.rationality_iff_rational_power_bound
