import FormalConjecturesUtil

/-!
# Comparison and uniqueness of power-law exponents

These analytic lemmas reduce the conditional rationality question to rational
Theta bounds. They do not establish such bounds for arbitrary forbidden graphs.
-/

open Filter Asymptotics

namespace Erdos713Work

lemma exponent_le_of_isBigO {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a ≤ b := by
  by_contra hab
  have hba : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (tendsto_rpow_atTop hba).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, hnC, hnpos⟩ :=
    (hC.and ((ht.eventually_gt_atTop C).and (eventually_gt_atTop 0))).exists
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : 0 < (n : ℝ) ^ b := Real.rpow_pos_of_pos hnpos' _
  simp only [Real.norm_eq_abs, abs_of_pos hpow,
    abs_of_pos (Real.rpow_pos_of_pos hnpos' a)] at hn
  rw [Real.rpow_sub hnpos'] at hnC
  exact (not_lt_of_ge ((div_le_iff₀ hpow).mpr hn)) hnC

lemma exponent_eq_of_isTheta {a b : ℝ}
    (h : (fun n : ℕ => (n : ℝ) ^ a) =Θ[atTop]
      (fun n : ℕ => (n : ℝ) ^ b)) : a = b :=
  le_antisymm (exponent_le_of_isBigO h.1) (exponent_le_of_isBigO h.2)

lemma rational_exponent_of_equivalent_of_isTheta {f : ℕ → ℝ} {a c : ℝ} {r : ℚ}
    (hc : c ≠ 0)
    (ha : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (hr : f =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ (r : ℝ))) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  have heq : a = (r : ℝ) := exponent_eq_of_isTheta
    ((ha.isTheta.of_const_mul_right hc).symm.trans hr)
  exact ⟨r, heq.symm⟩

end Erdos713Work

#print axioms Erdos713Work.exponent_le_of_isBigO
#print axioms Erdos713Work.rational_exponent_of_equivalent_of_isTheta
