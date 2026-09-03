import Submission.AffinePotentialCertificates

/-! A critical-rate criterion with an unbounded subtractive correction.
No potential satisfying its hypotheses is supplied. This is not a
settlement of Erdős 406. -/

namespace Erdos406CriticalRate
open Filter Erdos406AffineCertificate Erdos406AffinePotential

lemma orbit_growth_lower (V : ℕ → ℝ)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1)) (t : ℕ) :
    V 0 + (t : ℝ) ≤ V (orbit 4 1 t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hh := hgrow (orbit 4 1 t)
    rw [orbit_succ]
    push_cast
    linarith

lemma critical_orbit_length (c : ℝ) (hc : 0 ≤ c)
    (hcrit : c * Real.log 4 ≤ Real.log 3) (t : ℕ) :
    c * (Nat.digits 3 (orbit 4 1 t)).length ≤ (t : ℝ) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlen := mul_le_mul_of_nonneg_left (orbit_length_log_le t) hc
  have hr := mul_le_mul_of_nonneg_left hcrit (show (0 : ℝ) ≤ t by positivity)
  nlinarith

/-- At the critical slope a correction tending to infinity would suffice.
The good-word upper bound is not assumed on arbitrary integers. -/
theorem critical_affine_criterion (V : ℕ → ℝ) (c B : ℝ) (g : ℕ → ℝ)
    (hc : 0 ≤ c) (hcrit : c * Real.log 4 ≤ Real.log 3)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n + g (Nat.digits 3 n).length ≤ c * (Nat.digits 3 n).length + B)
    (hdiverge : Tendsto g atTop atTop) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have hcorrection (t : ℕ) (hg : Nat.digits 3 (orbit 4 1 t) ⊆ [0, 1]) :
      g (Nat.digits 3 (orbit 4 1 t)).length ≤ B - V 0 := by
    have hl := orbit_growth_lower V hgrow t
    have hu := hgood _ hg
    have hc' := critical_orbit_length c hc hcrit t
    linarith
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (hdiverge.eventually (eventually_gt_atTop (B - V 0)))
  apply Erdos406SingleAffine.single_affine_criterion
  apply Set.finite_iff_bddAbove.mpr
  refine ⟨3 ^ L, ?_⟩
  rintro n ⟨⟨t, rfl⟩, hg⟩
  have hlen : (Nat.digits 3 (orbit 4 1 t)).length < L := by
    by_contra hn
    have hh := hL (Nat.digits 3 (orbit 4 1 t)).length (by omega)
    have hh' := hcorrection t hg
    linarith
  exact (Nat.lt_base_pow_length_digits (by decide : 1 < 3)).le.trans
    (Nat.pow_le_pow_right (by decide : 0 < 3) hlen.le)

#print axioms critical_affine_criterion
end Erdos406CriticalRate
