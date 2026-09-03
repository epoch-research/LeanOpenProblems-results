import Submission.ReciprocalDivisorCounts

/-! Good rational approximants to the original slope, at scales obtained from
an approximant to its reciprocal. All denominator losses are fixed in α. -/
namespace Erdos972InverseGoodApproximation

open Erdos972PrimeRotation Erdos972ReciprocalDivisorCounts

set_option maxHeartbeats 1000000

/-- A fixed constant in the approximation error can be absorbed by replacing
the approximant, with only a fixed denominator loss. -/
lemma normalize_approximant {θ : ℝ} (r : ℚ) {C : ℕ} (hC : 0 < C)
    (hr : |θ-r| ≤ (C : ℝ)/(r.den : ℝ)^2) :
    ∃ s : ℚ, r.den ≤ 2*C*s.den ∧ s.den ≤ 4*C*r.den ∧
      |θ-s| ≤ 1/(s.den : ℝ)^2 := by
  let T := 4*C*r.den
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨s, hs, hsT⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hT
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hd : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC
  refine ⟨s, ?_, hsT, ?_⟩
  · by_contra hh
    have hsmall : 2*C*s.den < r.den := Nat.lt_of_not_ge hh
    by_cases he : r = s
    · subst s
      have hh : r.den ≤ 2*C*r.den := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    have hsep := rational_separation r s he
    have htri : |(r : ℝ)-s| ≤ (C : ℝ)/(r.den : ℝ)^2+1/(((T : ℝ)+1)*s.den) := by
      have hh := abs_sub_le (r : ℝ) θ (s : ℝ)
      rw [abs_sub_comm (r : ℝ) θ] at hh
      exact hh.trans (add_le_add hr hs)
    have hhalf : (C : ℝ)*s.den/r.den < 1/2 := by
      apply (div_lt_iff₀ hq).mpr
      have hh : 2*(C : ℝ)*s.den < r.den := by exact_mod_cast hsmall
      linarith only [hh]
    have hhalf' : (r.den : ℝ)/((T : ℝ)+1) < 1/2 := by
      apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ)+1)).mpr
      dsimp [T]
      push_cast
      nlinarith only [hCR, hq]
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htri hq.le) hd.le
    have he : ((C : ℝ)/(r.den : ℝ)^2+1/(((T : ℝ)+1)*s.den))*r.den*s.den =
        (C : ℝ)*s.den/r.den+(r.den : ℝ)/((T : ℝ)+1) := by field_simp
    rw [he] at hb
    linarith only [hb, hsep, hhalf, hhalf']
  · apply hs.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
    have hh : (s.den : ℝ) ≤ T := Nat.cast_le.mpr hsT
    nlinarith only [hh, hd]

/-- Both the direct and reciprocal frequency families can be treated on one
rational scale. The loss `64 J^3` is independent of that scale. -/
theorem inverse_good_approximant {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) (hq : 2*α ≤ r.den)
    {J : ℕ} (hαJ : α ≤ J) :
    ∃ s : ℚ, r.den ≤ (64*J^3)*s.den ∧ s.den ≤ (64*J^3)*r.den ∧
      |α-s| ≤ 1/(s.den : ℝ)^2 := by
  have hJ : (1 : ℝ) ≤ J := hα.trans hαJ
  have hJ0 : 0 < J := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hJ)
  have hα0 : 0 < α := by linarith
  obtain ⟨hrpos, hrlo, hrhi, herr⟩ := inverse_approximant_bounds hα r hr hq
  have hden0 : (0 : ℝ) < (r⁻¹).den := Nat.cast_pos.mpr (r⁻¹).pos
  have hq0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hbound : |α-(r⁻¹ : ℚ)| ≤ ((8*J^2 : ℕ) : ℝ)/((r⁻¹).den : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hden0)).mpr
    calc
      _ ≤ (2*α^2/(r.den : ℝ)^2)*((r⁻¹).den : ℝ)^2 := mul_le_mul_of_nonneg_right herr (sq_nonneg _)
      _ ≤ (2*α^2/(r.den : ℝ)^2)*(2*r.den)^2 := by gcongr
      _ = 8*α^2 := by field_simp; ring
      _ ≤ _ := by push_cast; gcongr
  obtain ⟨s, hslo, hshi, hs⟩ := normalize_approximant r⁻¹ (by positivity : 0 < 8*J^2) hbound
  refine ⟨s, ?_, ?_, hs⟩
  · have hqden : (r.den : ℝ) ≤ 2*α*(r⁻¹).den := by
      have hh := (div_le_iff₀ (by positivity : 0 < 2*α)).mp hrlo
      nlinarith only [hh]
    have hsloR : ((r⁻¹).den : ℝ) ≤ 16*(J : ℝ)^2*s.den := by
      have hh : ((r⁻¹).den : ℝ) ≤ 2*(8*(J : ℝ)^2)*s.den := by exact_mod_cast hslo
      nlinarith only [hh]
    have hmul := mul_le_mul_of_nonneg_left hsloR (show 0 ≤ 2*α by positivity)
    have hcoef : 32*α*(J : ℝ)^2 ≤ 64*(J : ℝ)^3 := by
      have hh := mul_le_mul_of_nonneg_right hαJ (show 0 ≤ 32*(J : ℝ)^2 by positivity)
      nlinarith only [hh, show 0 ≤ (J : ℝ)^3 by positivity]
    have hh := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) s.den)
    have hfinal : (r.den : ℝ) ≤ 64*(J : ℝ)^3*s.den := by nlinarith only [hqden, hmul, hh]
    exact_mod_cast hfinal
  · have hshiR : (s.den : ℝ) ≤ 32*(J : ℝ)^2*(r⁻¹).den := by
      have hh : (s.den : ℝ) ≤ 4*(8*(J : ℝ)^2)*(r⁻¹).den := by exact_mod_cast hshi
      nlinarith only [hh]
    have hmul := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ 32*(J : ℝ)^2 by positivity)
    have hpow : (J : ℝ)^2 ≤ (J : ℝ)^3 := pow_le_pow_right₀ hJ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 64*(r.den : ℝ) by positivity)
    have hfinal : (s.den : ℝ) ≤ 64*(J : ℝ)^3*r.den := by nlinarith only [hshiR, hmul, hh]
    exact_mod_cast hfinal

#print axioms inverse_good_approximant

end Erdos972InverseGoodApproximation
