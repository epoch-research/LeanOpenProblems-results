import Submission.PolynomialRowScales
import Submission.DivisorPairCount

/-! Joint divisibility counts at the same reciprocal rational scales used for
the one-prime Beatty-row estimates. -/
namespace Erdos972ReciprocalDivisorCounts

open Finset ArithmeticFunction
open Erdos972PrimeRotation Erdos972DivisorPairCount

set_option maxHeartbeats 1000000

lemma inverse_approximant_bounds {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) (hq : 2*α ≤ r.den) :
    0 < r⁻¹ ∧ (r.den : ℝ)/(2*α) ≤ (r⁻¹).den ∧
      ((r⁻¹).den : ℝ) ≤ 2*r.den ∧ |α-(r⁻¹ : ℚ)| ≤ 2*α^2/(r.den : ℝ)^2 := by
  have hα0 : 0 < α := by linarith
  have hq0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hsq : 2*α ≤ (r.den : ℝ)^2 := by nlinarith only [hq, hq1]
  have hsmall : |1/α-r| ≤ 1/(2*α) :=
    hr.trans (one_div_le_one_div_of_le (by positivity) hsq)
  have hrlo : 1/(2*α) ≤ (r : ℝ) := by
    have he : 1/α = 2*(1/(2*α)) := by field_simp
    linarith only [(abs_le.mp hsmall).2, he]
  have hrpos : (0 : ℝ) < r := (by positivity : (0 : ℝ) < 1/(2*α)).trans_le hrlo
  have hrposQ : 0 < r := by exact_mod_cast hrpos
  have hrhi : (r : ℝ) ≤ 2 := by
    have hαinv : 1/α ≤ (1 : ℝ) := (div_le_one hα0).mpr hα
    have he : |1/α-r| ≤ 1 := hr.trans ((div_le_one (by positivity)).mpr (by nlinarith only [hq1]))
    linarith only [(abs_le.mp he).1, hαinv]
  have hden : ((r⁻¹).den : ℝ) = (r : ℝ)*r.den := by
    rw [Rat.den_inv_of_ne_zero hrposQ.ne', Int.cast_natAbs, Int.cast_abs]
    have he : (r.num : ℝ) = (r : ℝ)*r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
    rw [he, abs_of_nonneg (mul_nonneg hrpos.le hq0.le)]
  refine ⟨inv_pos.mpr hrposQ, ?_, ?_, ?_⟩
  · rw [hden]
    have hh := mul_le_mul_of_nonneg_right hrlo hq0.le
    simpa only [one_div_mul_eq_div] using hh
  · rw [hden]
    exact mul_le_mul_of_nonneg_right hrhi hq0.le
  · have hinv : 1/(r : ℝ) ≤ 2*α := by
      have hh := one_div_le_one_div_of_le (show 0 < 1/(2*α) by positivity) hrlo
      simpa only [one_div_one_div] using hh
    have he : α-(r⁻¹ : ℚ) = α*((r : ℝ)-1/α)*(1/(r : ℝ)) := by
      rw [Rat.cast_inv]
      field_simp
    rw [he, abs_mul, abs_mul, abs_of_nonneg hα0.le, abs_of_nonneg (show 0 ≤ 1/(r : ℝ) by positivity), abs_sub_comm (r : ℝ)]
    calc
      _ ≤ α*(1/(r.den : ℝ)^2)*(2*α) := by gcongr
      _ = _ := by ring

/-- Uniform in the input prefix and both small divisors. The approximant is
to `1/α`, so this estimate shares its scales with the prime-output row bounds. -/
theorem reciprocal_scale_divisor_bound {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) {u v X d e : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hαu : 4*α ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (hX : α*X ≤ (u : ℝ)^6) (hd : 0 < d) (hdX : d ≤ X) (he : 0 < e) (hev : e ≤ v) :
    |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(v : ℝ)*(u : ℝ)^4 := by
  have hα0 : 0 < α := by linarith
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hq0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
  have hhiR : (r.den : ℝ) ≤ 16*(u : ℝ)^4 := by exact_mod_cast hhi
  have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
  have hq : 2*α ≤ r.den := by linarith only [hαu, hu4, hloR, hα0]
  obtain ⟨hs, hslo, hshi, herror⟩ := inverse_approximant_bounds hα r hr hq
  have hs0 : (0 : ℝ) < (r⁻¹).den := Nat.cast_pos.mpr (r⁻¹).pos
  have hdenmul : (r.den : ℝ) ≤ 2*α*(r⁻¹).den := by
    have hh := (div_le_iff₀ (show 0 < 2*α by positivity)).mp hslo
    nlinarith only [hh]
  have herr : |α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2 ≤ 2*α^2 :=
    (le_div_iff₀ (sq_pos_of_pos hq0)).mp herror
  have hu8 : (u : ℝ)^8 ≤ (r.den : ℝ)^2 := by
    convert pow_le_pow_left₀ (by positivity) hloR 2 using 1 <;> ring
  have hsmall : 2*(X : ℝ)*|α-(r⁻¹ : ℚ)| ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp
    calc
      _ = 2*(X : ℝ)*(|α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2) := by ring
      _ ≤ 2*(X : ℝ)*(2*α^2) := mul_le_mul_of_nonneg_left herr (by positivity)
      _ = (4*α)*(α*X) := by ring
      _ ≤ (u : ℝ)*(u : ℝ)^6 := mul_le_mul hαu hX (by positivity) (by positivity)
      _ = (u : ℝ)^7 := by ring
      _ ≤ (u : ℝ)^8 := pow_le_pow_right₀ huR (by norm_num)
      _ ≤ (r.den : ℝ)^2 := hu8
      _ = _ := by ring
  have hh := divisorPairs_discrepancy hα0.le r⁻¹ hs.le X d e hd hdX he hsmall
  have hfirst : 8*(X : ℝ)^2*|α-(r⁻¹ : ℚ)| ≤ 16*(u : ℝ)^4 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp
    calc
      _ = 8*(X : ℝ)^2*(|α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2) := by ring
      _ ≤ 8*(X : ℝ)^2*(2*α^2) := mul_le_mul_of_nonneg_left herr (by positivity)
      _ = 16*(α*X)^2 := by ring
      _ ≤ 16*((u : ℝ)^6)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hX 2) (by norm_num)
      _ = 16*(u : ℝ)^4*(u : ℝ)^8 := by ring
      _ ≤ 16*(u : ℝ)^4*(r.den : ℝ)^2 := mul_le_mul_of_nonneg_left hu8 (by positivity)
      _ = _ := by ring
  have hsecond : 2*(X : ℝ)/((r⁻¹).den : ℝ) ≤ 4*(u : ℝ)^2 := by
    apply (div_le_iff₀ hs0).mpr
    apply (mul_le_mul_iff_left₀ hα0).mp
    calc
      _ = 2*(α*X) := by ring
      _ ≤ 2*(u : ℝ)^6 := mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = 2*(u : ℝ)^2*(u : ℝ)^4 := by ring
      _ ≤ 2*(u : ℝ)^2*r.den := mul_le_mul_of_nonneg_left hloR (by positivity)
      _ ≤ 2*(u : ℝ)^2*(2*α*(r⁻¹).den) := mul_le_mul_of_nonneg_left hdenmul (by positivity)
      _ = _ := by ring
  have hthird : 3*(e : ℝ)*(r⁻¹).den ≤ 96*(v : ℝ)*(u : ℝ)^4 := by
    calc
      _ ≤ 3*(v : ℝ)*(2*r.den) := mul_le_mul (by exact_mod_cast Nat.mul_le_mul_left 3 hev) hshi (by positivity) (by positivity)
      _ ≤ 3*(v : ℝ)*(2*(16*(u : ℝ)^4)) := by gcongr
      _ = _ := by ring
  have hu24 : (u : ℝ)^2 ≤ (u : ℝ)^4 := pow_le_pow_right₀ huR (by norm_num)
  have hu14 : (1 : ℝ) ≤ (u : ℝ)^4 := one_le_pow₀ huR
  have hv4 := mul_le_mul_of_nonneg_right hvR (pow_nonneg hu0.le 4)
  linarith only [hh, hfirst, hsecond, hthird, hu24, hu14, hv4]

lemma divisorPairs_empty_of_lt {α : ℝ} {X d e : ℕ} (hdX : X < d) : divisorPairs α X d e = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnI, hdn, hen⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hnI
  exact (not_le.mpr hdX) ((Nat.le_of_dvd hn0 hdn).trans hnX)

/-- The same bound also covers prefixes shorter than the input divisor. -/
theorem reciprocal_scale_divisor_prefix_bound {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) {u v X d e : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hαu : 4*α ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (hX : α*X ≤ (u : ℝ)^6) (hd : 0 < d) (he : 0 < e) (hev : e ≤ v) :
    |((divisorPairs α X d e).card : ℝ)-(X : ℝ)/(d*e)| ≤ 118*(v : ℝ)*(u : ℝ)^4 := by
  by_cases hdX : d ≤ X
  · exact reciprocal_scale_divisor_bound hα r hr hu hv hαu hlo hhi hX hd hdX he hev
  · have hXd : X < d := Nat.lt_of_not_ge hdX
    rw [divisorPairs_empty_of_lt hXd, card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (X : ℝ)/(d*e))]
    have hbound : (X : ℝ)/(d*e) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
      have hXdR : (X : ℝ) ≤ d := Nat.cast_le.mpr hXd.le
      nlinarith only [hXdR, heR, Nat.cast_nonneg (α := ℝ) d]
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have hh := mul_le_mul hvR (one_le_pow₀ huR (n := 4)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    nlinarith only [hbound, hh]

#print axioms reciprocal_scale_divisor_prefix_bound

end Erdos972ReciprocalDivisorCounts
