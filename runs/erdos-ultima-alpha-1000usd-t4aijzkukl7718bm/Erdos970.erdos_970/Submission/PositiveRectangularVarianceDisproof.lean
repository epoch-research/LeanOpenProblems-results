import Submission.PositiveRectangularVariance
import Submission.PrimeCountingLeadingObstruction
import Submission.FirstHitCubeBridge
import Submission.PrimeCountingPowerSavingObstruction

/-! Disproof of the auxiliary uniform POSITIVE-part rectangular variance-cube
proposal. This file does not negate the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages
open Finset Real Filter FiniteSelberg
open scoped Topology

lemma prime_prefix_density_three_fifths (p : ℕ) (hp : p.Prime)
    (hLp : 30*firstHitProfileError ≤ log (p : ℝ)) :
    density p.primesBelow ≤ (3/5 : ℝ)/log (p : ℝ) := by
  have hlog : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hLp1 : 1 ≤ log (p : ℝ) := by linarith [firstHitProfileError_ge_one]
  have hN : p ≤ p^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos (show 1 ≤ 3 by omega)
  have hn := strict_normalizer_lower_through_cube p (p^3) hp hN hLp1 3
    (by norm_num) le_rfl (by rw [Nat.cast_pow, log_pow]; norm_num)
  change firstHitProfile 3*log (p : ℝ) - _ - 3 ≤ _ at hn
  have hg := mul_le_mul_of_nonneg_right firstHitProfile_three_ge hlog.le
  have hlo : (5/3 : ℝ)*log (p : ℝ) ≤ primeNormalizer p.primesBelow (p^3) := by
    unfold firstHitProfileError at hLp
    linarith
  have hP : ∀ q ∈ p.primesBelow, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  have ht := eulerMass_sub_normalizer_eq_tail p.primesBelow hP (p^3)
  have hu : primeNormalizer p.primesBelow (p^3) ≤ eulerMass p.primesBelow := by
    have hnonneg : 0 ≤ ∑ Q ∈ p.primesBelow.powerset with p^3 < ∏ q ∈ Q, q,
        primeWeight Q := by
      apply sum_nonneg
      intro Q hQ
      exact primeWeight_nonneg Q (fun q hq => hP q ((mem_powerset.mp (mem_filter.mp hQ).1) hq))
    linarith
  have hδ := density_pos p.primesBelow hP
  have he : density p.primesBelow * eulerMass p.primesBelow = 1 := by
    unfold density eulerMass
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    exact mul_inv_cancel₀ (prime_density_pos (hP q hq)).ne'
  have hh := mul_le_mul_of_nonneg_left (hlo.trans hu) hδ.le
  rw [he] at hh
  apply (le_div_iff₀ hlog).mpr
  nlinarith only [hh]

lemma positive_rectangle_power_budget (C : ℝ) (hC : 1 ≤ C) (t p : ℕ)
    (hp : p ≤ 2*t^30) :
    (p : ℝ)^3*(C*(t^48 : ℕ)^4) ≤ (2*C*(t : ℝ)^47)^6 := by
  have hC0 : 0 ≤ C := by linarith
  have hC6 : C ≤ C^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (show 1 ≤ 6 by omega)
  have hpR : (p : ℝ) ≤ 2*(t : ℝ)^30 := by exact_mod_cast hp
  calc
    _ ≤ (2*(t : ℝ)^30)^3 * (C*((t : ℝ)^48)^4) := by push_cast; gcongr
    _ = 8*C*(t : ℝ)^282 := by ring
    _ ≤ 64*C^6*(t : ℝ)^282 := by gcongr; nlinarith only [hC6, hC0]
    _ = _ := by ring

/-- An eventual positive-part cube bound would force a leading coefficient
24/25 for prime counts, apart from a lower-order error. -/
lemma prime_count_power_of_positive_cube (C : ℝ) (hC : 1 ≤ C)
    (hvar : UniformPositiveRectangularCubeBound C) (t : ℕ) (ht : 2 ≤ t)
    (hLt : firstHitProfileError ≤ log (t : ℝ)) :
    ((t^48).primeCounting : ℝ) * log (t^48 : ℕ) ≤
      (24/25 : ℝ)*(t : ℝ)^48 + 48*(4*C+2)*(t : ℝ)^47*log t := by
  have ht0 : 0 < t := by omega
  have ht1 : 1 ≤ t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hlogt : 0 < log (t : ℝ) := log_pos (by exact_mod_cast ht)
  obtain ⟨p,hp,hyp,hpy⟩ := Nat.exists_prime_lt_and_le_two_mul (t^30) (by positivity)
  let P := p.primesBelow
  have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  have hlt : ∀ q ∈ P, q < p := fun q hq => Nat.lt_of_mem_primesBelow hq
  have hc : ∀ q ∈ P, p.Coprime q := fun q hq =>
    (Nat.coprime_primes hp (hP q hq)).mpr (ne_of_gt (hlt q hq))
  have ht30 : 8 ≤ t^30 := by
    have hh := Nat.pow_le_pow_left ht 30
    norm_num at hh
    omega
  have hp8 : 8 ≤ p := by omega
  have ht18 : 2 ≤ t^18 := by
    exact ht.trans (Nat.le_self_pow (by omega : 18 ≠ 0) t)
  have hpn : p ≤ t^48 := by
    have hid : t^48 = t^30*t^18 := by ring
    rw [hid]
    exact hpy.trans (by nlinarith)
  have hnpsq : t^48 ≤ p^2 := by
    have hh : t^48 ≤ t^60 := Nat.pow_le_pow_right ht0 (by omega)
    have hh' : (t^30)^2 ≤ p^2 := Nat.pow_le_pow_left hyp.le 2
    have hid : (t^30)^2 = t^60 := by ring
    rw [hid] at hh'
    exact hh.trans hh'
  have hlogp : 30*log (t : ℝ) ≤ log (p : ℝ) := by
    have hh := log_le_log (pow_pos htR 30) (show (t : ℝ)^30 ≤ p by exact_mod_cast hyp.le)
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hδ := prime_prefix_density_three_fifths p hp (by linarith)
  have hδ0 := density_pos P hP
  have hlogp0 : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hδp : density P * log (p : ℝ) ≤ 3/5 := (le_div_iff₀ hlogp0).mp hδ
  have hδt : density P*(48*log (t : ℝ)) ≤ 24/25 := by
    have hh := mul_le_mul_of_nonneg_left hlogp hδ0.le
    nlinarith only [hh,hδp]
  have hrough := roughCount_upper_of_positive_variance_cube P hP (t^48) p hp8 hc
    C (2*C*(t : ℝ)^47) (by positivity) (positive_rectangle_power_budget C hC t p hpy)
    (fun j => hvar P hP p hp hlt (t^48*p^j)
      (hpn.trans (Nat.le_mul_of_pos_right _ (pow_pos hp.pos j))) (zeroPhase P hP))
  have he := roughCount_primesBelow_eq p (t^48) (by omega) hpn hnpsq
  change roughCount P _ = _ at he
  rw [he] at hrough
  have hpi := PrimeCountingDyadic.primeCounting_le_primeCounting'_add_one (t^48)
  have hpiR : ((t^48).primeCounting : ℝ) ≤ (t^48).primeCounting' + 1 := by exact_mod_cast hpi
  have hpcount : (p.primeCounting' : ℝ) ≤ 2*(t : ℝ)^47 := by
    have hh : p.primeCounting' ≤ p := Nat.count_le _
    have hpow := Nat.pow_le_pow_right ht0 (show 30 ≤ 47 by omega)
    exact_mod_cast hh.trans (hpy.trans (Nat.mul_le_mul_left 2 hpow))
  have hcount : ((t^48).primeCounting : ℝ) ≤
      (t : ℝ)^48*density P+(4*C+2)*(t : ℝ)^47 := by
    push_cast at hrough
    nlinarith only [hrough,hpiR,hpcount]
  have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 48*log (t : ℝ) by positivity)
  have hmain := mul_le_mul_of_nonneg_left hδt (pow_nonneg htR.le 48)
  rw [Nat.cast_pow, log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hmul,hmain]

/-- The positive-part bound is also impossible. This negates only the named
auxiliary variance proposal, not Erdős 970. -/
theorem not_uniformPositiveRectangularCubeBound (C : ℝ) :
    ¬UniformPositiveRectangularCubeBound C := by
  intro hC
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hv : UniformPositiveRectangularCubeBound D := hC.mono (le_max_left _ _)
  have hlim : Tendsto (fun t : ℕ => log (t : ℝ)/(t : ℝ)) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
    simp only [rpow_one] at hh
    exact hh.comp tendsto_natCast_atTop_atTop
  have hε : 0 < 1/(2400*(4*D+2)) := by positivity
  have hlogtop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply PrimeLeading.not_eventually_theta_power 48 (by omega) (49/50) (by norm_num) (by norm_num)
  filter_upwards [hlim.eventually_le_const hε,
    hlogtop.eventually_ge_atTop firstHitProfileError, eventually_ge_atTop 2] with t htε htL ht
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have he := (div_le_iff₀ htR).mp htε
  have hden : 0 < 2400*(4*D+2) := by positivity
  have he' : 2400*(4*D+2)*log (t : ℝ) ≤ t := by
    have hh := mul_le_mul_of_nonneg_right he hden.le
    field_simp at hh
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_right he' (pow_nonneg htR.le 47)
  have hid : (t : ℝ)^48 = (t : ℝ)^47*t := by ring
  have hh := prime_count_power_of_positive_cube D hD hv t ht htL
  have hθ := PrimeLeading.theta_le_primeCounting_mul_log (t^48)
  rw [hid]
  nlinarith only [hh,hθ,hm,hid]

#print axioms prime_prefix_density_three_fifths
#print axioms prime_count_power_of_positive_cube
#print axioms not_uniformPositiveRectangularCubeBound
end Erdos970.GapAverages
