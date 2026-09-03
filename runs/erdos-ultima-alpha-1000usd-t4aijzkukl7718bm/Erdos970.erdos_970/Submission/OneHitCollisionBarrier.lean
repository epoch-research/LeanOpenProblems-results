import Submission.OneHitCollisionRemainder
import Submission.LogCriticalExposureBudget

/-! The additive one-hit collision remainder is large when the mean core
population exceeds a tail modulus. This is an obstruction to discarding
that remainder, NOT a counterexample to a nonlinear void inequality or to
Erdős 970. -/
namespace Erdos970.OneHitLogConcavity
open Finset Real Filter GapAverages CoverFibers Resampling
set_option maxHeartbeats 2200000

lemma coreCollisionFraction_le_one (P R S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    coreCollisionFraction P R S ≤ 1 := by
  unfold coreCollisionFraction
  have hh := phaseMean_mono P (fun r =>
    show (if (∀ p ∈ R, Set.InjOn (fun x => x % p) (populationSurvivors S P r))
      then (0 : ℝ) else 1) ≤ 1 by split_ifs <;> norm_num)
  rwa [phaseMean_const P hP] at hh

/-- The probability of a residue-injective core phase is controlled by a
lower-count deviation whenever one tail modulus is below the mean. -/
theorem one_sub_collision_mul_gap_sq_le_variance (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m p : ℕ) (hp : p ∈ R) (hp0 : 0 < p)
    (hsmall : (p : ℝ) ≤ (m : ℝ)*density P) :
    (1-coreCollisionFraction P R (range m))*((m : ℝ)*density P-p)^2 ≤
      (m : ℝ)*density P*(1-density P) := by
  classical
  let bad := fun r : Phase P => if (∀ q ∈ R,
    Set.InjOn (fun x => x % q) (populationSurvivors (range m) P r)) then (0 : ℝ) else 1
  have hpoint (r : Phase P) :
      (1-bad r)*((m : ℝ)*density P-p)^2 ≤
        (intervalCount P m r-(m : ℝ)*density P)^2 := by
    dsimp only [bad]
    split_ifs with hr
    · have hinj := hr p hp
      have hcard := card_le_modulus_of_residue_injective
        (populationSurvivors (range m) P r) p hp0 hinj
      have hcount : intervalCount P m r ≤ p := by
        unfold intervalCount
        rw [← populationSurvivors_card]
        exact_mod_cast hcard
      norm_num only [sub_zero,one_mul]
      nlinarith only [hsmall,hcount]
    · simp only [sub_self,zero_mul]
      exact sq_nonneg _
  have hh := phaseMean_mono P hpoint
  have he : phaseMean P (fun r => (1-bad r)*((m : ℝ)*density P-p)^2) =
      (1-coreCollisionFraction P R (range m))*((m : ℝ)*density P-p)^2 := by
    have hm := phaseMean_mul P (((m : ℝ)*density P-p)^2) (fun r => 1-bad r)
    simp_rw [mul_comm (1-bad _) (((m : ℝ)*density P-p)^2)]
    rw [hm,phaseMean_sub,phaseMean_const P hP]
    change _ = (1-phaseMean P bad)*((m : ℝ)*density P-p)^2
    ring
  rw [he] at hh
  exact hh.trans (phase_variance_le P hP m)

/-- In the half-mean regime, the collision term is at least 1-O(1/mean).
The actual void probability is not estimated by this lower bound. -/
theorem collision_half_mean_lower (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m p : ℕ) (hm : 0 < m) (hp : p ∈ R) (hp0 : 0 < p)
    (hsmall : (p : ℝ) ≤ (m : ℝ)*density P/2) :
    1-4/((m : ℝ)*density P) ≤ coreCollisionFraction P R (range m) := by
  have hμ : 0 < (m : ℝ)*density P := mul_pos (by exact_mod_cast hm) (density_pos P hP)
  have hc := coreCollisionFraction_le_one P R (range m) hP
  have hh := one_sub_collision_mul_gap_sq_le_variance P R hP m p hp hp0 (by linarith)
  have hsq : (((m : ℝ)*density P)/2)^2 ≤ ((m : ℝ)*density P-p)^2 := by
    nlinarith only [hsmall,hμ]
  have hprod := mul_le_mul_of_nonneg_left hsq (by linarith only [hc] : 0 ≤ 1-coreCollisionFraction P R (range m))
  have hd : (m : ℝ)*density P*(1-density P) ≤ (m : ℝ)*density P := by
    have hd0 := (density_pos P hP).le
    nlinarith only [mul_nonneg hμ.le hd0]
  have hfin := hprod.trans (hh.trans hd)
  have hscaled : (1-coreCollisionFraction P R (range m))*((m : ℝ)*density P) ≤ 4 := by
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hfin]
  have hdiv : 1-coreCollisionFraction P R (range m) ≤ 4/((m : ℝ)*density P) :=
    (le_div_iff₀ hμ).mpr hscaled
  linarith only [hdiv]

/-- Uniformly over prime cores of cardinality at most k, at quadratic or
larger lengths the collision remainder tends to one if the tail includes
any modulus of size O(k*log(k)^d), with fixed d. Disjointness is unnecessary
for this statement about the remainder itself. -/
theorem eventually_collision_near_one (A : ℝ) (hA : 0 < A) (d : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ P R : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      (∃ p ∈ R, 0 < p ∧ (p : ℝ) ≤ A*(k : ℝ)*log ((k : ℝ)+2)^d) →
      ∀ m : ℕ, k^2 ≤ m → 1-ε ≤ coreCollisionFraction P R (range m) := by
  let c := exp (-WeightedMertens.reciprocalConstant-1)
  have hc : 0 < c := exp_pos _
  have hs := eventually_nat_log_power_small (d+1) 1 (by omega)
    (c/(6*A*3^d)) (by positivity)
  have hg := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (12/(c*ε)))
  filter_upwards [hs,hg,eventually_log_nat_ge 1,eventually_ge_atTop 2] with k hs hklarge hL hk
  intro P R hP hPk hex m hkm
  obtain ⟨p,hp,hp0,hpbound⟩ := hex
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hL0 : 0 < log (k : ℝ) := by linarith only [hL]
  have hM : 0 < m := (Nat.pow_pos (by omega : 0 < k)).trans_le hkm
  have hlog2 : 0 < log ((k : ℝ)+2) := log_pos (by linarith only [hk0])
  have hdensity : c/log ((k : ℝ)+2) ≤ density P := by
    simpa only [density,one_div,c] using WeightedMertens.prime_set_density_lower P hP k hPk
  have hlogup : log ((k : ℝ)+2) ≤ 3*log (k : ℝ) := by
    simpa only [pow_one,Nat.cast_one,show (1 : ℝ)+2=3 by norm_num] using log_power_add_two_le k 1 hk
  have hμlower : c*(k : ℝ)^2/(3*log (k : ℝ)) ≤ (m : ℝ)*density P := by
    have h1 := div_le_div_of_nonneg_left hc.le hlog2 hlogup
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hdensity) (sq_nonneg (k : ℝ))
    have h3 := mul_le_mul_of_nonneg_right
      (show (k : ℝ)^2 ≤ m by exact_mod_cast hkm) (density_pos P hP).le
    exact le_trans (by convert h2 using 1 <;> ring) h3
  have htail : 2*(p : ℝ) ≤ c*(k : ℝ)^2/(3*log (k : ℝ)) := by
    have hpow := pow_le_pow_left₀ hlog2.le hlogup d
    have hp' : (p : ℝ) ≤ A*3^d*(k : ℝ)*log (k : ℝ)^d := by
      have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ A*(k : ℝ) by positivity)
      apply hpbound.trans
      convert hh using 1 <;> ring
    apply (le_div_iff₀ (by positivity : 0 < 3*log (k : ℝ))).mpr
    have h1 := mul_le_mul_of_nonneg_right hp' (show 0 ≤ 6*log (k : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*A*3^d*(k : ℝ) by positivity)
    have he : (6*A*3^d*(k : ℝ))*(c/(6*A*3^d)*(k : ℝ)^1) = c*(k : ℝ)^2 := by
      field_simp
      <;> ring
    rw [he] at h2
    apply le_trans (by convert h1 using 1 <;> ring)
    convert h2 using 1 <;> ring
  have hμlarge : 4/ε ≤ (m : ℝ)*density P := by
    have hlogle : log (k : ℝ) ≤ k := log_le_self hk0.le
    have h1 : c*(k : ℝ)/3 ≤ c*(k : ℝ)^2/(3*log (k : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 3*log (k : ℝ))).mpr
      have hh := mul_le_mul_of_nonneg_left hlogle (show 0 ≤ c*(k : ℝ) by positivity)
      convert hh using 1 <;> ring
    have h2 : 4/ε ≤ c*(k : ℝ)/3 := by
      have hh := mul_le_mul_of_nonneg_left hklarge (show 0 ≤ c/3 by positivity)
      apply le_trans _ (by convert hh using 1 <;> ring)
      field_simp
      <;> norm_num
    exact h2.trans (h1.trans hμlower)
  have hfinite := collision_half_mean_lower P R hP m p hM hp hp0 (by linarith only [htail,hμlower])
  have hμ : 0 < (m : ℝ)*density P := mul_pos (by exact_mod_cast hM) (density_pos P hP)
  have h4 : 4/((m : ℝ)*density P) ≤ ε := by
    apply (div_le_iff₀ hμ).mpr
    have hh := (div_le_iff₀ hε).mp hμlarge
    nlinarith only [hh]
  linarith only [hfinite,h4]

#print axioms collision_half_mean_lower
#print axioms eventually_collision_near_one
end Erdos970.OneHitLogConcavity
