import Submission.BuchstabEulerStep
import Submission.BuchstabExponentialSource

/-! A global initial upper envelope in shifted Euler coordinates. The prime
threshold in the Rankin source is removed by exact finite-wheel vanishing.
The resulting constant is independent of the prime prefix and real level. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Set Finset MeasureTheory Filter FiniteSelberg ContinuousBuchstab
set_option maxHeartbeats 1800000

lemma referenceUpper_zero_le_one (k : ℕ) (D : ℝ) : referenceUpper 0 k D ≤ 1 := by
  change 1/normalizer (fun i : Fin k => primeMarginal i.val)
    (divisorSupport (fun i : Fin k => nthPrime i.val) (selbergCutoff (4*D))) ≤ 1
  rw [nthPrime_normalizer]
  have hG := primeNormalizer_ge_one (nthPrime k).primesBelow (selbergCutoff (4*D))
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (by unfold selbergCutoff; omega)
  exact (div_le_one (by linarith)).mpr hG

lemma primePrefix_density_antitone : Antitone (prefixDensity primeMarginal) := by
  apply antitone_nat_of_succ_le
  intro k
  rw [prefixDensity_prime_succ]
  have hd := nthPrime_prefix_density_pos k
  have hq := primeMarginal_pos k
  nlinarith only [hd,hq]

/-- The entire upper source is exact once its cutoff contains the wheel. -/
lemma referenceUpper_zero_eq_density_on_wheel (k W : ℕ) (hkW : nthPrime k ≤ W)
    (D : ℝ) (hD : (firstHitWheel W : ℝ)^2 ≤ D) :
    referenceUpper 0 k D=prefixDensity primeMarginal k := by
  have hW : (0 : ℝ) < firstHitWheel W := by exact_mod_cast firstHitWheel_pos W
  have hD0 : 0 ≤ D := (sq_nonneg (firstHitWheel W : ℝ)).trans hD
  have hsub : (nthPrime k).primesBelow ⊆ (W+1).primesBelow := by
    intro p hp
    obtain ⟨hpk,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩
  have hprod : (∏ p ∈ (nthPrime k).primesBelow, p) ≤ firstHitWheel W :=
    Nat.le_of_dvd (firstHitWheel_pos W) (prod_dvd_prod_of_subset _ _ id hsub)
  have hroot : (firstHitWheel W : ℝ) ≤ sqrt (4*D) := by
    apply (le_sqrt hW.le (by positivity)).mpr
    nlinarith only [hD,hD0]
  have hcut : firstHitWheel W ≤ selbergCutoff (4*D) :=
    (Nat.le_floor hroot).trans (le_max_right _ _)
  change 1/normalizer (fun i : Fin k => primeMarginal i.val)
    (divisorSupport (fun i : Fin k => nthPrime i.val) (selbergCutoff (4*D))) = _
  rw [nthPrime_normalizer,primeNormalizer_eq_eulerMass_of_prod_le _ _
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (hprod.trans hcut),nthPrime_prefix_density]

lemma eulerCoordinate_ge_initial (C : ℝ) (hC : 0 < C) (k : ℕ) :
    1/C ≤ eulerCoordinate C k := by
  simpa only [eulerCoordinate_zero] using eulerCoordinate_monotone C hC (Nat.zero_le k)

/-- The slower exponential is necessary here because Euler coordinates may
lie a bounded amount below the physical prime logarithm. -/
theorem exists_global_euler_upper_source (C B : ℝ) (hC : 0 < C) (hB0 : 0 ≤ B)
    (hB : ∀ k : ℕ, |eulerCoordinate C k-log (nthPrime k : ℝ)| ≤ B) :
    ∃ H > (0 : ℝ), ∀ k : ℕ, ∀ s : ℝ, 1 ≤ s →
      referenceUpper 0 k (exp (s*eulerCoordinate C k+B)) ≤
        prefixDensity primeMarginal k*(1+H*exp ((-2/3 : ℝ)*s)) := by
  obtain ⟨N,hN⟩ := exists_referenceUpper_exponential_source
  let W : ℕ := max 2 (max N ⌈exp (3*B)⌉₊)
  let S : ℝ := C*log ((firstHitWheel W : ℝ)^2)+1
  let H : ℝ := 2000+(1/prefixDensity primeMarginal W)*exp ((2/3 : ℝ)*S)
  have hW2 : 2 ≤ W := le_max_left _ _
  have hWN : N ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have hWe : ⌈exp (3*B)⌉₊ ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  have hden := nthPrime_prefix_density_pos W
  have hH0 : 0 < H := by dsimp [H]; positivity
  have hH2000 : (2000 : ℝ) ≤ H := by
    dsimp [H]
    exact le_add_of_nonneg_right (by positivity)
  have hwheel1 : (1 : ℝ) ≤ firstHitWheel W := by exact_mod_cast firstHitWheel_pos W
  have hwheel0 : (0 : ℝ) < (firstHitWheel W : ℝ)^2 := by positivity
  have hlogwheel : 0 ≤ log ((firstHitWheel W : ℝ)^2) := log_nonneg (by nlinarith only [hwheel1])
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith only [hC,hlogwheel]
  refine ⟨H,hH0,fun k s hs => ?_⟩
  have hT := eulerCoordinate_pos C hC k
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hlp : 0 < log (nthPrime k : ℝ) := log_pos (by exact_mod_cast (nthPrime_prime k).one_lt)
  by_cases hk : W ≤ nthPrime k
  · have h3B : 3*B ≤ log (nthPrime k : ℝ) := by
      apply (le_log_iff_exp_le hp0).mpr
      exact (Nat.le_ceil _).trans (by exact_mod_cast hWe.trans hk)
    have hcoord := (abs_le.mp (hB k)).1
    have hratio : (2/3 : ℝ)*log (nthPrime k : ℝ) ≤ eulerCoordinate C k := by
      linarith only [hcoord,h3B]
    let t : ℝ := (s*eulerCoordinate C k+B)/log (nthPrime k : ℝ)
    have ht1 : 1 ≤ t := by
      apply (le_div_iff₀ hlp).mpr
      nlinarith only [hcoord,hs,hT]
    have ht : (2/3 : ℝ)*s ≤ t := by
      apply (le_div_iff₀ hlp).mpr
      have hh := mul_le_mul_of_nonneg_left hratio (by linarith only [hs] : 0 ≤ s)
      nlinarith only [hh,hB0]
    have hh := hN k (hWN.trans hk) t ht1
    have he : t*log (nthPrime k : ℝ)=s*eulerCoordinate C k+B := by dsimp [t]; field_simp
    rw [he] at hh
    have htail : upperEnvelope 0 t ≤ H*exp ((-2/3 : ℝ)*s) := by
      change 2000*exp (-t) ≤ _
      exact mul_le_mul hH2000 (exp_le_exp.mpr (by linarith only [ht])) (exp_pos _).le hH0.le
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl htail)
      (nthPrime_prefix_density_pos k).le)
  · have hkW : nthPrime k ≤ W := by omega
    have hki : k ≤ W := (nthPrime_strictMono.id_le k).trans hkW
    have hd : prefixDensity primeMarginal W ≤ prefixDensity primeMarginal k := primePrefix_density_antitone hki
    by_cases hsS : S ≤ s
    · have htime : log ((firstHitWheel W : ℝ)^2) ≤ s*eulerCoordinate C k+B := by
        have hmul := mul_le_mul_of_nonneg_left (eulerCoordinate_ge_initial C hC k)
          (by linarith only [hs] : 0 ≤ s)
        have hdiv : log ((firstHitWheel W : ℝ)^2) ≤ s/C := by
          apply (le_div_iff₀ hC).mpr
          dsimp [S] at hsS
          nlinarith only [hsS]
        rw [mul_one_div] at hmul
        linarith only [hmul,hdiv,hB0]
      have hD := exp_le_exp.mpr htime
      rw [exp_log hwheel0] at hD
      rw [referenceUpper_zero_eq_density_on_wheel k W hkW _ hD]
      have hh : 1 ≤ 1+H*exp ((-2/3 : ℝ)*s) :=
        le_add_of_nonneg_right (mul_pos hH0 (exp_pos _)).le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (nthPrime_prefix_density_pos k).le
    · have hHsmall : (1/prefixDensity primeMarginal W)*exp ((2/3 : ℝ)*S) ≤ H := by
        dsimp [H]
        linarith
      have hcancel : 1 ≤ prefixDensity primeMarginal W*
          ((1/prefixDensity primeMarginal W)*exp ((2/3 : ℝ)*S))*exp ((-2/3 : ℝ)*s) := by
        have he : prefixDensity primeMarginal W*
            ((1/prefixDensity primeMarginal W)*exp ((2/3 : ℝ)*S))*exp ((-2/3 : ℝ)*s) =
            exp ((2/3 : ℝ)*(S-s)) := by
          rw [← mul_assoc,mul_one_div_cancel hden.ne',one_mul,← exp_add]
          congr 1
          ring
        rw [he]
        exact one_le_exp (by linarith only [hsS])
      have hbig : 1 ≤ prefixDensity primeMarginal k*(H*exp ((-2/3 : ℝ)*s)) := by
        have hh := mul_le_mul hd hHsmall (by positivity) (nthPrime_prefix_density_pos k).le
        have hm := mul_le_mul_of_nonneg_right hh (exp_pos ((-2/3 : ℝ)*s)).le
        exact hcancel.trans (by simpa only [mul_assoc] using hm)
      apply (referenceUpper_zero_le_one k _).trans
      nlinarith only [hbig,(nthPrime_prefix_density_pos k).le]

#print axioms referenceUpper_zero_eq_density_on_wheel
#print axioms exists_global_euler_upper_source
end Erdos970.RecursiveSieve.Buchstab
