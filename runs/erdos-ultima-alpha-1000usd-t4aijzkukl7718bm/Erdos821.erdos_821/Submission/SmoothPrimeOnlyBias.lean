import Submission.SmoothRestrictedMean
import Submission.MertensSubsetModuli

/-!
# Prime-only progression bias of the supplied smooth-prime family

The cofactor-averaged relative means do not imply a prime-only relative
mean with main term F(N)/phi(d). In fact that proposed mean fails for the
actual smooth-prime family, already below the square-root level. This is
NOT a disproof of Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open HigherDivisors
set_option maxHeartbeats 4000000

lemma smooth_prime_only_weight_zero (N Y q : ℕ) (hq : q.Prime) (hYq : Y ≤ q) :
    restrictedCofactorWeight (smoothMangoldtWeight N Y) q 1 0 1 N = 0 := by
  rw [restricted_cofactor_singleton]
  apply sum_eq_zero
  intro p hp
  by_cases hdiv : q ∣ p-1
  · rw [if_pos hdiv]
    have hnot : p ∉ smoothPrimePool N Y := by
      intro hmem
      have hs := (mem_filter.mp hmem).2
      have hlt := Nat.mem_smoothNumbers'.mp hs q hq hdiv
      omega
    simp only [smoothMangoldtWeight,mangoldtRestriction,ArithmeticFunction.coe_mk,
      Finset.mem_coe,hnot,if_false]
  · simp only [hdiv,if_false]

noncomputable def primeOnlyRestrictedError (f : ArithmeticFunction ℝ) (Q N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 Q, |restrictedCofactorWeight f d 1 0 1 N-restrictedMass f N/(d.totient : ℝ)|

lemma smooth_prime_only_block_error (N Y : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ Y ≤ q) :
    (∑ q ∈ P, |restrictedCofactorWeight (smoothMangoldtWeight N Y) q 1 0 1 N-
      restrictedMass (smoothMangoldtWeight N Y) N/(q.totient : ℝ)|) =
        restrictedMass (smoothMangoldtWeight N Y) N*poolTotientMass P := by
  unfold poolTotientMass
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  rw [smooth_prime_only_weight_zero N Y q (hP q hq).1 (hP q hq).2,zero_sub,abs_neg,
    abs_of_nonneg (div_nonneg (restrictedMass_nonneg (smoothMangoldtWeight N Y) (mangoldtRestriction_nonneg _) N) (Nat.cast_nonneg _))]
  ring

lemma smooth_prime_only_error_lower (N Y Q : ℕ) (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ Y ≤ q ∧ q ≤ Q) :
    restrictedMass (smoothMangoldtWeight N Y) N*poolTotientMass P ≤
      primeOnlyRestrictedError (smoothMangoldtWeight N Y) Q N := by
  rw [← smooth_prime_only_block_error N Y P (fun q hq => ⟨(hP q hq).1,(hP q hq).2.1⟩)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact mem_Icc.mpr ⟨(hP q hq).1.one_lt.le,(hP q hq).2.2⟩
  · intros
    exact abs_nonneg _

noncomputable def suppliedBiasPrimePool (m : ℕ) : Finset ℕ :=
  Erdos821.powerIntervalPrimes (256*44425) (256*50000) m

noncomputable def suppliedBiasConstant : ℝ := Real.log ((50000 : ℝ)/44425)

lemma suppliedBiasConstant_pos : 0 < suppliedBiasConstant := by
  apply Real.log_pos
  norm_num

lemma suppliedBiasPrimePool_properties (m q : ℕ) (hq : q ∈ suppliedBiasPrimePool m) :
    q.Prime ∧ cofactorScale 44425 m ≤ q ∧ q ≤ cofactorScale 50000 m := by
  have hh := Erdos821.powerIntervalPrimes_properties (256*44425) (256*50000) m q hq
  rw [cofactorScale_eq,cofactorScale_eq]
  exact ⟨hh.1,hh.2.1.le,hh.2.2⟩

lemma tendsto_suppliedBiasPrimePool_mass :
    Tendsto (fun m => poolTotientMass (suppliedBiasPrimePool m)) atTop (𝓝 suppliedBiasConstant) := by
  have hh := Erdos821.tendsto_primeTotientInterval_power (256*44425) (256*50000) (by decide) (by decide)
  have he : Real.log (((256*50000 : ℕ) : ℝ)/((256*44425 : ℕ) : ℝ))=suppliedBiasConstant := by
    unfold suppliedBiasConstant
    norm_num
  rw [he] at hh
  simpa only [suppliedBiasPrimePool,Erdos821.powerIntervalPrimes_mass_eq] using hh

/-- The bias occurs at a modulus cutoff strictly below sqrt(N). -/
lemma suppliedBias_level_below_half (m : ℕ) (hm : 1 ≤ m) :
    (cofactorScale 50000 (2*m))^2 < cofactorScale 100005 (2*m) := by
  rw [cofactorScale_eq,cofactorScale_eq,← pow_mul]
  apply Nat.pow_lt_pow_right (by decide)
  nlinarith

/-- The supplied family is nonempty, and its prime-only relative discrepancy
stays bounded away from zero. The cofactor-averaged theorems remain valid. -/
theorem eventually_supplied_prime_only_bias :
    ∀ᶠ m : ℕ in atTop,
      let N := cofactorScale 100005 (2*m)
      let Y := cofactorScale 44425 (2*m)
      let f := smoothMangoldtWeight N Y
      0 < restrictedMass f N ∧
        suppliedBiasConstant/2*restrictedMass f N ≤
          primeOnlyRestrictedError f (cofactorScale 50000 (2*m)) N := by
  have hhalf : suppliedBiasConstant/2 < suppliedBiasConstant := by linarith [suppliedBiasConstant_pos]
  obtain ⟨M,hM⟩ := eventually_atTop.mp (tendsto_suppliedBiasPrimePool_mass.eventually_const_lt hhalf)
  filter_upwards [eventually_supplied_smooth_mass,eventually_ge_atTop M] with m hmass hm
  dsimp only
  have hpool := hM (2*m) (by omega)
  have hF0 : 0 < restrictedMass (smoothMangoldtWeight (cofactorScale 100005 (2*m))
      (cofactorScale 44425 (2*m))) (cofactorScale 100005 (2*m)) := by
    have hN : (0 : ℝ)<cofactorScale 100005 (2*m) := by exact_mod_cast cofactorScale_pos 100005 (2*m)
    have hZ : (0 : ℝ)<(2 : ℝ)^m := by positivity
    nlinarith only [hmass,hN,hZ]
  refine ⟨hF0,?_⟩
  have hlower := smooth_prime_only_error_lower (cofactorScale 100005 (2*m)) (cofactorScale 44425 (2*m))
    (cofactorScale 50000 (2*m)) (suppliedBiasPrimePool (2*m)) (suppliedBiasPrimePool_properties (2*m))
  have hh := mul_le_mul_of_nonneg_right hpool.le hF0.le
  apply le_trans ?_ hlower
  simpa only [mul_comm] using hh

/-- A concrete false extrapolation, not the negation of the conjecture. -/
theorem not_supplied_prime_only_relative_decay :
    ¬(∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      let N := cofactorScale 100005 (2*m)
      let f := smoothMangoldtWeight N (cofactorScale 44425 (2*m))
      primeOnlyRestrictedError f (cofactorScale 50000 (2*m)) N ≤ η*restrictedMass f N) := by
  intro H
  have hη : 0 < suppliedBiasConstant/4 := by positivity [suppliedBiasConstant_pos]
  have he := (H (suppliedBiasConstant/4) hη).and eventually_supplied_prime_only_bias
  obtain ⟨m,hm⟩ := he.exists
  dsimp only at hm
  have hpositive := mul_pos suppliedBiasConstant_pos hm.2.1
  nlinarith only [hm.1,hm.2.2,hpositive]

end Erdos821.AnalyticSieve
