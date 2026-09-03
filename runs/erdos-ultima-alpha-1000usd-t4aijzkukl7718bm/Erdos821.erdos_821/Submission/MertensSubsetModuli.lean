import Submission.MertensPrimeIntervals
import Submission.ElementaryMassLimit
import Submission.GrowingSubsetMoments

/-!
# Sharp main terms for fixed-order power-interval prime products

The reciprocal-totient mass has the expected factorial-normalized limit.
This is a modulus main term; it does not assert prime distribution at
moduli beyond the already established range.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def powerIntervalPrimes (a b m : ℕ) : Finset ℕ :=
  (Ioc (2^(a*m)) (2^(b*m))).filter Nat.Prime

lemma powerIntervalPrimes_properties (a b m p : ℕ) (hp : p ∈ powerIntervalPrimes a b m) :
    p.Prime ∧ 2^(a*m) < p ∧ p ≤ 2^(b*m) := by
  obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
  exact ⟨hpr,mem_Ioc.mp hpI⟩

lemma powerIntervalPrimes_mass_eq (a b m : ℕ) :
    poolTotientMass (powerIntervalPrimes a b m) = primeTotientInterval (2^(a*m)) (2^(b*m)) := by
  simp only [powerIntervalPrimes,poolTotientMass,primeTotientInterval,one_div]

lemma powerIntervalPrimes_weight_upper (a b m p : ℕ) (hp : p ∈ powerIntervalPrimes a b m) :
    (p.totient : ℝ)⁻¹ ≤ 2/((2^(a*m) : ℕ) : ℝ) := by
  have h := powerIntervalPrimes_properties a b m p hp
  exact_mod_cast prime_reciprocal_totient_le_twice_inv (2^(a*m)) p (by positivity) h.1 h.2.1.le

/-- Every fixed order has its exact elementary-symmetric main term. -/
theorem tendsto_powerInterval_subset_mass (a b r : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun m => poolTotientMass (primeSubsetModuli (powerIntervalPrimes a b m) r))
      atTop (𝓝 ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))) := by
  have H := tendsto_elementaryMass_of_small_weights (powerIntervalPrimes a b)
    (fun _ p => (p.totient : ℝ)⁻¹) (fun m => 2/((2^(a*m) : ℕ) : ℝ))
    (Real.log ((b : ℝ)/a))
    (fun _ p _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun m p hp => powerIntervalPrimes_weight_upper a b m p hp)
    (by simpa only [poolTotientMass, powerIntervalPrimes, primeTotientInterval, one_div] using
      tendsto_primeTotientInterval_power a b ha hab)
    ((tendsto_natCast_atTop_atTop.comp (tendsto_power_scale_nat a ha)).const_div_atTop 2) r
  apply H.congr
  intro m
  exact (primeSubsetModuli_mass (powerIntervalPrimes a b m)
    (fun p hp => (powerIntervalPrimes_properties a b m p hp).1) r).symm

lemma powerInterval_subset_bounds (a b r m d : ℕ)
    (hd : d ∈ primeSubsetModuli (powerIntervalPrimes a b m) r) :
    0 < d ∧ 2^(a*m*r) ≤ d ∧ d ≤ 2^(b*m*r) := by
  have hP := fun p hp => (powerIntervalPrimes_properties a b m p hp).1
  refine ⟨primeSubsetModuli_pos _ hP hd,?_,?_⟩
  · obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    have hh : (2^(a*m) : ℕ)^r ≤ ∏ p ∈ S, p := by
      rw [← (mem_powersetCard.mp hS).2, ← prod_const]
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        (fun p hp => (powerIntervalPrimes_properties a b m p ((mem_powersetCard.mp hS).1 hp)).2.1.le)
    simpa only [pow_mul] using hh
  · have hh := primeSubsetModuli_le (powerIntervalPrimes a b m) (2^(b*m))
      (fun p hp => (powerIntervalPrimes_properties a b m p hp).2.2) hd
    simpa only [pow_mul] using hh

/-- A positive, fixed lower mass is available whenever the interval is nontrivial. -/
theorem eventually_powerInterval_subset_mass_lower (a b r : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      (Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)) ≤
        poolTotientMass (primeSubsetModuli (powerIntervalPrimes a b m) r) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (a : ℝ) < b := by exact_mod_cast hab
  have hlog : 0 < Real.log ((b : ℝ)/a) :=
    Real.log_pos ((one_lt_div haR).mpr hbR)
  have hpos : (0 : ℝ) < (Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ) := by positivity
  have hh := (tendsto_powerInterval_subset_mass a b r ha hab.le).eventually
    (eventually_ge_nhds (show (Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)) <
      (Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ) by
      have he : (Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)) =
          ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))/2 := by ring
      rw [he]
      linarith))
  exact hh

end Erdos821
