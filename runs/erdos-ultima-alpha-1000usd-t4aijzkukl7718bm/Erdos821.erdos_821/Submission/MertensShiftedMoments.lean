import Submission.MertensSubsetModuli
import Submission.RoughHalfPrimeLimits

/-!
# Exact fixed-order shifted-prime binomial moments below the half level

All orders are fixed before the scale tends to infinity. The explicit
condition 2*b*r+5<=t prevents any unproved extension to near-full moduli.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def primeBinomialMoment (P : Finset ℕ) (r N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, (((P.filter (fun q => q ∣ p-1)).card.choose r : ℕ) : ℝ)*Real.log p

lemma primeSubset_incidence_eq_binomial (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r N : ℕ) :
    primePoolIncidenceMoment (primeSubsetModuli P r) N = primeBinomialMoment P r N := by
  unfold primePoolIncidenceMoment primeBinomialMoment
  apply sum_congr rfl
  intro p hp
  have hpr := (Nat.mem_primesBelow.mp hp).2
  rw [primeSubsetModuli_divisor_count P hP r (p-1) (by have := hpr.two_le; omega)]

lemma scaled_powerInterval_subset_mass (a b r : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun m => poolTotientMass (primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r))
      atTop (𝓝 ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))) := by
  have hh := tendsto_powerInterval_subset_mass (64*a) (64*b) r (by omega) (by omega)
  have he : (((64*b : ℕ) : ℝ)/((64*a : ℕ) : ℝ)) = (b : ℝ)/a := by
    push_cast
    field_simp
  simpa only [he] using hh

lemma scaled_powerInterval_subset_upper (a b r m d : ℕ)
    (hd : d ∈ primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r) :
    0 < d ∧ d ≤ progressionScaleN ((b*r)*m) := by
  have hh := powerInterval_subset_bounds (64*a) (64*b) r m d hd
  refine ⟨hh.1,?_⟩
  simpa only [progressionScaleN,mul_assoc,mul_left_comm,mul_comm] using hh.2.2

lemma scaled_powerInterval_subset_rough (a b r m d : ℕ)
    (hd : d ∈ primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r)
    (c : ℕ) (hc : c ∈ d.divisors.erase 1) : progressionScaleN (a*m) ≤ c := by
  apply primeSubsetModuli_rough (powerIntervalPrimes (64*a) (64*b) m)
    (progressionScaleN (a*m)) ?_ hd hc
  intro p hp
  have hh := powerIntervalPrimes_properties (64*a) (64*b) m p hp
  refine ⟨hh.1,?_⟩
  simpa only [progressionScaleN,mul_assoc] using hh.2.1.le

/-- The normalized prime-only moment has its exact factorial coefficient. -/
theorem tendsto_powerInterval_primeBinomialMoment (a b r t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hr : 1 ≤ r) (ht : 22 ≤ t) (hlevel : 2*(b*r)+5 ≤ t) :
    Tendsto (fun m => primeBinomialMoment (powerIntervalPrimes (64*a) (64*b) m) r
      (progressionScaleN (t*m))/mangoldtSum (progressionScaleN (t*m))) atTop
      (𝓝 ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))) := by
  let D (m : ℕ) := primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r
  have habr : a ≤ b*r := hab.trans (Nat.le_mul_of_pos_right b hr)
  have hh := tendsto_rough_pool_prime_normalized D a (b*r) t ha habr ht hlevel
    (fun m _ d hd => scaled_powerInterval_subset_upper a b r m d hd)
    (fun m _ d hd c hc => scaled_powerInterval_subset_rough a b r m d hd c hc)
    ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ)) (scaled_powerInterval_subset_mass a b r ha hab)
  apply hh.congr
  intro m
  dsimp only [D]
  rw [primeSubset_incidence_eq_binomial _
    (fun p hp => (powerIntervalPrimes_properties (64*a) (64*b) m p hp).1)]

/-- Positive lower moments hold at every sufficiently large scale in the valid range. -/
theorem eventually_powerInterval_primeBinomialMoment_lower (a b r t : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hr : 1 ≤ r) (ht : 22 ≤ t) (hlevel : 2*(b*r)+5 ≤ t) :
    ∀ᶠ m : ℕ in atTop,
      ((Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)))*
        mangoldtSum (progressionScaleN (t*m)) ≤
      primeBinomialMoment (powerIntervalPrimes (64*a) (64*b) m) r (progressionScaleN (t*m)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlog : 0 < Real.log ((b : ℝ)/a) :=
    Real.log_pos ((one_lt_div haR).mpr (by exact_mod_cast hab))
  have hpos : (0 : ℝ) < (Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ) := by positivity
  have hhalf : (Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)) <
      (Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ) := by
    have he : (Real.log ((b : ℝ)/a))^r/(2*(r.factorial : ℝ)) =
        ((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))/2 := by ring
    rw [he]
    linarith
  filter_upwards [(tendsto_powerInterval_primeBinomialMoment a b r t ha hab.le hr ht hlevel).eventually
    (eventually_ge_nhds hhalf),
    (progressionScaleN_mul_tendsto t (by omega)).eventually eventually_mangoldt_nine_tenths]
    with m hm hpsi
  have hN : (0 : ℝ) < progressionScaleN (t*m) := by unfold progressionScaleN; positivity
  have hpsi0 : 0 < mangoldtSum (progressionScaleN (t*m)) := by linarith only [hpsi,hN]
  exact (le_div_iff₀ hpsi0).mp hm

end Erdos821
