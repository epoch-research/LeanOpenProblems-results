import Submission.CoprimeProductPools
import Submission.MertensShiftedMoments

/-!
# Joint fixed-order binomial moments for disjoint prime intervals

The limit factors, as predicted by the two reciprocal-prime masses. The
level condition bounds the TOTAL product modulus, not each factor separately.
-/
open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def primeJointBinomialMoment (P Q : Finset ℕ) (r s N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow,
    ((P.filter (fun q => q ∣ p-1)).card.choose r : ℝ)*
      ((Q.filter (fun q => q ∣ p-1)).card.choose s : ℝ)*Real.log p

lemma joint_primeSubset_incidence_eq (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (r s N : ℕ) :
    primePoolIncidenceMoment
      (pairPrimeProducts (primeSubsetModuli P r) (primeSubsetModuli Q s)) N =
      primeJointBinomialMoment P Q r s N := by
  unfold primePoolIncidenceMoment primeJointBinomialMoment
  apply sum_congr rfl
  intro p hp
  have hpr := (Nat.mem_primesBelow.mp hp).2
  rw [joint_primeSubset_divisor_count P Q hP hQ hPQ r s (p-1)
    (by have := hpr.two_le; omega),Nat.cast_mul]

lemma powerIntervalPrimes_disjoint (a b c d m : ℕ) (hbc : b ≤ c) :
    Disjoint (powerIntervalPrimes a b m) (powerIntervalPrimes c d m) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hp' := powerIntervalPrimes_properties a b m p hp
  have hq' := powerIntervalPrimes_properties c d m p hq
  have hh : 2^(b*m) ≤ (2 : ℕ)^(c*m) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right m hbc)
  omega

lemma scaled_joint_subset_mass (a b c d r s : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Tendsto (fun m => poolTotientMass
      (pairPrimeProducts (primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r)
        (primeSubsetModuli (powerIntervalPrimes (64*c) (64*d) m) s))) atTop
      (𝓝 (((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))*
        ((Real.log ((d : ℝ)/c))^s/(s.factorial : ℝ)))) := by
  have H := (scaled_powerInterval_subset_mass a b r ha hab).mul
    (scaled_powerInterval_subset_mass c d s (by omega) hcd)
  apply H.congr
  intro m
  symm
  apply coprime_pairProducts_mass
  · intro q hq
    exact (scaled_powerInterval_subset_upper a b r m q hq).1
  · intro q hq v hv
    exact disjoint_primeSubset_coprime _ _
      (fun p hp => (powerIntervalPrimes_properties (64*a) (64*b) m p hp).1)
      (fun p hp => (powerIntervalPrimes_properties (64*c) (64*d) m p hp).1)
      (powerIntervalPrimes_disjoint _ _ _ _ m (by omega)) hq hv

lemma scaled_joint_subset_upper (a b c d r s m q : ℕ)
    (hq : q ∈ pairPrimeProducts (primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r)
      (primeSubsetModuli (powerIntervalPrimes (64*c) (64*d) m) s)) :
    0 < q ∧ q ≤ progressionScaleN ((b*r+d*s)*m) := by
  have hD := scaled_powerInterval_subset_upper a b r m
  have hE := scaled_powerInterval_subset_upper c d s m
  refine ⟨pairProducts_pos _ _ (fun q hq => (hD q hq).1) (fun q hq => (hE q hq).1) hq,?_⟩
  have H := pairProducts_le _ _ (progressionScaleN ((b*r)*m)) (progressionScaleN ((d*s)*m))
    (fun q hq => (hD q hq).2) (fun q hq => (hE q hq).2) hq
  simpa only [progressionScaleN,← pow_add,Nat.add_mul,Nat.mul_add] using H

lemma scaled_joint_subset_rough (a b c d r s m q : ℕ) (hac : a ≤ c)
    (hq : q ∈ pairPrimeProducts (primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r)
      (primeSubsetModuli (powerIntervalPrimes (64*c) (64*d) m) s))
    (v : ℕ) (hv : v ∈ q.divisors.erase 1) : progressionScaleN (a*m) ≤ v := by
  apply pairProducts_rough _ _ (progressionScaleN (a*m))
    (fun q hq => (scaled_powerInterval_subset_upper a b r m q hq).1)
    (fun q hq => (scaled_powerInterval_subset_upper c d s m q hq).1) ?_ ?_ hq hv
  · exact fun q hq v hv => scaled_powerInterval_subset_rough a b r m q hq v hv
  · intro q hq v hv
    apply le_trans _ (scaled_powerInterval_subset_rough c d s m q hq v hv)
    unfold progressionScaleN
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 64 (Nat.mul_le_mul_right m hac))

/-- The joint limit is proved only when the combined selected modulus is below half. -/
theorem tendsto_powerInterval_primeJointBinomialMoment (a b c d r s t : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hrs : 1 ≤ r+s) (ht : 22 ≤ t) (hlevel : 2*(b*r+d*s)+5 ≤ t) :
    Tendsto (fun m => primeJointBinomialMoment
      (powerIntervalPrimes (64*a) (64*b) m) (powerIntervalPrimes (64*c) (64*d) m) r s
      (progressionScaleN (t*m))/mangoldtSum (progressionScaleN (t*m))) atTop
      (𝓝 (((Real.log ((b : ℝ)/a))^r/(r.factorial : ℝ))*
        ((Real.log ((d : ℝ)/c))^s/(s.factorial : ℝ)))) := by
  let D (m : ℕ) := pairPrimeProducts (primeSubsetModuli (powerIntervalPrimes (64*a) (64*b) m) r)
    (primeSubsetModuli (powerIntervalPrimes (64*c) (64*d) m) s)
  have habr : a ≤ b*r+d*s := by
    calc
      a ≤ a*(r+s) := Nat.le_mul_of_pos_right a hrs
      _ = a*r+a*s := Nat.mul_add _ _ _
      _ ≤ b*r+d*s := Nat.add_le_add (Nat.mul_le_mul_right r hab)
        (Nat.mul_le_mul_right s (by omega))
  have H := tendsto_rough_pool_prime_normalized D a (b*r+d*s) t ha habr ht hlevel
    (fun m _ q hq => scaled_joint_subset_upper a b c d r s m q hq)
    (fun m _ q hq v hv => scaled_joint_subset_rough a b c d r s m q (by omega) hq v hv)
    _ (scaled_joint_subset_mass a b c d r s ha hab hbc hcd)
  apply H.congr
  intro m
  dsimp only [D]
  rw [joint_primeSubset_incidence_eq _ _
    (fun p hp => (powerIntervalPrimes_properties (64*a) (64*b) m p hp).1)
    (fun p hp => (powerIntervalPrimes_properties (64*c) (64*d) m p hp).1)
    (powerIntervalPrimes_disjoint _ _ _ _ m (by omega))]

end Erdos821
