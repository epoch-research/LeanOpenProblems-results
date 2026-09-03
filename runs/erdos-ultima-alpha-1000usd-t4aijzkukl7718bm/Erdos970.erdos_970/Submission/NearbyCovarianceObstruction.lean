import Submission.NearbyCovarianceCertificate
import Submission.NearbyDisplacementCriterion

/-! Positive nearby coverage covariance at a length exceeding the prime
budget. This refutes the zero-loss auxiliary premise, not the original
quadratic conjecture nor the logarithmic-loss correlation premise. -/
namespace Erdos970.GapAverages
open Finset Real ParityDiscrepancy OneHitLogConcavity Resampling
set_option maxHeartbeats 2000000

lemma cyclic_void_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ)
    (dc : DecidablePred (fun a => CyclicSieve.natCount P m a = 0)) :
    coveredFraction P m =
      ((@Finset.filter ℕ (fun a => CyclicSieve.natCount P m a = 0) dc (range (primeProduct P))).card : ℝ) /
        primeProduct P := by
  classical
  letI := dc
  unfold coveredFraction phaseMean
  rw [← (CyclicSieve.cyclicPhaseEquiv P hP).sum_comp (fun r =>
    if intervalCount P m r = 0 then (1 : ℝ) else 0)]
  change (∑ a : Fin (primeProduct P),
    if intervalCount P m (CyclicSieve.cyclicPhase P hP a) = 0 then (1 : ℝ) else 0) / _ = _
  simp_rw [CyclicSieve.cyclic_count, Nat.cast_eq_zero]
  rw [Fin.sum_univ_eq_sum_range (fun a => if CyclicSieve.natCount P m a = 0 then (1 : ℝ) else 0),
    sum_boole]
  congr 1
  rw [prod_coe_sort P (fun p : ℕ => (p : ℝ))]
  simp only [primeProduct,Nat.cast_prod]

namespace NearbyExample

lemma actual_void : coveredFraction primes 7 = (36 : ℝ)/15015 := by
  rw [cyclic_void_count primes primes_prime 7 (fun _ => Classical.propDecidable _),prime_product]
  change (coverCount 15015 : ℝ)/15015 = (36 : ℝ)/15015
  rw [cover_count_certificate]
  norm_num

lemma actual_joint_lower : (1 : ℝ)/15015 ≤
    populationCoveredFraction (range 7 ∪ (range 7).image (fun x => 9+x)) primes := by
  classical
  let a : Fin (primeProduct primes) := ⟨7499,by rw [prime_product]; norm_num⟩
  let r := CyclicSieve.cyclicPhase primes primes_prime a
  have hc : ∀ x ∈ range 7 ∪ (range 7).image (fun x => 9+x),
      ∃ p ∈ primes, p ∣ 7499+x+1 := by decide +kernel
  have hr : ∀ x ∈ range 7 ∪ (range 7).image (fun x => 9+x),
      ∃ p : primes, x % p.val = (r p).val := by
    intro x hx
    obtain ⟨p,hp,hpx⟩ := hc x hx
    refine ⟨⟨p,hp⟩,(CyclicSieve.cyclic_hit primes primes_prime a x ⟨p,hp⟩).mpr ?_⟩
    exact hpx
  have hs := single_le_sum (s := (univ : Finset (Phase primes)))
    (f := fun s : Phase primes => if ∀ x ∈ range 7 ∪ (range 7).image (fun x => 9+x),
      ∃ p : primes, x % p.val = (s p).val then (1 : ℝ) else 0)
    (fun _ _ => by dsimp only; split_ifs <;> norm_num) (mem_univ r)
  dsimp only at hs
  rw [if_pos hr] at hs
  unfold populationCoveredFraction phaseMean
  have hd : (∏ p : primes, (p.val : ℝ)) = 15015 := by
    rw [prod_coe_sort primes (fun p : ℕ => (p : ℝ))]
    norm_num [primes]
  rw [hd]
  dsimp only
  apply div_le_div_of_nonneg_right _ (by norm_num)
  convert hs using 1
  apply sum_congr rfl
  intro s _
  by_cases h : ∀ x ∈ range 7 ∪ (range 7).image (fun x => 9+x),
      ∃ p : primes, x % p.val = (s p).val
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- Both blocks are disjoint and the second starts at offset 9, within the
required interval [7,14). Thus this is a genuinely local obstruction. -/
theorem nearby_covariance_pos : 0 < nearbyCovarianceSum primes 7 := by
  let J : ℕ → ℝ := fun d =>
    populationCoveredFraction (range 7 ∪ (range 7).image (fun x => (7+d)+x)) primes
  have hj : (1 : ℝ)/15015 ≤ ∑ d ∈ range 7, J d := by
    have hh := single_le_sum (s := range 7) (f := J)
      (fun d _ => populationCoveredFraction_nonneg _ _) (show 2 ∈ range 7 by decide)
    exact actual_joint_lower.trans hh
  have he : nearbyCovarianceSum primes 7 = (∑ d ∈ range 7, J d)-7*(coveredFraction primes 7)^2 := by
    unfold nearbyCovarianceSum coverageCovariance
    simp_rw [populationCoveredFraction_image_add primes (range 7) primes_prime]
    rw [← void_eq_population,sum_sub_distrib]
    simp only [sum_const,card_range,nsmul_eq_mul]
    dsimp only [J]
    ring
  rw [he,actual_void]
  norm_num at hj ⊢
  linarith only [hj]

theorem not_uniform_nonpositive_nearby :
    ¬∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, P.card ≤ m →
      nearbyCovarianceSum P m ≤ 0 := by
  intro h
  exact nearby_covariance_pos.not_ge (h primes primes_prime 7 (by norm_num [primes]))

#print axioms actual_void
#print axioms actual_joint_lower
#print axioms nearby_covariance_pos
#print axioms not_uniform_nonpositive_nearby
end NearbyExample
end Erdos970.GapAverages
