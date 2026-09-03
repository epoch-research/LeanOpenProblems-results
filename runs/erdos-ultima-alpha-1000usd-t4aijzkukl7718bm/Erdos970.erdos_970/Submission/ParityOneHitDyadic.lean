import Submission.OneHitCollisionRemainder
import Submission.OneHitMinimumFrequency

/-! A parity core makes odd residue maps injective on an interval of length
at most twice the modulus. This extends the one-hit dyadic reductions to tail
primes >=m rather than >=2m. The core fluctuation loss remains explicit. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling

/-- Surviving one fixed parity class rules out two distinct positions in the
same odd-prime class when their span is less than twice that prime. -/
theorem residue_injective_of_parity (P S : Finset ℕ) (m p : ℕ)
    (hS : S ⊆ range (2*m)) (h2 : 2 ∈ P) (hp : p.Prime) (hp2 : p ≠ 2)
    (hmp : m ≤ p) (r : Phase P) :
    Set.InjOn (fun x => x % p) (populationSurvivors S P r) := by
  intro x hx y hy hxy
  obtain ⟨hxS,hxa⟩ := mem_filter.mp hx
  obtain ⟨hyS,hya⟩ := mem_filter.mp hy
  have hxm : x < 2*m := mem_range.mp (hS hxS)
  have hym : y < 2*m := mem_range.mp (hS hyS)
  have hx2 := hxa ⟨2,h2⟩
  have hy2 := hya ⟨2,h2⟩
  have hr2 := (r ⟨2,h2⟩).isLt
  change x % 2 ≠ (r ⟨2,h2⟩).val at hx2
  change y % 2 ≠ (r ⟨2,h2⟩).val at hy2
  change (r ⟨2,h2⟩).val < 2 at hr2
  have hxl := Nat.mod_lt x (by omega : 0 < 2)
  have hyl := Nat.mod_lt y (by omega : 0 < 2)
  have he2 : x ≡ y [MOD 2] := by change x % 2 = y % 2; omega
  have hcp : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  have he := (Nat.modEq_and_modEq_iff_modEq_mul hcp).mp ⟨he2,hxy⟩
  exact he.eq_of_lt_of_lt (by omega) (by omega)

lemma coreCollisionFraction_zero_of_parity (P R : Finset ℕ) (m : ℕ)
    (hR : ∀ p ∈ R, p.Prime) (hPR : Disjoint P R) (h2 : 2 ∈ P)
    (hlarge : ∀ p ∈ R, m ≤ p) : coreCollisionFraction P R (range (2*m)) = 0 := by
  have he (r : Phase P) : ∀ p ∈ R,
      Set.InjOn (fun x => x % p) (populationSurvivors (range (2*m)) P r) := by
    intro p hp
    have hp2 : p ≠ 2 := by intro he; subst p; exact disjoint_left.mp hPR h2 hp
    exact residue_injective_of_parity P _ m p subset_rfl h2 (hR p hp) hp2 (hlarge p hp) r
  unfold coreCollisionFraction phaseMean
  have hs : (∑ r : Phase P, if (∀ p ∈ R, Set.InjOn (fun x => x % p)
      (populationSurvivors (range (2*m)) P r)) then (0 : ℝ) else 1) = 0 := by
    apply sum_eq_zero
    intro r hr
    exact if_pos (he r)
  rw [hs,zero_div]

/-- The one-hit second-moment reduction extends across the parity-filtered
half-modulus range, without changing or dropping its fluctuation term. -/
theorem parity_void_double_le_core_second_moment (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (h2 : 2 ∈ P) (hlarge : ∀ p ∈ R, m ≤ p) :
    coveredFraction (P ∪ R) (2*m) ≤
      phaseMean P (fun r => coreCoverWeight P R (range m) r^2) := by
  have hh := void_double_le_core_second_moment_add_collisions P R m hP hR hPR
  simpa only [coreCollisionFraction_zero_of_parity P R m hR hPR h2 hlarge,add_zero] using hh

/-- Minimum core-count frequency gives a rigorous loss also in the parity
range. No claim that this frequency is polynomially large is made. -/
theorem parity_minimum_frequency_mul_void_double_le (P R : Finset ℕ) (m s : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (h2 : 2 ∈ P) (hlarge : ∀ p ∈ R, m ≤ p)
    (hmin : ∀ r : Phase P, s ≤ (populationSurvivors (range m) P r).card) :
    coreCountFrequency P m s*coveredFraction (P ∪ R) (2*m) ≤ coveredFraction (P ∪ R) m^2 := by
  have hR' : ∀ p ∈ R, 0 < p ∧ m ≤ p := fun p hp => ⟨(hR p hp).pos,hlarge p hp⟩
  have hh := maximum_frequency_second_moment P (coreCoverWeight P R (range m))
    (occupancy R.toList s) (fun r => (populationSurvivors (range m) P r).card = s)
    (coreCoverWeight_nonneg P R _) (coreCoverWeight_le_minimum P R m s hR' hmin)
    (fun r hr => by
      unfold coreCoverWeight
      have hS : populationSurvivors (range m) P r ⊆ range m := filter_subset _ _
      rw [population_eq_finset_occupancy R _ m hR' hS,hr])
  rw [coreCoverWeight_mean P R _ hPR,← void_eq_population] at hh
  exact (mul_le_mul_of_nonneg_left
    (parity_void_double_le_core_second_moment P R m hP hR hPR h2 hlarge)
    (coreCountFrequency_nonneg P m s)).trans hh

/-- Coarse phase-count loss for the parity-filtered range. It is not an
absolute or sublinear-power dyadic loss. -/
theorem parity_void_double_le_core_phase_mass (P R : Finset ℕ) (m : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hPR : Disjoint P R) (h2 : 2 ∈ P) (hlarge : ∀ p ∈ R, m ≤ p) :
    coveredFraction (P ∪ R) (2*m) ≤ (∏ p ∈ P, (p : ℝ))*coveredFraction (P ∪ R) m^2 := by
  have hh := parity_void_double_le_core_second_moment P R m hP hR hPR h2 hlarge
  have hs := phaseMean_product_le_phase_mass P hP (coreCoverWeight P R (range m))
    (coreCoverWeight P R (range m)) (coreCoverWeight_nonneg P R _) (coreCoverWeight_nonneg P R _)
  simp only [← pow_two,coreCoverWeight_mean P R _ hPR,← void_eq_population] at hs
  nlinarith only [hh,hs]

#print axioms residue_injective_of_parity
#print axioms parity_void_double_le_core_second_moment
#print axioms parity_minimum_frequency_mul_void_double_le
#print axioms parity_void_double_le_core_phase_mass
end Erdos970.OneHitLogConcavity
