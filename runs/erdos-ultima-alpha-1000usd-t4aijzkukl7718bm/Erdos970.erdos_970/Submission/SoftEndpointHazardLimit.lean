import Submission.HazardPhaseTransport

/-! Exact soft-to-hard endpoint limits and a six-prime failure of global
monotonicity. This disproves a stronger auxiliary claim, NOT Erdos970 or
an endpoint estimate with a smaller positive constant. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology

lemma countLaplace_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (m : ℕ) : 0 < countLaplace P t m := by
  let r : Phase P := fun p => ⟨0, (hP p.val p.property).pos⟩
  have hs : 0 < ∑ s : Phase P, exp (-t*intervalCount P m s) :=
    (exp_pos (-t*intervalCount P m r)).trans_le
      (single_le_sum (f := fun s : Phase P => exp (-t*intervalCount P m s))
        (fun s _ => (exp_pos _).le) (mem_univ r))
  exact div_pos hs (prod_pos (fun p _ => by exact_mod_cast (hP p.val p.property).pos))

lemma tendsto_phase_exp_count (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    Tendsto (fun t : ℝ => exp (-t*intervalCount P m r)) atTop
      (𝓝 (if intervalCount P m r = 0 then (1 : ℝ) else 0)) := by
  by_cases hz : intervalCount P m r = 0
  · simp [hz]
  · have hn : 0 ≤ intervalCount P m r := by
      rw [← CoverFibers.phaseSurvivors_card]
      positivity
    have hp : 0 < intervalCount P m r := lt_of_le_of_ne hn (Ne.symm hz)
    have ht : Tendsto (fun t : ℝ => t*intervalCount P m r) atTop atTop :=
      Tendsto.atTop_mul_const hp tendsto_id
    simpa only [if_neg hz, Function.comp_def, neg_mul] using
      tendsto_exp_neg_atTop_nhds_zero.comp ht

/-- A finite positive Laplace sum tends to its zero-count mass. -/
theorem countLaplace_tendsto_void (P : Finset ℕ) (m : ℕ) :
    Tendsto (fun t : ℝ => countLaplace P t m) atTop (𝓝 (coveredFraction P m)) := by
  exact (tendsto_finset_sum univ (fun r _ => tendsto_phase_exp_count P m r)).div_const
    (∏ p : P, (p.val : ℝ))

noncomputable def coveredEndpointFraction (P : Finset ℕ) (m : ℕ) : ℝ :=
  phaseMean P (fun r => point P m r * if intervalCount P m r = 0 then 1 else 0)

/-- The weighted limit retains endpoint survival on the zero-count phases. -/
theorem endpointLaplace_tendsto_void (P : Finset ℕ) (m : ℕ) :
    Tendsto (fun t : ℝ => endpointLaplace P t m) atTop
      (𝓝 (coveredEndpointFraction P m)) := by
  exact (tendsto_finset_sum univ
    (fun r _ => (tendsto_phase_exp_count P m r).const_mul (point P m r))).div_const
      (∏ p : P, (p.val : ℝ))

namespace HazardExample

lemma real_phase_product : (∏ p : primes, (p.val : ℝ)) = 257130951 := by
  rw [prod_coe_sort primes (fun p : ℕ => (p : ℝ))]
  norm_num [primes]

lemma actual_void_fraction : coveredFraction primes 9 = (48 : ℝ)/257130951 := by
  classical
  unfold coveredFraction phaseMean
  rw [← reflectedPhaseEquiv.sum_comp (fun r =>
    if intervalCount primes 9 r = 0 then (1 : ℝ) else 0), real_phase_product]
  simp only [reflectedPhaseEquiv_apply, reflected_count_zero]
  rw [sum_boole, ← Fintype.card_subtype Covers, full_cover_counts.1]
  norm_num

lemma actual_endpoint_void_fraction :
    coveredEndpointFraction primes 9 = (24 : ℝ)/257130951 := by
  classical
  unfold coveredEndpointFraction phaseMean
  rw [← reflectedPhaseEquiv.sum_comp (fun r =>
    point primes 9 r * if intervalCount primes 9 r = 0 then (1 : ℝ) else 0),
    real_phase_product]
  simp only [reflectedPhaseEquiv_apply, reflected_count_zero, reflected_endpoint]
  have he (w : FullPhase) :
      (if Endpoint w then (1 : ℝ) else 0)*(if Covers w then 1 else 0) =
        if Covers w ∧ Endpoint w then 1 else 0 := by
    by_cases hc : Covers w <;> by_cases he : Endpoint w <;> simp [hc, he]
  simp_rw [he]
  rw [sum_boole, ← Fintype.card_subtype (fun w => Covers w ∧ Endpoint w), full_cover_counts.2]
  norm_num

/-- The actual normalized tilted endpoint converges to one half, below the
unconditional product density of these six primes. -/
theorem tilted_endpoint_limit :
    Tendsto (tiltedEndpoint primes 9) atTop (𝓝 (1/2 : ℝ)) := by
  have hF := countLaplace_tendsto_void primes 9
  have hG := endpointLaplace_tendsto_void primes 9
  rw [actual_void_fraction] at hF
  rw [actual_endpoint_void_fraction] at hG
  have hh := hG.div hF (by norm_num : (48 : ℝ)/257130951 ≠ 0)
  convert hh using 1
  norm_num [tiltedEndpoint]

/-- Thus the unit-constant endpoint estimate fails at positive parameters.
No assertion about every sufficiently small parameter is made. -/
theorem eventually_tilted_endpoint_lt_density :
    ∀ᶠ t : ℝ in atTop, tiltedEndpoint primes 9 t < density primes :=
  tilted_endpoint_limit.eventually (gt_mem_nhds density_gt_half)

theorem exists_positive_unit_endpoint_failure :
    ∃ t : ℝ, 0 < t ∧ ¬SoftEndpointBound 1 t := by
  obtain ⟨t, ht, he⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and eventually_tilted_endpoint_lt_density).exists
  refine ⟨t, ht, ?_⟩
  intro h
  have hh := h primes primes_prime 9
  have hz := countLaplace_pos primes primes_prime t 9
  have hl := (div_lt_iff₀ hz).mp he
  simp only [one_mul] at hh
  exact hl.not_ge hh

/-- Positive initial slope does not extend to monotonicity on the whole
positive half-line, even for this fixed genuine prime set and length. -/
theorem tilted_endpoint_not_monotone :
    ¬MonotoneOn (tiltedEndpoint primes 9) (Set.Ici 0) := by
  intro h
  obtain ⟨t, ht, he⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and eventually_tilted_endpoint_lt_density).exists
  have hh := h (by simp : (0 : ℝ) ∈ Set.Ici 0) ht.le ht.le
  rw [tiltedEndpoint_zero primes primes_prime 9] at hh
  exact he.not_ge hh

/-- Both behaviors hold for the SAME actual sieve: strict improvement close
to zero and strict worsening for all sufficiently large parameters. -/
theorem strict_improvement_then_worsening :
    (∀ᶠ t : ℝ in 𝓝[>] 0, density primes < tiltedEndpoint primes 9 t) ∧
    (∀ᶠ t : ℝ in atTop, tiltedEndpoint primes 9 t < density primes) := by
  refine ⟨eventually_tiltedEndpoint_gt_density primes primes_prime 9 ?_,
    eventually_tilted_endpoint_lt_density⟩
  norm_num [primes]

#print axioms actual_void_fraction
#print axioms actual_endpoint_void_fraction
#print axioms tilted_endpoint_limit
#print axioms exists_positive_unit_endpoint_failure
#print axioms tilted_endpoint_not_monotone
#print axioms strict_improvement_then_worsening
end HazardExample
end Erdos970.GapAverages
