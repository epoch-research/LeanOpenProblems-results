import Submission.CompletionFullPeriod

/-! Arbitrarily large relative-correlation loss for separated copies of a
two-point interval. This concerns unrestricted offsets, not adjacent blocks,
and does not disprove the Jacobsthal conjecture. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling ParityDiscrepancy
set_option maxHeartbeats 2200000

lemma two_prime_short_population (p q : ℕ) (hp : 3 ≤ p) (hq : 3 ≤ q) (hne : p ≠ q) :
    populationCoveredFraction (range 2) {p,q} = (2 : ℝ)/((p : ℝ)*q) ∧
      populationCoveredFraction (range 3) {p,q} = 0 := by
  have hnodup : ([p,q] : List ℕ).Nodup := by simp [hne]
  have hmods : ∀ r ∈ ([p,q] : List ℕ), 0 < r ∧ 3 ≤ r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> omega
  have h2 := population_eq_occupancy [p,q] hnodup 3 hmods (range 2) (range_mono (by omega))
  have h3 := population_eq_occupancy [p,q] hnodup 3 hmods (range 3) (Subset.refl _)
  simp only [List.toFinset_cons,List.toFinset_nil,insert_empty_eq,card_range] at h2 h3
  constructor
  · rw [h2]
    norm_num [occupancy,update]
    ring
  · rw [h3]
    norm_num [occupancy,update]

lemma range_two_shift_union :
    (range 2 ∪ (range 2).image (fun x => 1+x)) = range 3 := by decide

lemma two_prime_self_short_covariance (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hne : p ≠ q) :
    (∑ d ∈ range 2, coverageCovariance ({p,q} : Finset ℕ) (range 2)
      ((range 2).image (fun x => d+x))) =
        (2 : ℝ)/((p : ℝ)*q)-2*((2 : ℝ)/((p : ℝ)*q))^2 := by
  have hP : ∀ r ∈ ({p,q} : Finset ℕ), r.Prime := by
    simp only [mem_insert,mem_singleton]
    rintro r (rfl | rfl) <;> assumption
  have hF := two_prime_short_population p q hp3 hq3 hne
  simp only [sum_range_succ,sum_range_zero,zero_add,coverageCovariance]
  simp_rw [populationCoveredFraction_image_add _ _ hP]
  simp only [image_id']
  rw [union_self,range_two_shift_union,hF.1,hF.2]
  ring

lemma covariance_translate_full_period (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (d : ℕ) :
    coverageCovariance P S (S.image (fun x => (primeProduct P+d)+x)) =
      coverageCovariance P S (S.image (fun x => d+x)) := by
  rw [← coverageCovariance_displacement_mod P S S hP (primeProduct P+d)]
  simp only [Nat.add_mod_left]
  exact coverageCovariance_displacement_mod P S S hP d

/-- The prime-product loss cannot be replaced by any fixed constant times
the sum of the primes for arbitrary offsets. The budget, population length,
and averaging length in this counterexample are all two. -/
theorem no_uniform_additive_displacement_cost (C : ℝ) :
    ∃ (P : Finset ℕ) (b : ℕ),
      (∀ p ∈ P, p.Prime) ∧ P.card=2 ∧ 2 ≤ b ∧
      C*(∑ p ∈ P, (p : ℝ))*(populationCoveredFraction (range 2) P)^2 <
        |∑ d ∈ range 2, coverageCovariance P (range 2)
          ((range 2).image (fun x => (b+d)+x))| := by
  obtain ⟨p,hpl,hp⟩ := Nat.exists_infinite_primes (⌈4*(|C|+1)⌉₊+3)
  obtain ⟨q,hql,hq⟩ := Nat.exists_infinite_primes (p+1)
  have hp3 : 3 ≤ p := by omega
  have hq3 : 3 ≤ q := by omega
  have hpq : p ≠ q := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpbound : 4*(|C|+1) ≤ (p : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4*(|C|+1)⌉₊ ≤ p by omega))
  have hqbound : 4*(|C|+1) ≤ (q : ℝ) :=
    hpbound.trans (by exact_mod_cast (show p ≤ q by omega))
  have hprod1 := mul_le_mul_of_nonneg_right hpbound hqR.le
  have hprod2 := mul_le_mul_of_nonneg_right hqbound hpR.le
  have hsum : 2 < (p : ℝ)+q := by exact_mod_cast (show 2 < p+q by omega)
  have hcost := mul_le_mul_of_nonneg_right (le_abs_self C)
    (show 0 ≤ (p : ℝ)+q by positivity)
  have hcoeff : 2*C*((p : ℝ)+q)+4 < (p : ℝ)*q := by
    nlinarith only [hprod1,hprod2,hsum,hcost]
  let P : Finset ℕ := {p,q}
  have hP : ∀ r ∈ P, r.Prime := by
    simp only [P,mem_insert,mem_singleton]
    rintro r (rfl | rfl) <;> assumption
  refine ⟨P,primeProduct P,hP,by simp [P,hpq],?_,?_⟩
  · have he : primeProduct P=p*q := by simp [P,primeProduct,hpq]
    rw [he]
    nlinarith only [hp3,hq3]
  · have hs : (∑ d ∈ range 2, coverageCovariance P (range 2)
        ((range 2).image (fun x => (primeProduct P+d)+x))) =
        (2 : ℝ)/((p : ℝ)*q)-2*((2 : ℝ)/((p : ℝ)*q))^2 := by
      simp_rw [covariance_translate_full_period P (range 2) hP]
      exact two_prime_self_short_covariance p q hp hq hp3 hq3 hpq
    rw [hs]
    have hf := (two_prime_short_population p q hp3 hq3 hpq).1
    change populationCoveredFraction (range 2) P = _ at hf
    rw [hf]
    have hprimeSum : (∑ r ∈ P, (r : ℝ))=(p : ℝ)+q := by simp [P,hpq]
    rw [hprimeSum]
    apply lt_of_lt_of_le _ (le_abs_self _)
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos (mul_pos hpR hqR))).mp
    field_simp
    nlinarith only [hcoeff]

#print axioms two_prime_self_short_covariance
#print axioms no_uniform_additive_displacement_cost
end Erdos970.OneHitLogConcavity
