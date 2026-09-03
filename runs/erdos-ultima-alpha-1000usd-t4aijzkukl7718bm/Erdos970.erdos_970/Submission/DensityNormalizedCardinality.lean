import Submission.MixedCardinalityAffine
import Submission.PopulationLowCountBennett

/-! Filling missing reference primes before averaging removes a density loss
at the cost of a larger cardinality budget. These are consequences of an
already valid Jacobsthal bound, not a proof of the quadratic conjecture. -/
namespace Erdos970.MixedPattern
open Finset OptimalCoverCore CardinalityBootstrap GapAverages Resampling

lemma population_mean_card (S R : Finset ℕ) (hR : ∀ p ∈ R, p.Prime) :
    phaseMean R (fun s => ((populationSurvivors S R s).card : ℝ)) =
      (S.card : ℝ)*density R := by
  simp_rw [populationSurvivors_card]
  rw [phaseMean_sum]
  simp only [phaseMean_point R hR, sum_const, nsmul_eq_mul]

/-- Vary only the new residue classes, while preserving the old phase. -/
def adjoinResidues (R : Finset ℕ) (r : ℕ → ℕ) (s : Phase R) (p : ℕ) : ℕ :=
  if hp : p ∈ R then (s ⟨p,hp⟩).val else r p

lemma survivors_adjoin (m : ℕ) (P R : Finset ℕ) (r : ℕ → ℕ)
    (s : Phase R) (hd : Disjoint P R) :
    survivors m (P ∪ R) (adjoinResidues R r s) =
      populationSurvivors (survivors m P r) R s := by
  ext x
  simp only [mem_survivors, populationSurvivors, mem_filter]
  constructor
  · rintro ⟨hxm,hh⟩
    refine ⟨⟨hxm, ?_⟩, ?_⟩
    · intro p hp hhit
      have hn : p ∉ R := fun hpR => disjoint_left.mp hd hp hpR
      apply hh p (mem_union_left _ hp)
      simpa only [adjoinResidues, dif_neg hn] using hhit
    · intro p hhit
      apply hh p.val (mem_union_right _ p.property)
      simpa only [adjoinResidues, dif_pos p.property, Nat.ModEq,
        Nat.mod_eq_of_lt (s p).isLt] using hhit
  · rintro ⟨⟨hxm,hP⟩,hR⟩
    refine ⟨hxm, ?_⟩
    intro p hp hhit
    rcases mem_union.mp hp with hp | hp
    · have hn : p ∉ R := fun hpR => disjoint_left.mp hd hp hpR
      apply hP p hp
      simpa only [adjoinResidues, dif_neg hn] using hhit
    · apply hR ⟨p,hp⟩
      simpa only [adjoinResidues, dif_pos hp, Nat.ModEq,
        Nat.mod_eq_of_lt (s ⟨p,hp⟩).isLt] using hhit

lemma density_subset_le (P Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) :
    density Q ≤ density P := by
  have hd : Disjoint P (Q \ P) := by
    apply disjoint_left.mpr
    intro p hp hpR
    exact (mem_sdiff.mp hpR).2 hp
  have he : P ∪ (Q \ P) = Q := union_sdiff_of_subset hPQ
  have hsmall : density (Q \ P) ≤ 1 := by
    apply prod_le_one
    · intro p hp
      have hpR : (1 : ℝ) < p := by exact_mod_cast (hQ p (mem_sdiff.mp hp).1).one_lt
      have hi : (1 : ℝ)/p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr hpR.le
      linarith
    · intro p hp
      have hi : 0 ≤ (1 : ℝ)/p := by positivity
      linarith
  have hpos : 0 ≤ density P := (density_pos P (fun p hp => hQ p (hPQ hp))).le
  have hh := mul_le_mul_of_nonneg_left hsmall hpos
  rw [mul_one] at hh
  have hu : density Q = density P*density (Q \ P) := by
    conv_lhs => rw [← he]
    exact prod_union hd
  rw [hu]
  exact hh

/-- A phase-uniform Jacobsthal bound for the union, followed by averaging
only the added primes, supplies a density-normalized count for the old core. -/
theorem survivor_normalized_floor_lower {j g : ℕ} (h : IsJacobsthalBound j g)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    density P * (((m/g)*(j+1-(P.card+Q.card)) : ℕ) : ℝ) ≤
      density Q * ((survivors m P r).card : ℝ) := by
  let R := Q \ P
  have hR : ∀ p ∈ R, p.Prime := fun p hp => hQ p (mem_sdiff.mp hp).1
  have hd : Disjoint P R := by
    apply disjoint_left.mpr
    intro p hp hpR
    exact (mem_sdiff.mp hpR).2 hp
  have he : P ∪ R = P ∪ Q := union_sdiff_self_eq_union
  have hPR : ∀ p ∈ P ∪ R, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · exact hP p hp
    · exact hR p hp
  have hc : (P ∪ R).card ≤ P.card+Q.card := by
    rw [he]
    exact card_union_le P Q
  have hbudget : j+1-(P.card+Q.card) ≤ j+1-(P ∪ R).card := Nat.sub_le_sub_left hc _
  have hpnt (s : Phase R) :
      (((m/g)*(j+1-(P.card+Q.card)) : ℕ) : ℝ) ≤
        (populationSurvivors (survivors m P r) R s).card := by
    have hh := count_lower_floor_blocks (m := m) h (P ∪ R) hPR (adjoinResidues R r s)
    rw [survivors_adjoin m P R r s hd] at hh
    exact_mod_cast (Nat.mul_le_mul_left (m/g) hbudget).trans hh
  have hh := phaseMean_mono R hpnt
  rw [phaseMean_const R hR, population_mean_card _ R hR] at hh
  have hscale := mul_le_mul_of_nonneg_left hh (density_pos P hP).le
  have hden : density P*density R ≤ density Q := by
    have hsplit : density P*density R = density (P ∪ R) := (prod_union hd).symm
    rw [hsplit]
    apply density_subset_le Q (P ∪ R) hPR
    rw [he]
    exact subset_union_right
  have htail := mul_le_mul_of_nonneg_right hden (Nat.cast_nonneg (survivors m P r).card)
  nlinarith only [hscale,htail]

/-- Affine form of the normalized block inequality. The reference set may
intersect the old core; the proof only adjoins its missing primes. -/
theorem survivor_normalized_affine_lower {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    density P * (((j+1-(P.card+Q.card) : ℕ) : ℝ)/(g : ℝ)*(m : ℝ)-
      ((j+1-(P.card+Q.card) : ℕ) : ℝ)) ≤
        density Q * ((survivors m P r).card : ℝ) := by
  have hf := mul_le_mul_of_nonneg_right (real_floor_div_lower m g hg)
    (Nat.cast_nonneg (j+1-(P.card+Q.card)))
  have hs := mul_le_mul_of_nonneg_left hf (density_pos P hP).le
  have hh := survivor_normalized_floor_lower h P Q hP hQ r m
  push_cast at hh
  convert hs.trans hh using 1 <;> ring

/-- A mixed progression can use the same normalized count inequality after
rescaling. The added reference primes are chosen on the rescaled interval,
so no disjointness between them and the required-hit set is needed. -/
theorem mixedCount_normalized_affine_lower {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (m : ℕ) (A P Q : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hd : Disjoint A P) :
    density P * (((j+1-(P.card+Q.card) : ℕ) : ℝ)/(g : ℝ)*
      ((m : ℝ)/(∏ p ∈ A, (p : ℝ))-1)-((j+1-(P.card+Q.card) : ℕ) : ℝ)) ≤
        density Q * (mixedCount m A P r : ℝ) := by
  obtain ⟨c,s,hcl,_,he⟩ := mixedCount_rescale m A P r hA hP hd
  have hD : 0 < ∏ p ∈ A, p := prod_pos (fun p hp => (hA p hp).pos)
  have hcR : ((m/(∏ p ∈ A, p) : ℕ) : ℝ) ≤ c := by exact_mod_cast hcl
  have hc : (m : ℝ)/(∏ p ∈ A, (p : ℝ))-1 ≤ c := by
    rw [← Nat.cast_prod]
    exact (real_floor_div_lower m (∏ p ∈ A, p) hD).trans hcR
  have hn : 0 ≤ density P * (((j+1-(P.card+Q.card) : ℕ) : ℝ)/(g : ℝ)) :=
    mul_nonneg (density_pos P hP).le (by positivity)
  have hh := mul_le_mul_of_nonneg_left hc hn
  have hs := survivor_normalized_affine_lower h hg P Q hP hQ s c
  rw [he]
  nlinarith only [hh,hs]

#print axioms survivor_normalized_floor_lower
#print axioms survivor_normalized_affine_lower
#print axioms mixedCount_normalized_affine_lower
end Erdos970.MixedPattern
