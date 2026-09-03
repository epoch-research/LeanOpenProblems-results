import Submission.UndiscountedReferenceSource

/-! Exact union-budget version of the normalized cardinality source. Only
missing primes are adjoined, and their complete density is retained. The source
Jacobsthal bound is a hypothesis, not a consequence of these inequalities. -/
namespace Erdos970.MixedPattern
open Finset OptimalCoverCore CardinalityBootstrap GapAverages Resampling

/-- Averaging the new phases retains the exact union cardinality and density. -/
theorem survivor_union_floor_lower {j g : ℕ} (h : IsJacobsthalBound j g)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    (((m/g)*(j+1-(P ∪ Q).card) : ℕ) : ℝ) ≤
      density (Q \ P) * ((survivors m P r).card : ℝ) := by
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
  have hpnt (s : Phase R) :
      (((m/g)*(j+1-(P ∪ Q).card) : ℕ) : ℝ) ≤
        (populationSurvivors (survivors m P r) R s).card := by
    have hh := count_lower_floor_blocks (m := m) h (P ∪ R) hPR (adjoinResidues R r s)
    rw [survivors_adjoin m P R r s hd, he] at hh
    exact_mod_cast hh
  have hh := phaseMean_mono R hpnt
  rw [phaseMean_const R hR, population_mean_card _ R hR] at hh
  simpa only [mul_comm] using hh

/-- Affine form, still with the exact union budget. -/
theorem survivor_union_affine_lower {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) :
    ((j+1-(P ∪ Q).card : ℕ) : ℝ)/(g : ℝ)*(m : ℝ)-
      ((j+1-(P ∪ Q).card : ℕ) : ℝ) ≤
        density (Q \ P) * ((survivors m P r).card : ℝ) := by
  have hf := mul_le_mul_of_nonneg_right (real_floor_div_lower m g hg)
    (Nat.cast_nonneg (j+1-(P ∪ Q).card))
  have hh := survivor_union_floor_lower h P Q hP hQ r m
  push_cast at hh
  convert hf.trans hh using 1 <;> ring

/-- This density identity is why an extra inverse density survives boosting. -/
lemma density_union_cross (P Q : Finset ℕ) :
    density P * density (Q \ P) = density Q * density (P \ Q) := by
  have hd (S T : Finset ℕ) : Disjoint S (T \ S) := by
    apply disjoint_left.mpr
    intro p hp hpt
    exact (mem_sdiff.mp hpt).2 hp
  change (∏ p ∈ P, _) * (∏ p ∈ Q \ P, _) =
    (∏ p ∈ Q, _) * (∏ p ∈ P \ Q, _)
  rw [← prod_union (hd P Q), ← prod_union (hd Q P),
    union_sdiff_self_eq_union, union_sdiff_self_eq_union, union_comm]

/-- Normalized mixed source with the full missing-prime factor retained. -/
theorem mixedCount_union_normalized_affine_lower {j g : ℕ}
    (h : IsJacobsthalBound j g) (hg : 0 < g)
    (m : ℕ) (A P Q : Finset ℕ) (r : ℕ → ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hd : Disjoint A P) :
    density P *
      ((((j+1-(P ∪ Q).card : ℕ) : ℝ)/(g : ℝ)*
        ((m : ℝ)/(∏ p ∈ A, (p : ℝ))-1)-((j+1-(P ∪ Q).card : ℕ) : ℝ)) /
          density (P \ Q)) ≤
      density Q * (mixedCount m A P r : ℝ) := by
  obtain ⟨c,s,hcl,_,he⟩ := mixedCount_rescale m A P r hA hP hd
  have hD : 0 < ∏ p ∈ A, p := prod_pos (fun p hp => (hA p hp).pos)
  have hcR : ((m/(∏ p ∈ A, p) : ℕ) : ℝ) ≤ c := by exact_mod_cast hcl
  have hc : (m : ℝ)/(∏ p ∈ A, (p : ℝ))-1 ≤ c := by
    rw [← Nat.cast_prod]
    exact (real_floor_div_lower m (∏ p ∈ A, p) hD).trans hcR
  have hm := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ ((j+1-(P ∪ Q).card : ℕ) : ℝ)/(g : ℝ) by positivity)
  have hs := survivor_union_affine_lower h hg P Q hP hQ s c
  have hh :
      ((j+1-(P ∪ Q).card : ℕ) : ℝ)/(g : ℝ)*
        ((m : ℝ)/(∏ p ∈ A, (p : ℝ))-1)-((j+1-(P ∪ Q).card : ℕ) : ℝ) ≤
      density (Q \ P) * (mixedCount m A P r : ℝ) := by rw [he]; linarith
  have hp := mul_le_mul_of_nonneg_left hh (density_pos P hP).le
  rw [← mul_assoc, density_union_cross] at hp
  have hdpos : 0 < density (P \ Q) :=
    density_pos _ (fun p hp => hP p (mem_sdiff.mp hp).1)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hdpos).mpr
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hp

#print axioms survivor_union_floor_lower
#print axioms survivor_union_affine_lower
#print axioms mixedCount_union_normalized_affine_lower
end Erdos970.MixedPattern
