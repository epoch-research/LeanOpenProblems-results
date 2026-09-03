import Submission.NatPairAlgebraExplore

/-! Total deficit mass bounds the number of points any monotone repair must
add. This is a limitation on a repair method, not a disproof of Erdos 66. -/
namespace Erdos66AdditiveDeficitMass
open AdditiveCombinatorics Erdos66NatPairAlgebra
open scoped Classical

noncomputable def incrementMass (A F T : Finset ℕ) : ℝ :=
  ∑ n ∈ T, ((sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n)

lemma increment_eq (A F : Finset ℕ) (h : Disjoint A F) (n : ℕ) :
    (sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n =
      2*(pairs A F n : ℝ)+pairs F F n := by
  rw [sumRep_union_self A F n h,← pairs_self F n]
  push_cast
  ring

lemma incrementMass_nonneg (A F T : Finset ℕ) (h : Disjoint A F) : 0 ≤ incrementMass A F T := by
  apply Finset.sum_nonneg
  intro n hn
  rw [increment_eq A F h n]
  positivity

/-- Every new ordered pair uses at least one added point. A single pair can
contribute to only one target, so total repair mass has this sharp bound. -/
theorem incrementMass_le (A F T : Finset ℕ) (h : Disjoint A F) :
    incrementMass A F T ≤ 2*(A.card : ℝ)*F.card+(F.card : ℝ)^2 := by
  have hmix : (∑ n ∈ T, (pairs A F n : ℝ)) ≤ (A.card : ℝ)*F.card := by
    exact_mod_cast pairs_sum_le A F T
  have hself : (∑ n ∈ T, (pairs F F n : ℝ)) ≤ (F.card : ℝ)^2 := by
    exact_mod_cast (show (∑ n ∈ T, pairs F F n) ≤ F.card^2 by
      simpa only [pow_two] using pairs_sum_le F F T)
  unfold incrementMass
  simp_rw [increment_eq A F h]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  nlinarith

/-- Filling an arbitrary prescribed lower profile costs at least its positive
part deficit relative to the old finite set. -/
theorem deficit_mass_le (A F T : Finset ℕ) (h : Disjoint A F) (q : ℕ → ℝ)
    (hfill : ∀ n ∈ T, q n ≤ (sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)) :
    (∑ n ∈ T, max (q n-(sumRep (A : Set ℕ) n : ℝ)) 0) ≤
      2*(A.card : ℝ)*F.card+(F.card : ℝ)^2 := by
  apply (Finset.sum_le_sum (fun n hn ↦ ?_)).trans (incrementMass_le A F T h)
  apply max_le
  · exact sub_le_sub_right (hfill n hn) _
  · rw [increment_eq A F h n]
    positivity

theorem uniform_deficit_mass_le (A F T : Finset ℕ) (h : Disjoint A F) (d : ℝ)
    (hdef : ∀ n ∈ T, (sumRep (A : Set ℕ) n : ℝ)+d ≤
      sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n) :
    d*T.card ≤ 2*(A.card : ℝ)*F.card+(F.card : ℝ)^2 := by
  have hh : (∑ _n ∈ T, d) ≤ incrementMass A F T := by
    apply Finset.sum_le_sum
    intro n hn
    have hd := hdef n hn
    linarith
  have he : (∑ _n ∈ T, d) = d*T.card := by simp [mul_comm]
  rw [he] at hh
  exact hh.trans (incrementMass_le A F T h)

/-- Solving the quadratic gives an explicit necessary number of added points. -/
theorem repair_card_lower (A F T : Finset ℕ) (h : Disjoint A F) (d : ℝ)
    (hdef : ∀ n ∈ T, (sumRep (A : Set ℕ) n : ℝ)+d ≤
      sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n) :
    Real.sqrt ((A.card : ℝ)^2+d*T.card)-A.card ≤ F.card := by
  have hh := uniform_deficit_mass_le A F T h d hdef
  have ha : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  have hf : (0:ℝ) ≤ F.card := Nat.cast_nonneg _
  have hs : Real.sqrt ((A.card : ℝ)^2+d*T.card) ≤ A.card+F.card :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  linarith

end Erdos66AdditiveDeficitMass
