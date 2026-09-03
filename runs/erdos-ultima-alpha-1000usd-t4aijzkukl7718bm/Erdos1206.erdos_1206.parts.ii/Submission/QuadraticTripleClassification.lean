import Submission.QuadraticOrientationBridge
import Submission.QuadraticTwoSums

/-!
Classification, up to swapping the coordinates of individual representations,
of nondegenerate quadratic triple families with distinct polynomial coordinates.
This is not a classification of arbitrary numerical triples or arbitrary-degree
families, and it does not settle the density conjecture.
-/
namespace Erdos1206.QuadraticTripleClassification
open Polynomial FermatCubicConics FermatCubicSubspaces RationalCubePairRelations
open QuadraticOrientationBridge QuadraticTwoSums

abbrev Pair := Vec × Vec

def flip (p : Pair) : Pair := (p.2,p.1)

/-- The explicit nondegeneracy assumptions for two representations. -/
structure GoodPair (p q : Pair) : Prop where
  cubes : quad p.1^3+quad p.2^3=quad q.1^3+quad q.2^3
  nonzero : quad p.1^3+quad p.2^3 ≠ 0
  internal_left : quad p.1 ≠ quad p.2
  internal_right : quad q.1 ≠ quad q.2
  apart_left : quad p.1 ≠ quad q.1
  apart_right : quad p.1 ≠ quad q.2
  joint : JointlyInjective (linear p.1) (linear p.2) (linear q.1) (linear q.2)

lemma GoodPair.other {p q : Pair} (h : GoodPair p q) :
    quad p.2 ≠ quad q.2 ∧ quad p.2 ≠ quad q.1 :=
  other_differences h.cubes h.apart_left h.apart_right

lemma GoodPair.symm {p q : Pair} (h : GoodPair p q) : GoodPair q p where
  cubes := h.cubes.symm
  nonzero := by rw [← h.cubes]; exact h.nonzero
  internal_left := h.internal_right
  internal_right := h.internal_left
  apart_left := h.apart_left.symm
  apart_right := h.other.2.symm
  joint := fun x ha hb hc hd => h.joint x hc hd ha hb

lemma GoodPair.flip_left {p q : Pair} (h : GoodPair p q) : GoodPair (flip p) q where
  cubes := by change quad p.2^3+quad p.1^3=_; rw [add_comm]; exact h.cubes
  nonzero := by change quad p.2^3+quad p.1^3 ≠ 0; rw [add_comm]; exact h.nonzero
  internal_left := h.internal_left.symm
  internal_right := h.internal_right
  apart_left := h.other.2
  apart_right := h.other.1
  joint := fun x ha hb hc hd => h.joint x hb ha hc hd

lemma GoodPair.flip_right {p q : Pair} (h : GoodPair p q) : GoodPair p (flip q) :=
  h.symm.flip_left.symm

/-- Nondegeneracy for every pair of representations. -/
def GoodTriple (p q r : Pair) : Prop := GoodPair p q ∧ GoodPair p r ∧ GoodPair q r

lemma GoodTriple.flip₂ {p q r : Pair} (h : GoodTriple p q r) : GoodTriple p (flip q) r :=
  ⟨h.1.flip_right,h.2.1,h.2.2.flip_left⟩

lemma GoodTriple.flip₃ {p q r : Pair} (h : GoodTriple p q r) : GoodTriple p q (flip r) :=
  ⟨h.1,h.2.1.flip_right,h.2.2.flip_right⟩

lemma GoodTriple.rotate {p q r : Pair} (h : GoodTriple p q r) : GoodTriple r p q :=
  ⟨h.2.1.symm,h.2.2.symm,h.1⟩

lemma GoodTriple.swap₁₂ {p q r : Pair} (h : GoodTriple p q r) : GoodTriple q p r :=
  ⟨h.1.symm,h.2.2,h.2.1⟩

lemma GoodTriple.swap₂₃ {p q r : Pair} (h : GoodTriple p q r) : GoodTriple p r q :=
  ⟨h.2.1,h.1,h.2.2.symm⟩

abbrev SumRelated (p q : Pair) := SumRelation p.1 p.2 q.1 q.2
abbrev DifferenceRelated (p q : Pair) := DifferenceRelation p.1 p.2 q.1 q.2

lemma GoodPair.relation {p q : Pair} (h : GoodPair p q) :
    SumRelated p q ∨ DifferenceRelated p q ∨ DifferenceRelated p (flip q) :=
  normalized_pair_relation h.cubes h.nonzero h.apart_left h.apart_right

/-- Collinearity as an identity on the full three-dimensional linearization. -/
def Collinear (p q r : Pair) : Prop := ∀ x : Vec,
  (linear q.1 x-linear p.1 x)*(linear r.2 x-linear p.2 x)=
    (linear r.1 x-linear p.1 x)*(linear q.2 x-linear p.2 x)

private lemma two_differences_sum_false {p q u : Pair} (h : GoodTriple p q u)
    (h₁ : DifferenceRelated p q) (h₂ : DifferenceRelated p u)
    (h₃ : SumRelated q u) : False := by
  obtain ⟨r,hr,hr₁,h₁⟩ := h₁
  obtain ⟨s,hs,_,h₂⟩ := h₂
  obtain ⟨k,hk,hk₁,h₃⟩ := h₃
  exact one_sum_false h₁ h₂ h₃ h.1.cubes h.2.1.cubes h.1.other.1 h.2.1.other.1
    h.2.1.joint (ne_of_lt hs) hr₁ hk hk₁

private lemma two_sums_good_false {p q r : Pair} (h : GoodTriple p q r)
    (h₁ : SumRelated p q) (h₂ : SumRelated p r) : False := by
  exact two_sums_false h.1.cubes h.2.1.cubes h.1.nonzero
    h.1.internal_left h.1.internal_right h.2.1.internal_right
    h.2.2.apart_left h.2.2.apart_right h.1.joint h₁ h₂

private lemma sum_and_difference_false {p q r : Pair} (h : GoodTriple p q r)
    (hs : SumRelated p q) (hd : DifferenceRelated p r) : False := by
  rcases h.2.2.relation with hs' | hd' | hd'
  · exact two_sums_good_false h.swap₁₂ hs.symm hs'
  · exact two_differences_sum_false h.rotate hd.symm hd'.symm hs
  · exact two_differences_sum_false h.rotate.flip₃ hd.symm hd'.symm.swap_both hs.swap_right

/-- A nondegenerate triple cannot have any proportional-pair-sum relation. -/
theorem sum_relation_false {p q r : Pair} (h : GoodTriple p q r) (hs : SumRelated p q) : False := by
  rcases h.2.1.relation with hs' | hd | hd
  · exact two_sums_good_false h hs hs'
  · exact sum_and_difference_false h hs hd
  · exact sum_and_difference_false h.flip₃ hs hd

/-- Once two direction relations are aligned, the third forces collinearity. -/
theorem aligned_differences_collinear {p q u : Pair} (h : GoodTriple p q u)
    (h₁ : DifferenceRelated p q) (h₂ : DifferenceRelated p u) : Collinear p q u := by
  obtain ⟨r,hr,hr₁,h₁⟩ := h₁
  obtain ⟨s,hs,_,h₂⟩ := h₂
  rcases h.2.2.relation with h₃ | h₃ | h₃
  · exact (sum_relation_false h.rotate.rotate h₃).elim
  · obtain ⟨t,ht,_,h₃⟩ := h₃
    have hsr := consistent_ratios_equal h₁ h₂ h₃ h.1.cubes h.2.1.cubes
      h.1.other.1 h.2.1.other.1 h.2.1.joint (ne_of_lt hr) (ne_of_lt hs) (ne_of_lt ht)
    subst s
    intro x
    linear_combination -(linear u.2 x-linear p.2 x)*(h₁ x)+
      (linear q.2 x-linear p.2 x)*(h₂ x)
  · obtain ⟨t,ht,ht₁,h₃⟩ := h₃
    exact (inconsistent_difference_false h₁ h₂ h₃ h.1.cubes h.2.1.cubes
      h.1.other.1 h.2.1.other.1 h.2.1.joint hr (ne_of_lt hs) ht hr₁ ht₁).elim

/-- Nondegenerate quadratic triple families are collinear after possibly
swapping the coordinates in the second and third representations. -/
theorem collinear_after_swaps {p q r : Pair} (h : GoodTriple p q r) :
    Collinear p q r ∨ Collinear p (flip q) r ∨
      Collinear p q (flip r) ∨ Collinear p (flip q) (flip r) := by
  have h₁ := h.1.relation
  have h₂ := h.2.1.relation
  rcases h₁ with hs | hq | hq
  · exact (sum_relation_false h hs).elim
  · rcases h₂ with hs | hr | hr
    · exact (sum_relation_false h.swap₂₃ hs).elim
    · exact Or.inl (aligned_differences_collinear h hq hr)
    · exact Or.inr (Or.inr (Or.inl (aligned_differences_collinear h.flip₃ hq hr)))
  · rcases h₂ with hs | hr | hr
    · exact (sum_relation_false h.swap₂₃ hs).elim
    · exact Or.inr (Or.inl (aligned_differences_collinear h.flip₂ hq hr))
    · exact Or.inr (Or.inr (Or.inr (aligned_differences_collinear h.flip₂.flip₃ hq hr)))

#print axioms sum_relation_false
#print axioms aligned_differences_collinear
#print axioms collinear_after_swaps
end Erdos1206.QuadraticTripleClassification
