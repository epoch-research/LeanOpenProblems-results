import Submission.QuadraticTripleClassification
import Submission.WeightedPolynomialCubes

/-!
Rank-degenerate cases in the quadratic triple classification: for a nontrivial
triple with nonzero coordinates, every degeneracy propagates to a common
polynomial dilation of a constant six-tuple. No global density conclusion.
-/
namespace Erdos1206.QuadraticTripleDichotomy
open Polynomial FermatCubicConics FermatCubicSubspaces FermatConicDegeneracy
open RationalCubePairRelations QuadraticTripleClassification WeightedPolynomialCubes

/-- All six polynomial coordinates are multiples of one nonzero polynomial. -/
def CommonTriple (p q r : Pair) : Prop :=
  ∃ Q : ℚ[X], ∃ a b c d e f : ℚ, Q ≠ 0 ∧
    quad p.1=C a*Q ∧ quad p.2=C b*Q ∧ quad q.1=C c*Q ∧
    quad q.2=C d*Q ∧ quad r.1=C e*Q ∧ quad r.2=C f*Q

lemma CommonTriple.swap₂₃ {p q r : Pair} (h : CommonTriple p q r) : CommonTriple p r q := by
  obtain ⟨Q,a,b,c,d,e,f,hQ,ha,hb,hc,hd,he,hf⟩ := h
  exact ⟨Q,a,b,e,f,c,d,hQ,ha,hb,he,hf,hc,hd⟩

lemma CommonTriple.rotate {p q r : Pair} (h : CommonTriple p q r) : CommonTriple r p q := by
  obtain ⟨Q,a,b,c,d,e,f,hQ,ha,hb,hc,hd,he,hf⟩ := h
  exact ⟨Q,e,f,a,b,c,d,hQ,he,hf,ha,hb,hc,hd⟩

private lemma linear_neg (a x : Vec) : linear (-a) x= -linear a x := by
  dsimp [linear]
  ring

/-- A nontrivial degenerate four-coordinate identity is a common dilation. -/
theorem degenerate_pair_common {a b c d : Vec}
    (he : quad a^3+quad b^3=quad c^3+quad d^3) (hn : quad a^3+quad b^3 ≠ 0)
    (hac : quad a ≠ quad c) (had : quad a ≠ quad d)
    (hj : ¬ JointlyInjective (linear a) (linear b) (linear c) (linear d)) :
    FermatCubicLines.CommonFactor (quad a) (quad b) (quad c) (quad d) := by
  have he' : quad a^3+quad b^3+quad (-c)^3+quad (-d)^3=0 := by
    rw [quad_neg,quad_neg]
    linear_combination he
  have hj' : ¬ JointlyInjective (linear a) (linear b) (linear (-c)) (linear (-d)) := by
    intro hh
    apply hj
    intro x ha hb hc hd
    apply hh x ha hb
    · rw [linear_neg,hc,neg_zero]
    · rw [linear_neg,hd,neg_zero]
  rcases degenerate_family_classification he' hj' with hp | hp
  · rcases hp with ⟨hab,_⟩ | ⟨hac',_⟩ | ⟨had',_⟩
    · exact (sum_ne_zero hn hab).elim
    · rw [quad_neg] at hac'
      exact (hac (by linear_combination hac')).elim
    · rw [quad_neg] at had'
      exact (had (by linear_combination had')).elim
  · obtain ⟨Q,u,v,w,z,ha,hb,hc,hd⟩ := hp
    refine ⟨Q,u,v,-w,-z,ha,hb,?_,?_⟩
    · rw [quad_neg] at hc
      rw [map_neg]
      linear_combination -hc
    · rw [quad_neg] at hd
      rw [map_neg]
      linear_combination -hd

/-- A common dilation in one nontrivial pair of representations propagates
to every third nonzero representation of the same polynomial cube sum. -/
theorem degenerate_triple_common {p q r : Pair}
    (he₁ : quad p.1^3+quad p.2^3=quad q.1^3+quad q.2^3)
    (he₂ : quad p.1^3+quad p.2^3=quad r.1^3+quad r.2^3)
    (hn : quad p.1^3+quad p.2^3 ≠ 0)
    (h₁ : quad p.1 ≠ quad q.1) (h₂ : quad p.1 ≠ quad q.2)
    (hr₁ : quad r.1 ≠ 0) (hr₂ : quad r.2 ≠ 0)
    (hj : ¬ JointlyInjective (linear p.1) (linear p.2) (linear q.1) (linear q.2)) :
    CommonTriple p q r := by
  obtain ⟨Q,a,b,c,d,ha,hb,hc,hd⟩ := degenerate_pair_common he₁ hn h₁ h₂ hj
  have hsum : quad p.1^3+quad p.2^3=C (a^3+b^3)*Q^3 := by
    rw [ha,hb]
    simp only [map_add,map_pow]
    ring
  have hQ : Q ≠ 0 := by
    intro hz
    apply hn
    rw [hsum,hz,zero_pow (by decide : 3 ≠ 0),mul_zero]
  have hS : a^3+b^3 ≠ 0 := by
    intro hz
    apply hn
    rw [hsum,hz,map_zero,zero_mul]
  obtain ⟨e,f,he,hf⟩ := proportional_to_common_cube hr₁ hr₂ hQ hS (he₂.symm.trans hsum)
  exact ⟨Q,a,b,c,d,e,f,hQ,ha,hb,hc,hd,he,hf⟩

/-- The classification including rank degeneracies. The distinctness and
nonzero hypotheses are explicit; constant-dilation families are not omitted. -/
theorem common_or_collinear_after_swaps {p q r : Pair}
    (he₁ : quad p.1^3+quad p.2^3=quad q.1^3+quad q.2^3)
    (he₂ : quad p.1^3+quad p.2^3=quad r.1^3+quad r.2^3)
    (hn : quad p.1^3+quad p.2^3 ≠ 0)
    (hp₁ : quad p.1 ≠ 0) (hp₂ : quad p.2 ≠ 0)
    (hq₁ : quad q.1 ≠ 0) (hq₂ : quad q.2 ≠ 0)
    (hr₁ : quad r.1 ≠ 0) (hr₂ : quad r.2 ≠ 0)
    (hpp : quad p.1 ≠ quad p.2) (hqq : quad q.1 ≠ quad q.2) (hrr : quad r.1 ≠ quad r.2)
    (hpq₁ : quad p.1 ≠ quad q.1) (hpq₂ : quad p.1 ≠ quad q.2)
    (hpr₁ : quad p.1 ≠ quad r.1) (hpr₂ : quad p.1 ≠ quad r.2)
    (hqr₁ : quad q.1 ≠ quad r.1) (hqr₂ : quad q.1 ≠ quad r.2) :
    CommonTriple p q r ∨ Collinear p q r ∨ Collinear p (flip q) r ∨
      Collinear p q (flip r) ∨ Collinear p (flip q) (flip r) := by
  by_cases hj₁ : JointlyInjective (linear p.1) (linear p.2) (linear q.1) (linear q.2)
  swap
  · exact Or.inl (degenerate_triple_common he₁ he₂ hn hpq₁ hpq₂ hr₁ hr₂ hj₁)
  by_cases hj₂ : JointlyInjective (linear p.1) (linear p.2) (linear r.1) (linear r.2)
  swap
  · exact Or.inl (degenerate_triple_common he₂ he₁ hn hpr₁ hpr₂ hq₁ hq₂ hj₂).swap₂₃
  have he₃ := he₁.symm.trans he₂
  have hn' : quad q.1^3+quad q.2^3 ≠ 0 := by rw [← he₁]; exact hn
  by_cases hj₃ : JointlyInjective (linear q.1) (linear q.2) (linear r.1) (linear r.2)
  swap
  · exact Or.inl (degenerate_triple_common he₃ he₁.symm hn' hqr₁ hqr₂ hp₁ hp₂ hj₃).rotate
  right
  apply collinear_after_swaps
  exact ⟨⟨he₁,hn,hpp,hqq,hpq₁,hpq₂,hj₁⟩,
    ⟨he₂,hn,hpp,hrr,hpr₁,hpr₂,hj₂⟩,⟨he₃,hn',hqq,hrr,hqr₁,hqr₂,hj₃⟩⟩

#print axioms degenerate_pair_common
#print axioms degenerate_triple_common
#print axioms common_or_collinear_after_swaps
end Erdos1206.QuadraticTripleDichotomy
