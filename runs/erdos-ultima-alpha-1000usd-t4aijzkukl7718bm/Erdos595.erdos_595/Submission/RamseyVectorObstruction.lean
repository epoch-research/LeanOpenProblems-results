import Submission.PaleyObstruction

/-!
A conditional obstruction to the uniform triangle-hitting route.

This file does not prove an infinite Folkman theorem or settle Erdős 595.
It proves that the usual finite Ramsey property transfers an all-edge
vector obstruction to a minimum-edge triangle obstruction. In particular,
a graph Ramsey for a red Paley-17 graph or a blue triangle cannot have a
unit-vector triangle-hitting assignment at margin 1/3.

The finite clique-preserving Ramsey existence theorem is not proved here.
-/

set_option autoImplicit false

open SimpleGraph Set

namespace Erdos595RamseyVector

/-- Every red/blue edge cover with no blue triangle contains a red
homomorphic copy of K. An ordinary Ramsey embedding property implies this. -/
def RamseyAgainstTriangle {U V : Type*} (K : SimpleGraph U) (G : SimpleGraph V) : Prop :=
  ∀ R B : SimpleGraph V, G = R ⊔ B → B.CliqueFree 3 → Nonempty (K →g R)

/-- Unit vectors having at least one sufficiently negative pair on each
triangle. This definition makes no assertion that such vectors exist. -/
def UnitTriangleHit {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : SimpleGraph V) (δ : ℝ) (v : V → E) : Prop :=
  (∀ a, inner ℝ (v a) (v a) = 1) ∧
  (∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
    inner ℝ (v a) (v b) ≤ δ ∨ inner ℝ (v a) (v c) ≤ δ ∨
      inner ℝ (v b) (v c) ≤ δ)

theorem no_triangle_hit_of_ramsey {U V E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : SimpleGraph U) (G : SimpleGraph V) (δ : ℝ)
    (hK : ¬∃ w : U → E, (∀ a, inner ℝ (w a) (w a) = 1) ∧
      (∀ a b, K.Adj a b → inner ℝ (w a) (w b) ≤ δ))
    (hG : RamseyAgainstTriangle K G) :
    ¬∃ v : V → E, UnitTriangleHit G δ v := by
  classical
  rintro ⟨v, hu, ht⟩
  let R : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ inner ℝ (v a) (v b) ≤ δ
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  let B : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ δ < inner ℝ (v a) (v b)
      symm := fun a b h => ⟨h.1.symm, by simpa only [real_inner_comm] using h.2⟩
      loopless := fun a h => G.loopless a h.1 }
  have heq : G = R ⊔ B := by
    ext a b
    change G.Adj a b ↔ (G.Adj a b ∧ inner ℝ (v a) (v b) ≤ δ) ∨
      (G.Adj a b ∧ δ < inner ℝ (v a) (v b))
    constructor
    · intro h
      rcases le_or_gt (inner ℝ (v a) (v b)) δ with hn | hp
      · exact Or.inl ⟨h, hn⟩
      · exact Or.inr ⟨h, hp⟩
    · rintro (h | h) <;> exact h.1
  have hB : B.CliqueFree 3 := by
    intro t h
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp h
    rcases ht a b c hab.1 hac.1 hbc.1 with hn | hn | hn
    · exact (not_le_of_gt hab.2) hn
    · exact (not_le_of_gt hac.2) hn
    · exact (not_le_of_gt hbc.2) hn
  obtain ⟨f⟩ := hG R B heq hB
  exact hK ⟨v ∘ f, fun a => hu (f a), fun a b h => (f.map_adj h).2⟩

theorem no_triangle_hit_third_of_paley_ramsey {V E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : SimpleGraph V) (hG : RamseyAgainstTriangle Erdos595Paley.G G) :
    ¬∃ v : V → E, UnitTriangleHit G (-(1 / 3 : ℝ)) v := by
  exact no_triangle_hit_of_ramsey Erdos595Paley.G G (-(1 / 3 : ℝ))
    Erdos595Paley.no_unit_all_edges_le_neg_third hG

#print axioms no_triangle_hit_of_ramsey
#print axioms no_triangle_hit_third_of_paley_ramsey

end Erdos595RamseyVector
