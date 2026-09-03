import FormalConjecturesUtil

/-! Ordered pairs of ordered pairs sharing a coordinate. -/
open Finset
open scoped Classical
namespace Erdos713PairCollisionCounting
variable {V : Type*} [Fintype V]

noncomputable def collisionPairs (S : Finset (V × V)) : Finset ((V × V) × (V × V)) :=
  (S ×ˢ S).filter (fun p => p.2.1=p.1.1 ∨ p.2.1=p.1.2 ∨ p.2.2=p.1.1 ∨ p.2.2=p.1.2)

lemma card_collisionPairs_le (S : Finset (V × V)) :
    (collisionPairs S).card ≤ 4*Fintype.card V*S.card := by
  let T := S ×ˢ (univ : Finset V)
  let f₁ : (V × V) × V → (V × V) × (V × V) := fun p => (p.1,(p.1.1,p.2))
  let f₂ : (V × V) × V → (V × V) × (V × V) := fun p => (p.1,(p.1.2,p.2))
  let f₃ : (V × V) × V → (V × V) × (V × V) := fun p => (p.1,(p.2,p.1.1))
  let f₄ : (V × V) × V → (V × V) × (V × V) := fun p => (p.1,(p.2,p.1.2))
  have hsub : collisionPairs S ⊆ (T.image f₁ ∪ T.image f₂) ∪ (T.image f₃ ∪ T.image f₄) := by
    intro p hp
    obtain ⟨hmem,heq⟩ := mem_filter.mp hp
    have hpS := (mem_product.mp hmem).1
    rcases heq with h | h | h | h
    · apply mem_union_left
      apply mem_union_left
      exact mem_image.mpr ⟨(p.1,p.2.2),mem_product.mpr ⟨hpS,mem_univ _⟩,
        by dsimp [f₁]; exact Prod.ext rfl (Prod.ext h.symm rfl)⟩
    · apply mem_union_left
      apply mem_union_right
      exact mem_image.mpr ⟨(p.1,p.2.2),mem_product.mpr ⟨hpS,mem_univ _⟩,
        by dsimp [f₂]; exact Prod.ext rfl (Prod.ext h.symm rfl)⟩
    · apply mem_union_right
      apply mem_union_left
      exact mem_image.mpr ⟨(p.1,p.2.1),mem_product.mpr ⟨hpS,mem_univ _⟩,
        by dsimp [f₃]; exact Prod.ext rfl (Prod.ext rfl h.symm)⟩
    · apply mem_union_right
      apply mem_union_right
      exact mem_image.mpr ⟨(p.1,p.2.1),mem_product.mpr ⟨hpS,mem_univ _⟩,
        by dsimp [f₄]; exact Prod.ext rfl (Prod.ext rfl h.symm)⟩
  have hT : T.card = S.card*Fintype.card V := by simp only [T,card_product,card_univ]
  have h₁ := card_image_le (s := T) (f := f₁)
  have h₂ := card_image_le (s := T) (f := f₂)
  have h₃ := card_image_le (s := T) (f := f₃)
  have h₄ := card_image_le (s := T) (f := f₄)
  have h₁₂ := card_union_le (T.image f₁) (T.image f₂)
  have h₃₄ := card_union_le (T.image f₃) (T.image f₄)
  have hU := card_union_le (T.image f₁ ∪ T.image f₂) (T.image f₃ ∪ T.image f₄)
  have hC := card_le_card hsub
  nlinarith only [hT,h₁,h₂,h₃,h₄,h₁₂,h₃₄,hU,hC]

/-- If all coordinate-disjoint pairs land in T, then the square of |S|
is bounded by |T| and the explicit collision error. -/
theorem square_le (S : Finset (V × V)) (T : Finset ((V × V) × (V × V)))
    (h : ∀ p ∈ S, ∀ q ∈ S, q.1 ≠ p.1 → q.1 ≠ p.2 →
      q.2 ≠ p.1 → q.2 ≠ p.2 → (p,q) ∈ T) :
    S.card^2 ≤ 4*Fintype.card V*S.card+T.card := by
  have hsub : S ×ˢ S ⊆ collisionPairs S ∪ T := by
    intro p hp
    obtain ⟨h₁,h₂⟩ := mem_product.mp hp
    by_cases he : p.2.1=p.1.1 ∨ p.2.1=p.1.2 ∨ p.2.2=p.1.1 ∨ p.2.2=p.1.2
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,he⟩)
    · push_neg at he
      exact mem_union_right _ (h p.1 h₁ p.2 h₂ he.1 he.2.1 he.2.2.1 he.2.2.2)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_product,← pow_two] at hh
  exact hh.trans (Nat.add_le_add_right (card_collisionPairs_le S) _)

#print axioms square_le
end Erdos713PairCollisionCounting
