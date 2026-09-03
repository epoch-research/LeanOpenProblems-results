import Submission.LargeChildPropagation

/-!
# Avoiding every large-child branch

The complement of an ancestor layer avoids the base set along every eligible
branch, rather than merely admitting one avoiding path. The recursive predicate
below records precisely this stronger property.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

/-- Every vertex reachable in at most L weak large-child steps is prime
and outside A. The first conjunct at a successor retains all shorter branches. -/
def largeChildAvoidingTree (k : ℕ) (A : Set ℕ) : ℕ → ℕ → Prop
  | 0, p => p.Prime ∧ p ∉ A
  | L+1, p => largeChildAvoidingTree k A L p ∧ ∀ q : ℕ,
      q.Prime → q ∣ p-1 → p-1 ≤ q^k → largeChildAvoidingTree k A L q

lemma largeChildAvoidingTree_iff (k : ℕ) (A : Set ℕ) (L p : ℕ) :
    largeChildAvoidingTree k A L p ↔ p.Prime ∧ p ∉ largeChildLayer k A L := by
  induction L generalizing p with
  | zero => rfl
  | succ L ih =>
    constructor
    · rintro ⟨hp, hchildren⟩
      obtain ⟨hp, hpL⟩ := (ih p).mp hp
      refine ⟨hp, ?_⟩
      rintro (hpL' | ⟨_, q, hqL, hq, hqd, hqs⟩)
      · exact hpL hpL'
      · exact ((ih q).mp (hchildren q hq hqd hqs)).2 hqL
    · rintro ⟨hp, hpL⟩
      refine ⟨(ih p).mpr ⟨hp, fun h => hpL (Or.inl h)⟩, ?_⟩
      intro q hq hqd hqs
      exact (ih q).mpr ⟨hq, fun h => hpL (Or.inr ⟨hp, q, h, hq, hqd, hqs⟩)⟩

lemma largeChildAvoidingTree_has_path (k : ℕ) (A : Set ℕ)
    (hsplit : ∀ p : ℕ, p.Prime → p ∉ A →
      ∃ q : ℕ, q.Prime ∧ q ∣ p-1 ∧ p-1 < q^k)
    (L p : ℕ) (H : largeChildAvoidingTree k A L p) :
    largeChildAvoidingPath k A L p := by
  obtain ⟨hp, hpL⟩ := (largeChildAvoidingTree_iff k A L p).mp H
  exact outside_largeChildLayer_has_avoiding_path k A hsplit L p hp hpL

end Erdos821
