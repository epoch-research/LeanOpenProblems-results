import Submission.DirectedOrRightCover
import Submission.WellOrderedSecondShiftCover

/-!
All second ordered-shift exponential domains are excluded, for ARBITRARY
linear orders, not just well-orders. Two repeated profile COLORS suffice;
cofinal repetition of exact profiles is unnecessary. This does not settle
Erdős 595 or exclude general/higher exponential domains.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595AllSecondShift
open Erdos595DirectedRight Erdos595DirectedOrRight
open Erdos595SecondShiftExponential Erdos595MiddleCorner
variable {A W : Type*} [LinearOrder A] [Countable W]

/-- Non-colorability of the second shift rules out even a single-powerset
encoding of its index. This needs no well-foundedness assumption. -/
lemma no_encoding (hA : IsEmpty ((oneGraph A).Coloring ℕ))
    (e : A → Set ℕ) : ¬Function.Injective e := by
  intro he
  have hs : Function.Injective (fun a => ({e a} : Set (Set ℕ))) := by
    intro a b h
    exact he (Set.singleton_injective h)
  exact hA.false (Erdos595WellOrderedSecondShift.coloring_of_encoding _ hs).some

/-- A proper Set-N color of the directed two-stage profile, repeated at two
indices, becomes a proper Set-N color of the exponential vertex. -/
theorem coloring (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (hA : IsEmpty ((oneGraph A).Coloring ℕ)) :
    Nonempty ((F H hA).Coloring (Set ℕ)) := by
  classical
  obtain ⟨c⟩ := two_powerset H hH
  let col (f : Word (A := A) (W := W)) (a : A) : Set ℕ := c (profile H hA (f,a))
  have heq_index (f g : Word (A := A) (W := W)) (hfg : (F H hA).Adj f g)
      (a b : A) (he : col f a = col g b) : a = b := by
    rcases lt_trichotomy a b with hab | hab | hba
    · exact False.elim (c.valid (Or.inl (profile_rel H hA ⟨hfg,hab⟩)) he)
    · exact hab
    · exact False.elim (c.valid (Or.inl (profile_rel H hA ⟨hfg.symm,hba⟩)) he.symm)
  have hrep (f : Word (A := A) (W := W)) :
      ∃ a b, col f a = col f b ∧ a ≠ b := by
    obtain ⟨a,b,he,hne⟩ := Function.not_injective_iff.mp (no_encoding hA (col f))
    exact ⟨a,b,he,hne⟩
  choose a b he hne using hrep
  refine ⟨SimpleGraph.Coloring.mk (fun f => col f (a f)) ?_⟩
  intro f g hfg hcol
  have h₁ := heq_index f g hfg (a f) (a g) hcol
  have h₂ := heq_index f g hfg (b f) (a g) ((he f).symm.trans hcol)
  exact hne f (h₁.trans h₂.symm)

/-- A convenient explicit coding of a powerset palette by binary sequences. -/
noncomputable def bits : Set ℕ ↪ (ℕ → Fin 2) := by
  classical
  refine ⟨fun S n => if n ∈ S then 1 else 0,?_⟩
  intro S T he
  ext n
  have h := congrFun he n
  change (if n ∈ S then (1 : Fin 2) else 0) = (if n ∈ T then (1 : Fin 2) else 0) at h
  by_cases hs : n ∈ S <;> by_cases ht : n ∈ T <;> simp_all

/-- This includes dense, lexicographic, reversed, and non-well-ordered
linear-order domains; no large monotone subsequence is extracted. -/
theorem countable_cover (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (hA : IsEmpty ((oneGraph A).Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (F H hA) := by
  obtain ⟨c⟩ := coloring H hH hA
  exact Erdos595Work.countable_union_of_coloring _ ((F H hA).recolorOfEmbedding bits c)

#print axioms coloring
#print axioms countable_cover
end Erdos595AllSecondShift
