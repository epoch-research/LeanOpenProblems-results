import Submission.SquareGraphRealization
import Submission.RotationFiniteGrid

/-!
Finite square-graph realization with explicit height. The bound is
56*n^8+28 for a graph on n core vertices; it is not a near-linear Sidon
construction. Independence is exactly Sidonness for all carrier subsets.
-/
namespace Erdos773.SquareGraphRealization
open Finset GreedyHypergraphState QuadraticRotationTrade
set_option maxHeartbeats 1500000
noncomputable section

/-- The previous finite realization, now with a verified polynomial height. -/
theorem realize_bounded (n : ℕ) (E : Finset (Edge n)) :
    ∃ f : Vertex E → ℕ, (∀ u, 0 < f u ∧ f u ≤ 56*n^8+28) ∧ Function.Injective f ∧
      (∀ J, IsSidon (J.image (fun u => f u^2) : Set ℕ) ↔ Independent (H E) J) ∧
      squareEdges f=H E ∧ IsSidon ((I E).image (fun u => f u^2) : Set ℕ) ∧
      available (squareEdges f) (I E)=cores E ∧
      (∀ J ⊆ I E, ∀ u ∈ I E, u ∉ J → u ∈ available (squareEdges f) J) ∧
      (∀ e : Index E, edge e \ I E={.inl e.val.val.1,.inl e.val.val.2}) := by
  classical
  obtain ⟨g,hbound,hinj,hg⟩ := bounded_integer_model n
  let f : Vertex E → ℕ := g ∘ embed
  have hf : ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔
      value (embed u)+value (embed v)=value (embed w)+value (embed z) :=
    fun u v w z => hg _ _ _ _
  have hs := squareEdges_eq hf
  refine ⟨f,fun u => hbound _,hinj.comp embed_injective,
    sidon_iff_independent (hinj.comp embed_injective) hf,hs,selected_sidon hf,?_,?_,edge_residual⟩
  · rw [hs,available_eq]
  · intro J hJ u hu hn
    obtain ⟨⟨e,c⟩,_,rfl⟩ := mem_image.mp hu
    rw [hs]
    exact label_available hJ hn

lemma selected_card {n : ℕ} (E : Finset (Edge n)) : (I E).card=2*E.card := by
  classical
  rw [I,card_image_of_injective _ Sum.inr_injective,card_univ]
  simp [Index,Nat.mul_comm]

lemma vertex_card {n : ℕ} (E : Finset (Edge n)) : Fintype.card (Vertex E)=n+2*E.card := by
  classical
  simp [Vertex,Index,Nat.mul_comm]

lemma complete_selected_card (n : ℕ) :
    (I (univ : Finset (Edge n))).card=n^2-n := by
  classical
  have hsurj : Function.Surjective (embed (E := (univ : Finset (Edge n)))) := by
    intro u
    cases u with
    | core a => exact ⟨Sum.inl a,rfl⟩
    | plus e => exact ⟨Sum.inr (⟨e,mem_univ _⟩,false),rfl⟩
    | minus e => exact ⟨Sum.inr (⟨e,mem_univ _⟩,true),rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective embed ⟨embed_injective,hsurj⟩)
  rw [vertex_card,root_card] at hc
  rw [selected_card]
  omega

/-- Actual Sidon squares below the explicit height, retaining all private
    labels. This finite consequence is weaker than existing asymptotic bounds. -/
theorem sidon_set_below_height (n : ℕ) (E : Finset (Edge n)) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (56*n^8+28) ∧ A.card=2*E.card ∧
      IsSidon (A.image (fun a => a^2) : Set ℕ) := by
  classical
  obtain ⟨f,hbound,hinj,_,_,hS,_⟩ := realize_bounded n E
  refine ⟨(I E).image f,?_,?_,?_⟩
  · intro a ha
    obtain ⟨u,_,rfl⟩ := mem_image.mp ha
    exact mem_Icc.mpr ⟨(hbound u).1,(hbound u).2⟩
  · rw [card_image_of_injective _ hinj,selected_card]
  · simpa only [image_image,Function.comp_apply] using hS

#print axioms realize_bounded
#print axioms selected_card
#print axioms vertex_card
#print axioms complete_selected_card
#print axioms sidon_set_below_height
end
end Erdos773.SquareGraphRealization
