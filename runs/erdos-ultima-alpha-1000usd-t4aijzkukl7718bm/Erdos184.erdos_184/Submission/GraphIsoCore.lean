import Submission.GraphSubdivisionTheory

/-! Isomorphism invariance for the even-core notions. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphIsoCore
open Critical EvenCore Rigidity
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V W : Type*} [Fintype V] [Fintype W]
variable {G : SimpleGraph V} {H : SimpleGraph W}

lemma even_iso (e : G ≃g H) (hG : ∀ x, Even (G.degree x)) : ∀ y, Even (H.degree y) := by
  intro y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [e.degree_eq]
  exact hG x

lemma even_iso_iff (e : G ≃g H) :
    (∀ x, Even (G.degree x)) ↔ (∀ y, Even (H.degree y)) :=
  ⟨even_iso e,even_iso e.symm⟩

lemma comap_subgraph_le (e : G ≃g H) {R : SimpleGraph W} (hR : R ≤ H) :
    R.comap e.toEquiv.toEmbedding ≤ G := by
  intro x y hxy
  exact e.map_rel_iff.mp (hR hxy)

lemma minimal_iso (e : G ≃g H) (hG : EvenMinimal G) : EvenMinimal H := by
  intro R hRH hR hlt
  let S := R.comap e.toEquiv.toEmbedding
  let f : S ≃g R := SimpleGraph.Iso.comap e.toEquiv R
  have hS : ∀ x, Even (S.degree x) := even_iso f.symm hR
  have hSG : S ≤ G := comap_subgraph_le e hRH
  have hcS := f.card_edgeFinset_eq
  have hcG := e.card_edgeFinset_eq
  have hltS : S.edgeFinset.card < G.edgeFinset.card := by
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hcS hcG hlt ⊢
    omega
  have hn := hG S hSG hS hltS
  rw [BlockRestriction.number_eq_of_iso f,BlockRestriction.number_eq_of_iso e] at hn
  exact hn

lemma minimal_iso_iff (e : G ≃g H) : EvenMinimal G ↔ EvenMinimal H :=
  ⟨minimal_iso e,minimal_iso e.symm⟩

lemma rigid_iso (e : G ≃g H) (hG : ∀ x, Even (G.degree x)) (hr : CycleRigid G) : CycleRigid H := by
  apply (rigid_iff_hereditarily_evenMinimal (even_iso e hG)).mpr
  intro R hRH hR
  let S := R.comap e.toEquiv.toEmbedding
  let f : S ≃g R := SimpleGraph.Iso.comap e.toEquiv R
  have hS : ∀ x, Even (S.degree x) := even_iso f.symm hR
  have hSG : S ≤ G := comap_subgraph_le e hRH
  exact minimal_iso f ((rigid_iff_hereditarily_evenMinimal hG).mp hr S hSG hS)

lemma rigid_iso_iff (e : G ≃g H) (hG : ∀ x, Even (G.degree x)) : CycleRigid G ↔ CycleRigid H :=
  ⟨rigid_iso e hG,rigid_iso e.symm (even_iso e hG)⟩

#print axioms minimal_iso_iff
#print axioms rigid_iso_iff
end Erdos184Work.GraphIsoCore
