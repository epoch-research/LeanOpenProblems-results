import Submission.CorePathPieces

/-! Ordering all visits of a walk to a finite embedded core. -/
namespace Erdos583OrderedCoreVisitsDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma ordered_core_visits {N : ℕ} {V : Type*} {G : SimpleGraph V} {a b : V}
    (f : Fin N → V) (hf : Function.Injective f) (P : G.Walk a b)
    (htouch : ∃ i, f i ∈ P.support) :
    ∃ k : ℕ, 0 < k ∧ k ≤ N ∧ ∃ q : Fin k → Fin N, ∃ h : Fin k → ℕ,
      Function.Injective q ∧ StrictMono h ∧ (∀ i, h i ≤ P.length) ∧
      (∀ i, P.getVert (h i)=f (q i)) ∧ (∀ i, f (q i) ∈ P.support) ∧
      (∀ x, f x ∈ P.support → ∃ i, q i=x) := by
  classical
  let A : Set (Fin N) := {i | f i ∈ P.support}
  let k := Fintype.card A
  have hk : 0 < k := Fintype.card_pos_iff.mpr (by
    obtain ⟨i,hi⟩ := htouch
    exact ⟨⟨i,hi⟩⟩)
  have hkN : k ≤ N := by simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i ↦ i ∈ A)
  let e : Fin k ≃ A := (Fintype.equivFin A).symm
  let c (i : Fin k) := f (e i).val
  have hci : Function.Injective c := hf.comp (Subtype.val_injective.comp e.injective)
  have hc (i : Fin k) : c i ∈ P.support := (e i).property
  obtain ⟨h,p,hh,hpi,hb,hpos⟩ := PentagonCoordinates.ordered_vertices P c hci hc
  let q (i : Fin k) := (e (p i)).val
  refine ⟨k,hk,hkN,q,h,Subtype.val_injective.comp (e.injective.comp hpi),hh,hb,hpos,?_,?_⟩
  · intro i; exact (e (p i)).property
  · intro x hx
    obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp hpi) (e.symm ⟨x,hx⟩)
    refine ⟨i,?_⟩
    dsimp [q]
    rw [hi,e.apply_symm_apply]

end Erdos583OrderedCoreVisitsDevelopment
