import FormalConjecturesUtil
import Submission.GlobalThetaLinks

/-! Oriented incidence copies account for both orientations of the connected
apex-theta pattern in a bipartite host. -/

open SimpleGraph
namespace Erdos713ApexThetaOrientations
open Erdos713C6 Erdos713GlobalTheta
set_option maxHeartbeats 1000000
variable {A B : Type*}

def HasApex (R : A → B → Prop) : Prop :=
  ∃ (a : Option (Fin 3) → A) (b : Fin 4 → B),
    Function.Injective a ∧ Function.Injective b ∧
      ∀ i j, apexRel i j → R (a i) (b j)

lemma hasApex_of_root_left {R : A → B → Prop}
    (f : pattern.Copy (bipGraph R)) {d : A}
    (hd : f (.inl none) = .inl d) : HasApex R := by
  have hmap (i : Option (Fin 3)) (j : Fin 4) (hij : apexRel i j) :
      (bipGraph R).Adj (f (.inl i)) (f (.inr j)) := f.toHom.map_adj hij
  have hcols (j : Fin 4) : ∃ b : B, f (.inr j) = .inr b := by
    have h := hmap none j (by trivial)
    rw [hd] at h
    cases he : f (.inr j) with
    | inl a => simp [he,bipGraph] at h
    | inr b => exact ⟨b,rfl⟩
  choose b hb using hcols
  have hrows (i : Option (Fin 3)) : ∃ a : A, f (.inl i) = .inl a := by
    have hsome : ∃ j : Fin 4, apexRel i j := by
      cases i with
      | none => exact ⟨0,by trivial⟩
      | some i =>
        fin_cases i <;> simp only [apexRel, Option.elim_some, thetaRel] <;> decide
    obtain ⟨j,hij⟩ := hsome
    have h := hmap i j hij
    rw [hb] at h
    cases he : f (.inl i) with
    | inl a => exact ⟨a,rfl⟩
    | inr b => simp [he,bipGraph] at h
  choose a ha using hrows
  refine ⟨a,b,?_,?_,?_⟩
  · intro i j hij
    apply Sum.inl_injective
    apply f.injective
    change f (.inl i) = f (.inl j)
    rw [ha,ha,hij]
  · intro i j hij
    apply Sum.inr_injective
    apply f.injective
    change f (.inr i) = f (.inr j)
    rw [hb,hb,hij]
  · intro i j hij
    have h := hmap i j hij
    simpa only [ha,hb] using h

lemma hasApex_or_transpose {R : A → B → Prop}
    (h : pattern ⊑ bipGraph R) : HasApex R ∨ HasApex (fun b a => R a b) := by
  obtain ⟨f⟩ := h
  cases he : f (.inl none) with
  | inl d => exact Or.inl (hasApex_of_root_left f he)
  | inr d =>
    let g : pattern.Copy (bipGraph (fun b a => R a b)) :=
      (transposeIso R).symm.toCopy.comp f
    apply Or.inr
    apply hasApex_of_root_left g (d := d)
    change (transposeIso R).symm (f (.inl none)) = .inl d
    rw [he]
    rfl

lemma contained_of_hasApex {R : A → B → Prop} (h : HasApex R) :
    pattern ⊑ bipGraph R := by
  obtain ⟨a,b,ha,hb,hm⟩ := h
  apply Erdos713Anchors.bipGraph_contained_of_maps apexRel (bipGraph R)
    (fun i => .inl (a i)) (fun j => .inr (b j))
    (Sum.inl_injective.comp ha) (Sum.inr_injective.comp hb)
    (fun _ _ => Sum.inl_ne_inr)
  exact hm

/-- Freeness requires excluding both shores, not just the displayed matrix
orientation. -/
theorem free_iff {R : A → B → Prop} :
    pattern.Free (bipGraph R) ↔ ¬ HasApex R ∧ ¬ HasApex (fun b a => R a b) := by
  constructor
  · intro hf
    refine ⟨fun h => hf (contained_of_hasApex h),?_⟩
    intro h
    exact hf ((contained_of_hasApex h).trans ⟨(transposeIso R).toCopy⟩)
  · rintro ⟨hf,hr⟩ h
    exact (hasApex_or_transpose h).elim hf hr

end Erdos713ApexThetaOrientations
