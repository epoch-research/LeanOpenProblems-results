import Submission.ArcAdjoint

/-! The right adjoint of a triangle is three-colorable. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595RightThree
open Erdos595ArcAdjoint
abbrev Three := (⊤ : SimpleGraph (Fin 3))

private def rawCode (a b : Finset (Fin 3)) : Fin 3 :=
  if a = {0} then 0 else if a = {1} then 1 else
  if a = {2} then 2 else if b = {0} then 1 else
  if b = {1} then 2 else 0

private lemma raw_code_ne : ∀ a b c d : Finset (Fin 3), Disjoint a b → Disjoint c d →
    (b ∩ c).Nonempty → (d ∩ a).Nonempty → rawCode a b ≠ rawCode c d := by
  decide +kernel

noncomputable def code (p : Biclique Three) : Fin 3 := by
  classical
  exact rawCode p.val.1.toFinset p.val.2.toFinset

lemma code_ne (p q : Biclique Three) (hpq : (right Three).Adj p q) : code p ≠ code q := by
  classical
  apply raw_code_ne
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (p.property a (Set.mem_toFinset.mp ha) a (Set.mem_toFinset.mp hb)) rfl
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (q.property a (Set.mem_toFinset.mp ha) a (Set.mem_toFinset.mp hb)) rfl
  · obtain ⟨a,ha,hb⟩ := hpq.1
    exact ⟨a,Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr ha,Set.mem_toFinset.mpr hb⟩⟩
  · obtain ⟨a,ha,hb⟩ := hpq.2
    exact ⟨a,Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr ha,Set.mem_toFinset.mpr hb⟩⟩

noncomputable def hom : right Three →g Three := ⟨code,fun h => code_ne _ _ h⟩

#print axioms hom
end Erdos595RightThree
