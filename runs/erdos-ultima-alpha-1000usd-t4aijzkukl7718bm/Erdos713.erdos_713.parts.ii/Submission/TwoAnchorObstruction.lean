import FormalConjecturesUtil
import Submission.SuspensionGraph

/-! Representative 17 cannot be reduced by a tree-suspension containment.
This is a diagnostic, not a rate bound or a disproof of Erdos 713. -/
open SimpleGraph
namespace Erdos713TwoAnchorObstruction
open Erdos713EightCore Erdos713Suspension
set_option maxHeartbeats 2000000
abbrev F := Graph (representative 17)

def remaining (a b : Fin 4) : Set (Fin 4 ⊕ Fin 4) :=
  {v | v ≠ Sum.inl a ∧ v ≠ Sum.inr b}

instance (a b : Fin 4) : DecidablePred (remaining a b) := fun v =>
  inferInstanceAs (Decidable (v ≠ Sum.inl a ∧ v ≠ Sum.inr b))

lemma four_not_acyclic : ¬ (cycleGraph 4).IsAcyclic := by
  intro h
  let w : (cycleGraph 4).Walk 0 0 := Walk.cons (show (cycleGraph 4).Adj 0 1 from by decide) (Walk.cons (show (cycleGraph 4).Adj 1 2 from by decide) (Walk.cons (show (cycleGraph 4).Adj 2 3 from by decide) (Walk.cons (show (cycleGraph 4).Adj 3 0 from by decide) (Walk.nil))))
  apply h w
  rw [Walk.isCycle_def]
  refine ⟨?_,?_,?_⟩
  · rw [Walk.isTrail_def]
    decide
  · simp [w]
  · decide

lemma six_not_acyclic : ¬ (cycleGraph 6).IsAcyclic := by
  intro h
  let w : (cycleGraph 6).Walk 0 0 := Walk.cons (show (cycleGraph 6).Adj 0 1 from by decide) (Walk.cons (show (cycleGraph 6).Adj 1 2 from by decide) (Walk.cons (show (cycleGraph 6).Adj 2 3 from by decide) (Walk.cons (show (cycleGraph 6).Adj 3 4 from by decide) (Walk.cons (show (cycleGraph 6).Adj 4 5 from by decide) (Walk.cons (show (cycleGraph 6).Adj 5 0 from by decide) (Walk.nil))))))
  apply h w
  rw [Walk.isCycle_def]
  refine ⟨?_,?_,?_⟩
  · rw [Walk.isTrail_def]
    decide
  · simp [w]
  · decide

lemma remaining_contains_cycle (a b : Fin 4) :
    (cycleGraph 4 ⊑ F.induce (remaining a b)) ∨
    (cycleGraph 6 ⊑ F.induce (remaining a b)) := by
  fin_cases a <;> fin_cases b
  · apply Or.inl
    let f : Fin 4 → remaining 0 0 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 0 1 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 0 2 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 0 3 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 1 0 := ![⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 1 1 := ![⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inr
    let f : Fin 6 → remaining 1 2 := ![⟨Sum.inl 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inr
    let f : Fin 6 → remaining 1 3 := ![⟨Sum.inl 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 2 0 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 2 1 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inr
    let f : Fin 6 → remaining 2 2 := ![⟨Sum.inl 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inr
    let f : Fin 6 → remaining 2 3 := ![⟨Sum.inl 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 3 0 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 3 1 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 3 2 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 3,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩
  · apply Or.inl
    let f : Fin 4 → remaining 3 3 := ![⟨Sum.inl 1,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 0,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inl 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩,⟨Sum.inr 2,by simp only [remaining,Set.mem_setOf_eq]; decide⟩]
    exact ⟨⟨⟨f,by decide⟩,by decide⟩⟩

lemma remaining_not_acyclic (a b : Fin 4) : ¬ (F.induce (remaining a b)).IsAcyclic := by
  intro h
  rcases remaining_contains_cycle a b with h4 | h6
  · obtain ⟨f⟩ := h4
    exact four_not_acyclic (h.comap f.toHom f.injective)
  · obtain ⟨f⟩ := h6
    exact six_not_acyclic (h.comap f.toHom f.injective)

lemma common_left (i j : Fin 4) :
    ∃ k : Fin 4, F.Adj (Sum.inl i) (Sum.inr k) ∧ F.Adj (Sum.inl j) (Sum.inr k) := by
  revert i j
  decide

lemma common_right (i j : Fin 4) :
    ∃ k : Fin 4, F.Adj (Sum.inr i) (Sum.inl k) ∧ F.Adj (Sum.inr j) (Sum.inl k) := by
  revert i j
  decide

lemma two_colors_eq {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

def suspensionColor {W : Type*} (H : SimpleGraph W) (c : H.Coloring Bool) :
    (graph H c).Coloring Bool := Coloring.mk (Sum.elim id c) (by
  rintro (x|x) (y|y) h
  · exact h
  · exact h
  · exact h
  · exact c.valid h)

lemma choose_root {W : Type*} (g : Fin 4 → Bool ⊕ W) (hg : Function.Injective g)
    (χ : Bool ⊕ W → Bool) (hχ : ∀ x, χ (Sum.inl x) = x)
    (hcol : ∀ i j, χ (g i) = χ (g j)) :
    ∃ a : Fin 4, ∀ i, i ≠ a → ∃ w : W, g i = Sum.inr w := by
  classical
  by_cases hh : ∃ a x, g a = Sum.inl x
  · obtain ⟨a,x,hax⟩ := hh
    refine ⟨a,?_⟩
    intro i hi
    cases he : g i with
    | inr w => exact ⟨w,rfl⟩
    | inl y =>
      have hc := hcol i a
      rw [he,hax,hχ,hχ] at hc
      exact (hi (hg (he.trans ((congrArg Sum.inl hc).trans hax.symm)))).elim
  · refine ⟨0,?_⟩
    intro i _
    cases he : g i with
    | inr w => exact ⟨w,rfl⟩
    | inl x => exact (hh ⟨i,x,he⟩).elim

/-- Even an arbitrary acyclic base (not necessarily a connected tree)
cannot give a suspension containing representative 17. -/
lemma not_contained_forest_suspension {W : Type*} (H : SimpleGraph W)
    (c : H.Coloring Bool) (hH : H.IsAcyclic) : ¬ F ⊑ graph H c := by
  rintro ⟨f⟩
  let χ := suspensionColor H c
  let d : F.Coloring Bool := χ.comp f.toHom
  have hl (i j : Fin 4) : χ (f (Sum.inl i)) = χ (f (Sum.inl j)) := by
    obtain ⟨k,hik,hjk⟩ := common_left i j
    exact two_colors_eq (d.valid hik) (d.valid hjk)
  have hr (i j : Fin 4) : χ (f (Sum.inr i)) = χ (f (Sum.inr j)) := by
    obtain ⟨k,hik,hjk⟩ := common_right i j
    exact two_colors_eq (d.valid hik) (d.valid hjk)
  obtain ⟨a,ha⟩ := choose_root (fun i => f (Sum.inl i))
    (f.injective.comp Sum.inl_injective) χ (fun _ => rfl) hl
  obtain ⟨b,hb⟩ := choose_root (fun i => f (Sum.inr i))
    (f.injective.comp Sum.inr_injective) χ (fun _ => rfl) hr
  have hex (v : remaining a b) : ∃ w : W, f v.val = Sum.inr w := by
    rcases v with ⟨i|j,hv⟩
    · exact ha i (fun he => hv.1 (congrArg Sum.inl he))
    · exact hb j (fun he => hv.2 (congrArg Sum.inr he))
  choose m hm using hex
  let g : (F.induce (remaining a b)).Copy H :=
    { toHom := ⟨m,by
        intro u v huv
        have hh := f.toHom.map_adj huv
        change (graph H c).Adj (f u.val) (f v.val) at hh
        rw [hm,hm] at hh
        exact hh⟩
      injective' := by
        intro u v he
        apply Subtype.ext
        apply f.injective
        change f u.val = f v.val
        change m u = m v at he
        rw [hm,hm,he] }
  exact remaining_not_acyclic a b (hH.comap g.toHom g.injective)

#print axioms remaining_contains_cycle
#print axioms remaining_not_acyclic
#print axioms not_contained_forest_suspension
end Erdos713TwoAnchorObstruction
