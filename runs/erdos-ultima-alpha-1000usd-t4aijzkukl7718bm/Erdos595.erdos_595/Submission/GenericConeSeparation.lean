import Submission.OneSidedSupport
import Submission.GenericTraceRealization

/-!
For the countable generic K4-free base, distinct nonempty one-sided cones
really have distinct ultrafilter indices. Even restriction to ultrafilters
supported on one fixed triangle-free set does not create equal cones.
This is a limitation of equality-based support compression, not a settlement
of the covering conjecture.
-/
set_option autoImplicit false
open Set SimpleGraph Filter
namespace Erdos595GenericConeSeparation
open Erdos595Work Erdos595CountableExtension Erdos595GenericTrace
open Erdos595OneSidedSupport

lemma point_mem_cone (r : Ultrafilter Vertex) (S : Set Vertex)
    (hS : (G.induce S).CliqueFree 3) :
    point S hS ∈ cone G r ↔ S ∈ r := by
  change trace (point S hS) ∈ r ↔ _
  rw [trace_point]

/-- A single triangle-free support makes the cone determine its index. -/
theorem eq_of_cone_eq_of_support (r s : Ultrafilter Vertex)
    (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) (hr : S ∈ r)
    (he : cone G r = cone G s) : r = s := by
  have hs : S ∈ s := by
    apply (point_mem_cone s S hS).mp
    rw [← he]
    exact (point_mem_cone r S hS).mpr hr
  ext A
  have ht : (G.induce (A ∩ S)).CliqueFree 3 := by
    let e : G.induce (A ∩ S) ↪g G.induce S :=
      { toFun := fun x => ⟨x.val,x.property.2⟩
        inj' := fun _ _ h => Subtype.ext (congrArg (fun z : S => (z : Vertex)) h)
        map_rel_iff' := Iff.rfl }
    exact hS.comap e
  have hm : A ∩ S ∈ r ↔ A ∩ S ∈ s := by
    rw [← point_mem_cone r (A ∩ S) ht, ← point_mem_cone s (A ∩ S) ht, he]
  constructor
  · intro hA
    exact Filter.mem_of_superset (hm.mp (Filter.inter_mem hA hr)) Set.inter_subset_left
  · intro hA
    exact Filter.mem_of_superset (hm.mpr (Filter.inter_mem hA hs)) Set.inter_subset_left

/-- Only the empty cone can have more than one ultrafilter index. -/
theorem eq_of_cone_eq_of_nonempty (r s : Ultrafilter Vertex)
    (hr : (cone G r).Nonempty) (he : cone G r = cone G s) : r = s := by
  obtain ⟨p,hp⟩ := hr
  exact eq_of_cone_eq_of_support r s (trace p)
    (ultrafilter_trace_cliqueFree G G_cliqueFree p) hp he

/-- Exact equality criterion, including the collapsed empty-cone fiber. -/
theorem cone_eq_iff (r s : Ultrafilter Vertex) :
    cone G r = cone G s ↔ r = s ∨ (cone G r = ∅ ∧ cone G s = ∅) := by
  constructor
  · intro he
    by_cases hr : (cone G r).Nonempty
    · exact Or.inl (eq_of_cone_eq_of_nonempty r s hr he)
    · have hz : cone G r = ∅ := Set.not_nonempty_iff_eq_empty.mp hr
      exact Or.inr ⟨hz,he.symm.trans hz⟩
  · rintro (rfl | ⟨hr,hs⟩)
    · rfl
    · exact hr.trans hs.symm

/-- In particular, fixing a triangle-free original support does not identify
any of its ultrafilters under the cone map. -/
theorem injective_on_supported (S : Set Vertex) (hS : (G.induce S).CliqueFree 3) :
    Set.InjOn (cone G) {r : Ultrafilter Vertex | S ∈ r} := by
  intro r hr s _ he
  exact eq_of_cone_eq_of_support r s S hS hr he

#print axioms eq_of_cone_eq_of_support
#print axioms cone_eq_iff
#print axioms injective_on_supported
end Erdos595GenericConeSeparation
