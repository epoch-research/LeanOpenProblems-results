import FormalConjecturesUtil

/-!
A valid two-coloring of a finite K4-free graph need not become a local
proper earlier-neighbor coloring under ANY vertex order. This obstructs
ordering a prescribed coloring, not choosing both a new coloring and order,
and does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PrescribedOrderObstruction

private def edges : List (Fin 7 × Fin 7) :=
  [(0,1),(0,3),(0,4),(0,6),(1,2),(1,3),(2,3),(2,5),
    (3,4),(3,5),(3,6),(4,5),(5,6)]

def Adj (a b : Fin 7) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges
instance : DecidableRel Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
private lemma irreflexive : ∀ a : Fin 7, ¬Adj a a := by decide +kernel

def graph : SimpleGraph (Fin 7) where
  Adj := Adj
  symm := fun _ _ h => h.symm
  loopless := irreflexive

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel Adj)

private def red : List (Fin 7 × Fin 7) :=
  [(0,3),(0,4),(1,2),(1,3),(3,5),(5,6)]

def color (a b : Fin 7) : Fin 2 :=
  if (a,b) ∈ red ∨ (b,a) ∈ red then 1 else 0

lemma color_symm : ∀ a b : Fin 7, color a b = color b a := by decide +kernel

/-- There is no monochromatic triangle under this TWO-color edge coloring. -/
theorem valid : ∀ a b c : Fin 7,
    graph.Adj a b → graph.Adj a c → graph.Adj b c →
      ¬(color a b = color a c ∧ color a b = color b c) := by decide +kernel

theorem cliqueFree : graph.CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree
  simp only [SimpleGraph.isNClique_iff,SimpleGraph.isClique_iff]
  decide +kernel

private def witnesses : Fin 7 → Fin 7 × Fin 7 :=
  ![(3,4),(2,3),(3,5),(0,1),(3,5),(3,6),(0,3)]

/-- Every vertex is the center of an equally colored pair of triangle edges. -/
lemma every_vertex_bad : ∀ a : Fin 7,
    graph.Adj a (witnesses a).1 ∧ graph.Adj a (witnesses a).2 ∧
    graph.Adj (witnesses a).1 (witnesses a).2 ∧
    color a (witnesses a).1 = color a (witnesses a).2 := by decide +kernel

/-- This holds for every ranking in every linear order, not just for the
standard order on Fin 7. The vertex with largest rank always fails. -/
theorem no_order {I : Type*} [LinearOrder I] (r : Fin 7 → I)
    (hr : Function.Injective r) :
    ∃ a b c : Fin 7, r b < r a ∧ r c < r a ∧
      graph.Adj a b ∧ graph.Adj a c ∧ graph.Adj b c ∧ color a b = color a c := by
  classical
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image Finset.univ r (by simp)
  obtain ⟨hab,hac,hbc,he⟩ := every_vertex_bad a
  refine ⟨a,(witnesses a).1,(witnesses a).2,?_,?_,hab,hac,hbc,he⟩
  · exact lt_of_le_of_ne (hmax _ (Finset.mem_univ _))
      (fun h => hab.ne (hr h).symm)
  · exact lt_of_le_of_ne (hmax _ (Finset.mem_univ _))
      (fun h => hac.ne (hr h).symm)

#print axioms valid
#print axioms cliqueFree
#print axioms every_vertex_bad
#print axioms no_order
end Erdos595PrescribedOrderObstruction
