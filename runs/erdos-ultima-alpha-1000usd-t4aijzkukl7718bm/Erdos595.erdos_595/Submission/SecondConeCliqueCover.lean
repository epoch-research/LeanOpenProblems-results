import Submission.SecondConeRightCover

/-!
A finite certificate shows that K4-freeness of the SECOND right adjoint of
a single cone forces the base to have no closed five-step walk. Combining
this with the pure-biclique transversal theorem excludes every such cone.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open Set SimpleGraph
namespace Erdos595SecondConeClique
open Erdos595Work Erdos595ArcAdjoint Erdos595SecondConeRight

def wheel : SimpleGraph (Fin 6) where
  Adj a b := a ≠ b ∧ (a = 5 ∨ b = 5 ∨ (a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val)
  symm := by intro a b h; exact ⟨h.1.symm, by tauto⟩
  loopless := by intro a h; exact h.1 rfl
instance : DecidableRel wheel.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

abbrev K4 := (⊤ : SimpleGraph (Fin 4))
abbrev A1 := arcGraph K4
abbrev A2 := arcGraph A1
local instance : DecidableRel A1.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))
local instance : DecidableRel A2.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

private def table : Fin 256 → Fin 6 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 4, 2, 0, 0, 1, 5, 5, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 4, 4, 5, 0, 0, 5, 5, 5, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 0, 0, 0, 0, 0, 2, 5, 2, 0, 0, 5, 5, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def label (p : Arc A1) : Fin 6 :=
  table ⟨p.val.1.val.1.val * 64 + p.val.1.val.2.val * 16 +
    p.val.2.val.1.val * 4 + p.val.2.val.2.val, by omega⟩

theorem label_adj : ∀ p q : Arc A1, A2.Adj p q → wheel.Adj (label p) (label q) := by
  decide +kernel

def finiteHom : A2 →g wheel := ⟨label, fun h => label_adj _ _ h⟩

variable {V : Type*} (G : SimpleGraph V)

def wheelToCone (a b c d e : V) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) : wheel →g coneGraph G where
  toFun := ![some a,some b,some c,some d,some e,none]
  map_rel' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [wheel,coneGraph,G.adj_comm]

/-- The base may be arbitrary: the K4-free hypothesis already excludes
both triangles and five-cycles in the base. -/
theorem noFive_of_cliqueFree (h : (right (right (coneGraph G))).CliqueFree 4) : NoFive G := by
  intro a b c d e hab hbc hcd hde hea
  let f := (wheelToCone G a b c d e hab hbc hcd hde hea).comp finiteHom
  let g : K4 →g right (right (coneGraph G)) := toRight (toRight f)
  have hadj : ∀ i j : Fin 4, i ≠ j → (right (right (coneGraph G))).Adj (g i) (g j) :=
    fun i j hij => g.map_adj hij
  exact Erdos595Work.no_adj_common_neighbors h
    (hadj 0 1 (by decide)) (hadj 0 2 (by decide)) (hadj 1 2 (by decide))
    (hadj 0 3 (by decide)) (hadj 1 3 (by decide)) (hadj 2 3 (by decide))

theorem countable_cover (h : (right (right (coneGraph G))).CliqueFree 4) :
    IsCountableUnionOfTriangleFree (right (right (coneGraph G))) :=
  Erdos595SecondConeRight.countable_cover G (noFive_of_cliqueFree G h)

#print axioms label_adj
#print axioms noFive_of_cliqueFree
#print axioms countable_cover
end Erdos595SecondConeClique
