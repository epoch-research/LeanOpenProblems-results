import FormalConjecturesUtil
import Submission.ThetaGram
import Submission.C6Upper

/-! A finite necessary condition for oriented theta exclusion.  This does
not supply a rationality theorem for arbitrary forbidden graphs. -/
open SimpleGraph
namespace Erdos713ThetaColumnHexagon
open Erdos713ThetaGram Erdos713C6
set_option maxHeartbeats 1000000

/-- Keep the rows incident with `u`, and puncture the column set at `u`. -/
def columnLink {A B : Type*} (R : A → B → Prop) (u : B) :
    {a : A // R a u} → {b : B // b ≠ u} → Prop :=
  fun a b => R a.val b.val

lemma no_hexagon {A B : Type*} {R : A → B → Prop}
    (hR : ¬ HasTheta R) (u : B)
    (a : Fin 3 → {a : A // R a u}) (b : Fin 3 → {b : B // b ≠ u})
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdiag : ∀ i, columnLink R u (a i) (b i))
    (hnext : ∀ i, columnLink R u (a (i + 1)) (b i)) : False := by
  classical
  let f : Fin 3 → A := fun i => (a i).val
  let g : Fin 4 → B := ![u, (b 0).val, (b 2).val, (b 1).val]
  have hf : Function.Injective f := by
    intro i j hij
    exact ha (Subtype.ext hij)
  have hbi : Function.Injective (fun i : Fin 3 => (b i).val) := by
    intro i j hij
    exact hb (Subtype.ext hij)
  have hb01 : (b 0).val ≠ (b 1).val := fun h => (by decide : (0 : Fin 3) ≠ 1) (hbi h)
  have hb02 : (b 0).val ≠ (b 2).val := fun h => (by decide : (0 : Fin 3) ≠ 2) (hbi h)
  have hb21 : (b 2).val ≠ (b 1).val := fun h => (by decide : (2 : Fin 3) ≠ 1) (hbi h)
  have hg : Function.Injective g := by
    intro i j hij
    have h0 := (b 0).property
    have h1 := (b 1).property
    have h2 := (b 2).property
    fin_cases i <;> fin_cases j <;> simp_all [g]
  apply hR
  refine ⟨f, g, hf, hg, (a 0).property, (a 1).property,
    hdiag 0, ?_, ?_, hdiag 2, hdiag 1, ?_⟩
  · simpa [f, g, columnLink] using hnext 0
  · simpa [f, g, columnLink] using hnext 2
  · simpa [f, g, columnLink] using hnext 1

/-- Each punctured column link of a theta-free relation is an actual
six-cycle-free bipartite graph.  The converse is not asserted. -/
theorem columnLink_free {A B : Type*} {R : A → B → Prop}
    (hR : ¬ HasTheta R) (u : B) :
    (cycleGraph 6).Free (bipGraph (columnLink R u)) := by
  apply free_of_no_hexagon
  exact no_hexagon hR u

open scoped Classical in
/-- The existing six-cycle bound applies to this same link. -/
theorem columnLink_edge_cube {A B : Type*} [Fintype A] [Fintype B]
    {R : A → B → Prop} (hR : ¬ HasTheta R) (u : B) :
    (Nat.card (bipGraph (columnLink R u)).edgeSet)^3 ≤
      (512 * (24^3 + 1)) *
        (Nat.card {a : A // R a u} + Nat.card {b : B // b ≠ u})^4 := by
  classical
  have h := edge_cube_le (bipGraph (columnLink R u)) (columnLink_free hR u)
  simpa only [edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_sum] using h

#print axioms no_hexagon
#print axioms columnLink_free
#print axioms columnLink_edge_cube
end Erdos713ThetaColumnHexagon
