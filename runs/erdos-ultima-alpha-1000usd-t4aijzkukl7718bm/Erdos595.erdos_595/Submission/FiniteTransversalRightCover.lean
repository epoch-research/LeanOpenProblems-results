import Submission.RightProperTransversal
import Submission.CompleteFilterEdgeCover
import Submission.SecondConeCliqueCover

/-!
An n-colorable triangle transversal in a base gives n+1 triangle-free edge
pieces in its right adjoint. In particular every K4-free second right
adjoint of a single cone has a THREE-piece edge cover.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiniteTransversalRight
open Erdos595ArcAdjoint Erdos595RightProperTransversal Erdos595CompleteFilterEdgeCover
variable {V : Type*} (H : SimpleGraph V) (S : Set V) {n : ℕ}

theorem finite_cover (hT : (H.induce Sᶜ).CliqueFree 3)
    (c : (H.induce S).Coloring (Fin n)) : CoversWith (right H) (n+1) := by
  classical
  let same : SimpleGraph (Biclique H) :=
    { Adj p q := (right H).Adj p q ∧ code H S c p = code H S c q
      symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
      loopless := fun p h => (right H).loopless p h.1 }
  let cut (i : Fin n) : SimpleGraph (Biclique H) :=
    right H ⊓ (⊤ : SimpleGraph Bool).comap (fun p => decide (i ∈ code H S c p))
  let K : Fin (n+1) → SimpleGraph (Biclique H) := Fin.cases same cut
  refine ⟨K,?_,?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · intro t ht
      obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact no_triangle H S hT c p q r hpq.1 hpr.1 hqr.1 hpq.2 hpr.2
    · have cf : (cut i).Coloring Bool := SimpleGraph.Coloring.mk
        (fun p => decide (i ∈ code H S c p)) (fun h => h.2)
      exact cf.colorable.cliqueFree (by decide)
  · intro p q hpq
    by_cases he : code H S c p = code H S c q
    · exact ⟨0,hpq,he⟩
    · have hex : ∃ i : Fin n, decide (i ∈ code H S c p) ≠ decide (i ∈ code H S c q) := by
        by_contra hh
        push_neg at hh
        apply he
        ext i
        exact decide_eq_decide.mp (hh i)
      obtain ⟨i,hi⟩ := hex
      exact ⟨i.succ,hpq,hi⟩

open Erdos595Work Erdos595SecondConeRight

/-- The earlier countable bound for single cones is in fact uniformly three. -/
theorem cone_three_cover (G : SimpleGraph V) (h : NoFive G) :
    CoversWith (right (right (coneGraph G))) 3 := by
  let e : Bool ↪ Fin 2 := ⟨fun b => if b then 1 else 0,by decide⟩
  let C := (right (coneGraph G)).induce {p | Pure G p}
  let c : C.Coloring (Fin 2) := C.recolorOfEmbedding e (pureColor G)
  exact finite_cover (right (coneGraph G)) {p | Pure G p} (pure_transversal G h) c

theorem cone_three_cover_of_cliqueFree (G : SimpleGraph V)
    (h : (right (right (coneGraph G))).CliqueFree 4) :
    CoversWith (right (right (coneGraph G))) 3 :=
  cone_three_cover G (Erdos595SecondConeClique.noFive_of_cliqueFree G h)

#print axioms finite_cover
#print axioms cone_three_cover
#print axioms cone_three_cover_of_cliqueFree
end Erdos595FiniteTransversalRight
