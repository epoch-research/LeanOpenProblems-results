import Submission.MixedStarTriangle
import Submission.SecondArcNormalForm
import Submission.SecondArcCover

/-!
An exact nonstar reduction of countable triangle-free edge coverability.
The remaining right adjoint is not asserted to have a countable cover.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcNonstarReduction
open Erdos595Work Erdos595ArcAdjoint Erdos595ArcRoundTrip
variable {V : Type*} (G : SimpleGraph V)

abbrev base := arcGraph (arcGraph G)
abbrev core := Erdos595MixedStarTriangle.nonstars (base G)
abbrev target := right (core G)

lemma first_cover : IsCountableUnionOfTriangleFree (right (base G)) := by
  obtain ⟨S,hT,hS⟩ := Erdos595SecondArcNormalForm.second_arc_transversal G
  let c : ((base G).induce S).Coloring (Fin 1) :=
    SimpleGraph.Coloring.mk (fun _ => 0)
      (fun {a b} h _ => hS a.val a.property b.val b.property h)
  exact Erdos595RightProperTransversal.countable_cover (base G) S hT c

/-- This equivalence is valid for every source, without a clique hypothesis. -/
theorem cover_iff : IsCountableUnionOfTriangleFree G ↔
    IsCountableUnionOfTriangleFree (target G) :=
  (Erdos595SecondArcCover.twice_cover_iff G).symm.trans
    (Erdos595MixedStarTriangle.second_cover_iff (base G)
      (arc_unique_triangle_edge (arcGraph G)) (first_cover G))

/-- The reduction's full target retains the required clique bound. -/
theorem cliqueFree (hG : G.CliqueFree 4) : (target G).CliqueFree 4 := by
  have h := (Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG
  let f : target G →g right (right (base G)) :=
    Erdos595RightFiber.rightHom
      (SimpleGraph.Embedding.induce {p | ¬Erdos595MatchingBundle.Star (base G) p}).toHom
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let g := f.comp e.toHom
  exact no_adj_common_neighbors h
    (g.map_adj (show (0 : Fin 4) ≠ 1 by decide))
    (g.map_adj (show (0 : Fin 4) ≠ 2 by decide))
    (g.map_adj (show (1 : Fin 4) ≠ 2 by decide))
    (g.map_adj (show (0 : Fin 4) ≠ 3 by decide))
    (g.map_adj (show (1 : Fin 4) ≠ 3 by decide))
    (g.map_adj (show (2 : Fin 4) ≠ 3 by decide))

#print axioms cover_iff
#print axioms cliqueFree
end Erdos595SecondArcNonstarReduction
