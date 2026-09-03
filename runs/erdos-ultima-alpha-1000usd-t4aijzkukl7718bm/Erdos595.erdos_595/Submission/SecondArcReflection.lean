import Submission.ArcRoundTrip

/-!
The SECOND symmetrized arc iteration reflects four-cliques. This gives a
K4-preserving two-step adjoint normal form, not a covering theorem.
-/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
open SimpleGraph Set
namespace Erdos595SecondArcReflection
open Erdos595ArcAdjoint Erdos595ArcRoundTrip Erdos595Work

private abbrev K : SimpleGraph (Fin 4) := ⊤
private abbrev A := Arc K
private abbrev F := arcGraph K
private def root : A := ⟨(0,1),by decide⟩

private instance : DecidableRel F.Adj := fun p q =>
  inferInstanceAs (Decidable (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1))

private def Step (p q : A) : Prop :=
  p = q ∨ ∃ r, F.Adj p q ∧ F.Adj p r ∧ F.Adj q r
private instance : DecidableRel Step := fun p q =>
  inferInstanceAs (Decidable (p = q ∨ ∃ r, F.Adj p q ∧ F.Adj p r ∧ F.Adj q r))

private theorem paths : ∀ p : A, ∃ q r, Step root q ∧ Step q r ∧ Step r p := by
  decide +kernel

private theorem root_triangle : ∃ b c, F.Adj root b ∧ F.Adj root c ∧ F.Adj b c := by
  decide +kernel

private theorem connected (P : A → Prop) (h₀ : P root)
    (hP : ∀ a b c, F.Adj a b → F.Adj a c → F.Adj b c → P a → P b) :
    ∀ a, P a := by
  have hs : ∀ a b, Step a b → P a → P b := by
    intro a b h ha
    rcases h with rfl | ⟨c,hab,hac,hbc⟩
    · exact ha
    · exact hP a b c hab hac hbc ha
  intro a
  obtain ⟨b,c,hb,hc,ha⟩ := paths a
  exact hs c a ha (hs b c hc (hs root b hb h₀))

variable {V : Type*} (G : SimpleGraph V)

/-- There is no loss of K4 information at the second symmetrized arc stage. -/
theorem reflects_four (f : arcGraph (arcGraph K) →g arcGraph (arcGraph G)) :
    ¬G.CliqueFree 4 := by
  obtain ⟨h⟩ := triangle_connected_hom (arcGraph G) F root root_triangle connected
    (arc_unique_triangle_edge G) (toRight f)
  exact (arc_four_hom_iff G).mp ⟨h⟩

private def arcMap {X Y : Type*} {H : SimpleGraph X} {J : SimpleGraph Y} (f : H →g J) :
    arcGraph H →g arcGraph J where
  toFun e := ⟨(f e.val.1,f e.val.2),f.map_adj e.property⟩
  map_rel' := by
    intro e d h
    exact h.imp (congrArg f) (congrArg f)

theorem arc_twice_four_hom_iff :
    Nonempty (arcGraph (arcGraph K) →g arcGraph (arcGraph G)) ↔ ¬G.CliqueFree 4 := by
  refine ⟨fun ⟨f⟩ => reflects_four G f,?_⟩
  intro h
  exact ⟨arcMap (arcMap (SimpleGraph.topEmbeddingOfNotCliqueFree h).toHom)⟩

/-- Every graph maps into its exact two-step arc/right round trip. -/
def unitTwice : G →g right (right (arcGraph (arcGraph G))) :=
  toRight (toRight (SimpleGraph.Hom.id))

/-- Unlike collapsing the independent transversal to a universal apex,
 keeping the exact second arc graph DOES preserve the four-clique condition. -/
theorem right_twice_arc_twice_cliqueFree_iff :
    (right (right (arcGraph (arcGraph G)))).CliqueFree 4 ↔ G.CliqueFree 4 := by
  classical
  constructor
  · intro h
    by_contra hn
    let f := (unitTwice G).comp (SimpleGraph.topEmbeddingOfNotCliqueFree hn).toHom
    exact no_adj_common_neighbors h
      (f.map_adj (show (0 : Fin 4) ≠ 1 by decide))
      (f.map_adj (show (0 : Fin 4) ≠ 2 by decide))
      (f.map_adj (show (1 : Fin 4) ≠ 2 by decide))
      (f.map_adj (show (0 : Fin 4) ≠ 3 by decide))
      (f.map_adj (show (1 : Fin 4) ≠ 3 by decide))
      (f.map_adj (show (2 : Fin 4) ≠ 3 by decide))
  · intro h
    by_contra hn
    obtain ⟨f⟩ := (right_not_cliqueFree_iff (right (arcGraph (arcGraph G))) 4).mp hn
    exact reflects_four G (fromRight f) h

/-- Covers of the exact two-step target pull back to the source. No converse
 cover-preservation theorem is asserted here. -/
theorem source_cover_of_twice_cover
    (h : IsCountableUnionOfTriangleFree (right (right (arcGraph (arcGraph G))))) :
    IsCountableUnionOfTriangleFree G :=
  countable_union_of_hom (unitTwice G) h

#print axioms reflects_four
#print axioms arc_twice_four_hom_iff
#print axioms right_twice_arc_twice_cliqueFree_iff
#print axioms source_cover_of_twice_cover
end Erdos595SecondArcReflection
