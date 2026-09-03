import Submission.MatchingRouteExtraction

/-!
All three four-terminal parity corrections supply the alternatives required
by adaptive sewing. The relabeling keeps the two path orientations explicit.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V] {G A : SimpleGraph V}
set_option maxHeartbeats 800000

def reorder (t : Fin 4 → V) (i : Fin 3) : Fin 4 → V :=
  ![t 0,t (firstEnd i),t (secondStart i),t (secondEnd i)]

def reorderIndex (i : Fin 3) : Fin 4 → Fin 4 := ![0,firstEnd i,secondStart i,secondEnd i]

omit [Fintype V] in
lemma reorder_injective {t : Fin 4 → V} (ht : Function.Injective t) (i : Fin 3) :
    Function.Injective (reorder t i) := by
  have hh : Function.Injective (reorderIndex i) := by fin_cases i <;> decide
  have he : reorder t i = t ∘ reorderIndex i := by
    funext j
    fin_cases j <;> rfl
  rw [he]
  exact ht.comp hh

noncomputable def Route.unorder {t : Fin 4 → V} {i : Fin 3}
    (R : Route G A (reorder t i) 0) : Route G A t i :=
  R.repath ⟨R.paths.p,R.paths.q,R.paths.hp,R.paths.hq,R.paths.disjoint⟩ rfl

lemma Route.unorder_strong {t : Fin 4 → V} {i j : Fin 3}
    (R : Route G A (reorder t i) j) (hs : R.paths.Strong) :
    ∃ k : Fin 3, ∃ Q : Route G A t k, Q.paths.Strong ∧ Q.rest.pieces.card = R.rest.pieces.card := by
  fin_cases j
  · exact ⟨i,R.unorder,hs,rfl⟩
  · fin_cases i
    · let P : PairedPaths G t 1 := ⟨R.paths.p,R.paths.q,R.paths.hp,R.paths.hq,R.paths.disjoint⟩
      exact ⟨1,R.repath P rfl,hs,rfl⟩
    · let P : PairedPaths G t 0 := ⟨R.paths.p,R.paths.q,R.paths.hp,R.paths.hq,R.paths.disjoint⟩
      exact ⟨0,R.repath P rfl,hs,rfl⟩
    · let P : PairedPaths G t 0 := ⟨R.paths.p,R.paths.q.reverse,R.paths.hp,R.paths.hq.reverse,
        by simpa only [walkEdges_reverse] using R.paths.disjoint⟩
      have he : P.edges = R.paths.edges := by simp only [PairedPaths.edges,P,walkEdges_reverse]
      refine ⟨0,R.repath P he,?_,rfl⟩
      change R.paths.p.support.Disjoint R.paths.q.reverse.support
      simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hs
  · fin_cases i
    · let P : PairedPaths G t 2 := ⟨R.paths.p,R.paths.q,R.paths.hp,R.paths.hq,R.paths.disjoint⟩
      exact ⟨2,R.repath P rfl,hs,rfl⟩
    · let P : PairedPaths G t 2 := ⟨R.paths.p,R.paths.q.reverse,R.paths.hp,R.paths.hq.reverse,
        by simpa only [walkEdges_reverse] using R.paths.disjoint⟩
      have he : P.edges = R.paths.edges := by simp only [PairedPaths.edges,P,walkEdges_reverse]
      refine ⟨2,R.repath P he,?_,rfl⟩
      change R.paths.p.support.Disjoint R.paths.q.reverse.support
      simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hs
    · let P : PairedPaths G t 1 := ⟨R.paths.p,R.paths.q.reverse,R.paths.hp,R.paths.hq.reverse,
        by simpa only [walkEdges_reverse] using R.paths.disjoint⟩
      have he : P.edges = R.paths.edges := by simp only [PairedPaths.edges,P,walkEdges_reverse]
      refine ⟨1,R.repath P he,?_,rfl⟩
      change R.paths.p.support.Disjoint R.paths.q.reverse.support
      simpa only [Walk.support_reverse,List.disjoint_reverse_right] using hs

/-- Each completion may be decomposed independently. No common or minimum
choice of those three decompositions is required. -/
lemma routing_alternatives_of_completions (t : Fin 4 → V) (ht : Function.Injective t)
    (hAG : A ≤ G) (K : Fin 3 → SimpleGraph V) (k : ℕ)
    (hK : ∀ i, (K i).edgeSet = A.edgeSet ∪
      {s(t 0,t (firstEnd i)),s(t (secondStart i),t (secondEnd i))})
    (hnot : ∀ i, s(t 0,t (firstEnd i)) ∉ A.edgeSet ∧
      s(t (secondStart i),t (secondEnd i)) ∉ A.edgeSet)
    (hb : ∀ i, ∃ D : Finset (K i).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (K i) D ∧ D.card ≤ k) : FourRoutingAlternatives G A t k := by
  intro i
  obtain ⟨D,hc,hd,hcard⟩ := hb i
  rcases first_matching_routes (reorder t i) (reorder_injective ht i) hAG (hK i)
      (hnot i).1 (hnot i).2 D hc hd with ⟨R,hR⟩ | ⟨R,hs,hR⟩ | ⟨R,hs,hR⟩
  · exact Or.inl ⟨R.unorder,by change R.rest.pieces.card+2 ≤ k; omega⟩
  · obtain ⟨j,Q,hQ,hcardQ⟩ := R.unorder_strong hs
    exact Or.inr ⟨j,Q,hQ,by omega⟩
  · obtain ⟨j,Q,hQ,hcardQ⟩ := R.unorder_strong hs
    exact Or.inr ⟨j,Q,hQ,by omega⟩

end Erdos184.TerminalRouting
