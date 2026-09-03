import Submission.ButterflyOrderedAbsorption
import Submission.OrderedCoreVisits

/-! Two-path absorption when a path misses a noncentral vertex of the two triangles. -/
namespace Erdos583ButterflyMissingDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyOrderedAbsorptionDevelopment Erdos583OrderedCoreVisitsDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma butterfly_missing_vertex_absorption {V : Type*} [Fintype V] {G : SimpleGraph V} {a b : V}
    (f : Fin 5 → V) (hf : Function.Injective f) (ha : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)))
    (P : G.Walk a b) (hP : P.IsPath)
    (hmiss0 : f 0 ∉ P.support) (hmiss : ∃ w : Fin 5, w ≠ 0 ∧ f w ∉ P.support)
    (htouch : ∃ i, f i ∈ P.support)
    (havoid : ∀ i, s(f (baseSource i),f (baseTarget i)) ∉ P.edges) :
    TwoPathCover (G := G) (coreEdges baseSource baseTarget f ∪ P.toSubgraph.edgeSet) := by
  classical
  obtain ⟨w,hw,hwP⟩ := hmiss
  obtain ⟨k,hk,_,q,h,hqi,hh,hb,hc,hmem,hmarked⟩ := ordered_core_visits f hf P htouch
  have hq0 (i : Fin k) : q i ≠ 0 := fun hi ↦ hmiss0 (hi ▸ hmem i)
  have hqw (i : Fin k) : q i ≠ w := fun hi ↦ hwP (hi ▸ hmem i)
  have hcard : k+2 ≤ 5 := by
    have hd : Disjoint (Set.range q) ({0,w} : Set (Fin 5)) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨i,rfl⟩ (hi|hi)
      · exact hq0 i hi
      · exact hqw i hi
    have hh := Set.ncard_le_card (Set.range q ∪ ({0,w} : Set (Fin 5)))
    rw [Set.ncard_union_eq hd,Set.ncard_range_of_injective hqi,Set.ncard_pair hw.symm] at hh
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using hh
  cases k with
  | zero => omega
  | succ n =>
    let n' : Fin 3 := ⟨n,by omega⟩
    let p : Fin (n+1) → Fin 4 := fun i ↦ ⟨(q i).val-1,by have hv := (q i).isLt; omega⟩
    have hep (i : Fin (n+1)) : outer (p i)=q i := by
      have hpos : 0 < (q i).val := by
        by_contra hn
        exact hq0 i (Fin.ext (by omega))
      apply Fin.ext
      simp only [outer,p]
      omega
    have hpi : Function.Injective p := by
      intro i j hij
      apply hqi
      rw [←hep i,←hep j,hij]
    apply ordered_missing_absorption n' p hpi f hf ha P hP h hh hb
    · intro i; rw [hep]; exact hc i
    · intro x hx
      obtain ⟨j,hj⟩ := hmarked x hx
      exact ⟨j,(hep j).trans hj⟩
    · exact havoid

end Erdos583ButterflyMissingDevelopment
