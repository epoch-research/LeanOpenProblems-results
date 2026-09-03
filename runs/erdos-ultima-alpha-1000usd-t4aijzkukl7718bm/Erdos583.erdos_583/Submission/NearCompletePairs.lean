import Submission.CompleteEdgeExposure
import Submission.FirstEdgeFamilyDeletion

/-! Prescribed endpoint pairs in an even complete graph minus one edge.
One omitted endpoint label is replaced by a second copy of its nonneighbor;
the duplicated copies must belong to distinct pairs. -/
namespace Erdos583NearCompletePairsDevelopment
open SimpleGraph Erdos583Work
open Erdos583CompleteEdgeExposureDevelopment Erdos583FirstEdgeFamilyDeletionDevelopment
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma complete_minus_edge_prescribed_pairs {V : Type*} [Fintype V] {k : ℕ}
    (a b : Fin k → V)
    (he : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a z.1 else b z.1))
    (i j : Fin k) (hij : i ≠ j) (c : Bool) :
    ∃ q : ∀ l, ((⊤ : SimpleGraph V).deleteEdges {s(a i,if c then a j else b j)}).Walk
        (if l=i then (if c then a j else b j) else a l) (b l),
      (∀ l, (q l).IsPath) ∧
      Pairwise (fun l m ↦ Disjoint (q l).toSubgraph.edgeSet (q m).toSubgraph.edgeSet) ∧
      (⋃ l, (q l).toSubgraph.edgeSet)=
        ((⊤ : SimpleGraph V).deleteEdges {s(a i,if c then a j else b j)}).edgeSet := by
  obtain ⟨p,hp,hd,hc,hfirst⟩ := complete_prescribed_first_edge a b he i j hij c
  have hab : a i ≠ b i := by
    intro h
    have heq := he.injective (a₁ := (i,true)) (a₂ := (i,false)) h
    cases congrArg Prod.snd heq
  exact delete_first_edge_family a b p hp hd hc i (Walk.not_nil_of_ne hab) _ hfirst

/-- A practical collision-label form: replacing one occurrence of v by u
must give a bijection of all endpoint labels. No v-to-v pair is allowed. -/
lemma near_complete_prescribed_pairs {V : Type*} [Fintype V] {k : ℕ}
    (u v : V) (huv : u ≠ v) (a b : Fin k → V) (i : Fin k)
    (hai : a i=v) (hbi : b i ≠ v)
    (he : Function.Bijective (fun z : Fin k × Bool ↦
      if z.2 then (if z.1=i then u else a z.1) else b z.1)) :
    ∃ q : ∀ l, ((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).Walk (a l) (b l),
      (∀ l, (q l).IsPath) ∧
      Pairwise (fun l m ↦ Disjoint (q l).toSubgraph.edgeSet (q m).toSubgraph.edgeSet) ∧
      (⋃ l, (q l).toSubgraph.edgeSet)=((⊤ : SimpleGraph V).deleteEdges {s(u,v)}).edgeSet := by
  classical
  let a' (l : Fin k) := if l=i then u else a l
  have he' : Function.Bijective (fun z : Fin k × Bool ↦ if z.2 then a' z.1 else b z.1) := he
  obtain ⟨⟨j,c⟩,hjc⟩ := he'.surjective v
  have hij : i ≠ j := by
    intro h
    subst j
    cases c
    · exact hbi hjc
    · exact huv (by simpa only [a',if_pos rfl] using hjc)
  have haa : a' i=u := by simp [a']
  have hnew (l : Fin k) : (if l=i then v else a' l)=a l := by
    by_cases hli : l=i
    · subst l; simp [hai]
    · simp [hli,a']
  have hex := complete_minus_edge_prescribed_pairs a' b he' i j hij c
  change (if c then a' j else b j)=v at hjc
  rw [haa,hjc] at hex
  obtain ⟨q,hq,hd,hc⟩ := hex
  let P (l : Fin k) := (q l).copy (hnew l) rfl
  have hPe (l : Fin k) : (P l).toSubgraph=(q l).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  refine ⟨P,?_,?_,?_⟩
  · intro l; simpa only [P,Walk.isPath_copy] using hq l
  · simpa only [hPe] using hd
  · simpa only [hPe] using hc

end Erdos583NearCompletePairsDevelopment
