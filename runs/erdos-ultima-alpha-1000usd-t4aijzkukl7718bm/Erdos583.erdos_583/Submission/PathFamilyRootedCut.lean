import Submission.RegularFlowerExposures

/-! Every all-path family admits a regular cut at any prescribed root. -/
namespace Erdos583PathFamilyRootedCutDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted
open Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583RegularRootedCutDevelopment Erdos583RegularFlowerExposuresDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma path_family_regular_rooted {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (v : V) : RegularlyRooted T v := by
  classical
  let I := Finset.univ.filter fun i ↦ v ∈ (T.walk i).support
  have hia (i : Fin k) : i ∈ I ↔ v ∈ (T.walk i).support := by simp [I]
  let L (j : I) := (T.walk j.val).takeUntil v ((hia j.val).mp j.property)
  let Q (j : I) := ((T.walk j.val).dropUntil v ((hia j.val).mp j.property)).reverse
  have hc (j : I) : T.walk j.val=(L j).append (Q j).reverse := by simp [L,Q]
  have hpart (j : I) : (T.walk j.val).toSubgraph = (L j).toSubgraph ⊔ (Q j).toSubgraph := by
    rw [hc j,Walk.toSubgraph_append,Walk.toSubgraph_reverse]
  have htr (j : I) : (L j).IsTrail ∧ (Q j).IsTrail ∧
      Disjoint (L j).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet := by
    have ht : ((L j).append (Q j).reverse).IsTrail := hc j ▸ T.isTrail j.val
    refine ⟨ht.of_append_left, ?_, ?_⟩
    · simpa only [Walk.reverse_isTrail_iff] using ht.of_append_right
    · simpa only [Walk.toSubgraph_reverse] using append_trail_disjoint ht
  let tail (s : {s : Fin k × Bool // s.1 ∈ I}) : G.Walk (T.endpoint s.val) v := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact Q ⟨j,hj⟩
    · exact L ⟨j,hj⟩
  have hslot (s : {s : Fin k × Bool // s.1 ∈ I}) : (tail s).IsTrail := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact (htr ⟨j,hj⟩).2.1
    · exact (htr ⟨j,hj⟩).1
  have hle (s : {s : Fin k × Bool // s.1 ∈ I}) :
      (tail s).toSubgraph ≤ (T.walk s.val.1).toSubgraph := by
    rw [hpart ⟨s.val.1,s.property⟩]
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hdis : Pairwise fun s t ↦ Disjoint (tail s).toSubgraph.edgeSet (tail t).toSubgraph.edgeSet := by
    rintro ⟨⟨i,b⟩,hi⟩ ⟨⟨j,c⟩,hj⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact (htr ⟨i,hi⟩).2.2.symm
      · exact (htr ⟨i,hi⟩).2.2
      · exact (hne rfl).elim
    · exact (T.disjoint hij).mono (Subgraph.edgeSet_mono (hle ⟨(i,b),hi⟩)) (Subgraph.edgeSet_mono (hle ⟨(j,c),hj⟩))
  let R : RootedCut T v I :=
    { tail := tail, trail := hslot, disjoint := hdis,
      decomp := fun i hi ↦ hpart ⟨i,hi⟩,
      outside := fun i hi hv ↦ hi ((hia i).mpr hv) }
  refine ⟨I,R,?_,?_,?_⟩
  · rintro ⟨⟨i,b⟩,hi⟩
    have hh : ((L ⟨i,hi⟩).append (Q ⟨i,hi⟩).reverse).IsPath := hc ⟨i,hi⟩ ▸ hp i
    cases b
    · exact Or.inl (by simpa only [Walk.reverse_reverse] using hh.of_append_right.reverse)
    · exact Or.inl hh.of_append_left
  · intro i hi
    change (L ⟨i,hi⟩).toSubgraph.verts ∩ (Q ⟨i,hi⟩).toSubgraph.verts ⊆ {v}
    dsimp only [L,Q]
    rw [Walk.toSubgraph_reverse,CycleRelocation.path_split_verts_inter _ (hp i)]
  · intro i _
    exact hp i

end Erdos583PathFamilyRootedCutDevelopment
