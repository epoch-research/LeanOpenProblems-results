import Submission.CorePairSplicing
import Submission.CollisionCorePairs

/-! Splicing permuted exterior arms through a near-complete core. All arms
are oriented from their outside endpoint toward the core. -/
namespace Erdos583ReindexedCoreArmsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CorePairSplicingDevelopment Erdos583CollisionCorePairsDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma reindexed_near_complete_splice {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {k : ℕ} (a : Fin k × Bool → S) (x : Fin k × Bool → V)
    (P : ∀ z, G.Walk (x z) (a z).val)
    (hp : ∀ z, (P z).IsPath)
    (hPS : ∀ z, ∀ v ∈ (P z).support, v ∈ S → v=(a z).val)
    (hd : Pairwise (fun z w ↦ Disjoint (P z).toSubgraph.edgeSet (P w).toSubgraph.edgeSet))
    (hc : (BridgeGlue.within G S).edgeSet ∪ (⋃ z, (P z).toSubgraph.edgeSet)=G.edgeSet)
    (u v : S) (huv : u ≠ v)
    (hnear : G.induce S=(⊤ : SimpleGraph S).deleteEdges {s(u,v)})
    (e : Fin k × Bool) (he : a e=v)
    (hbij : Function.Bijective (fun z ↦ if z=e then u else a z))
    (π : Equiv.Perm (Fin k × Bool))
    (hne : a (π ((π.symm e).1,true)) ≠ a (π ((π.symm e).1,false)))
    (hcompat : ∀ i, ∀ w ∈ (P (π (i,true))).support,
      w ∈ (P (π (i,false))).support → False) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  let aa (i : Fin k) := a (π (i,true))
  let bb (i : Fin k) := a (π (i,false))
  have hmap : (fun z : Fin k × Bool ↦ if z=π.symm e then u else if z.2 then aa z.1 else bb z.1)=
      (fun z ↦ if z=e then u else a z) ∘ π := by
    funext z
    have hz : z=π.symm e ↔ π z=e := by
      constructor
      · intro hh; rw [hh,π.apply_symm_apply]
      · intro hh; exact π.injective (hh.trans (π.apply_symm_apply e).symm)
    rcases z with ⟨i,c⟩
    cases c <;> simp only [hz,Function.comp_apply,aa,bb,Bool.false_eq_true,if_false,if_true]
  have hbij' : Function.Bijective (fun z : Fin k × Bool ↦
      if z=π.symm e then u else if z.2 then aa z.1 else bb z.1) := by
    rw [hmap]
    exact hbij.comp π.bijective
  have he' : (if (π.symm e).2 then aa (π.symm e).1 else bb (π.symm e).1)=v := by
    have hlabel (z : Fin k × Bool) : (if z.2 then aa z.1 else bb z.1)=a (π z) := by
      rcases z with ⟨i,c⟩; cases c <;> rfl
    rw [hlabel,π.apply_symm_apply]
    exact he
  obtain ⟨q,hq,hqd,hqc⟩ := near_complete_repaired_pairs u v huv aa bb
    (π.symm e).1 (π.symm e).2 he' hne hbij'
  have hcore : ∃ q : ∀ i, (G.induce S).Walk (aa i) (bb i),
      (∀ i, (q i).IsPath) ∧
      Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) ∧
      (⋃ i, (q i).toSubgraph.edgeSet)=(G.induce S).edgeSet := by
    rw [hnear]
    exact ⟨q,hq,hqd,hqc⟩
  obtain ⟨q',hq',hqd',hqc'⟩ := hcore
  obtain ⟨Q,hQ,hQS,hQd,hQc⟩ := map_induced_partition S aa bb q' hq' hqd' hqc'
  let xx (i : Fin k) := x (π (i,true))
  let yy (i : Fin k) := x (π (i,false))
  let A (i : Fin k) : G.Walk (xx i) (aa i).val := P (π (i,true))
  let B (i : Fin k) : G.Walk (bb i).val (yy i) := (P (π (i,false))).reverse
  have hPe (z : Fin k × Bool) :
      (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)=
      (P (π z)).toSubgraph.edgeSet := by
    rcases z with ⟨i,c⟩
    cases c <;> simp only [A,B,Bool.false_eq_true,if_false,if_true,Walk.toSubgraph_reverse]
  have hdis : Pairwise (fun z w : Fin k × Bool ↦
      Disjoint (if z.2 then (A z.1).toSubgraph.edgeSet else (B z.1).toSubgraph.edgeSet)
        (if w.2 then (A w.1).toSubgraph.edgeSet else (B w.1).toSubgraph.edgeSet)) := by
    intro z w hzw
    rw [hPe,hPe]
    exact hd (fun h ↦ hzw (π.injective h))
  have houter : (⋃ i, (A i).toSubgraph.edgeSet ∪ (B i).toSubgraph.edgeSet)=
      (⋃ z, (P z).toSubgraph.edgeSet) := by
    ext e
    simp only [Set.mem_iUnion,Set.mem_union,A,B,Walk.toSubgraph_reverse]
    constructor
    · rintro ⟨i,he | he⟩
      · exact ⟨π (i,true),he⟩
      · exact ⟨π (i,false),he⟩
    · rintro ⟨z,hz⟩
      obtain ⟨⟨i,c⟩,rfl⟩ := π.surjective z
      refine ⟨i,?_⟩
      cases c
      · exact Or.inr hz
      · exact Or.inl hz
  obtain ⟨p,hp',hd',hc'⟩ := splice_given_core_pairs S aa bb xx yy A B Q hQ hQS hQd hQc
    (fun i ↦ hp _) (fun i ↦ (hp _).reverse)
    (fun i ↦ hPS _) (fun i w hw ↦ hPS _ w (by simpa only [B,Walk.support_reverse,List.mem_reverse] using hw))
    (fun i w hwA hwB ↦ hcompat i w hwA (by simpa only [B,Walk.support_reverse,List.mem_reverse] using hwB))
    hdis (by rw [houter]; exact hc)
  let U : TrailFamily G k :=
    { start := xx
      finish := yy
      walk := p
      isTrail := fun i ↦ (hp' i).isTrail
      disjoint := hd'
      cover := fun e ↦ by rw [←hc']; exact Set.mem_iUnion }
  exact MatchingAppend.path_family_partition U hp'

end Erdos583ReindexedCoreArmsDevelopment
