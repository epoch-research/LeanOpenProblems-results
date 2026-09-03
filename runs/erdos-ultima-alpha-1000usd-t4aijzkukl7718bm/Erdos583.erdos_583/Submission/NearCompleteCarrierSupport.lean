import Submission.CycleOneCoreGap

/-! Every carrier visits all ordinary vertices of a near-complete even
cycle core, and in particular has at least two core vertices. -/
namespace Erdos583NearCompleteCarrierSupportDevelopment
open SimpleGraph Erdos583Work
open Erdos583PathCoreIntervalsDevelopment Erdos583CycleOneCoreGapDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma near_complete_carriers_two_core_vertices {V : Type*} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (a b : Fin t → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=G.edgeSet)
    (hlen : C.length=2*t+2) (u v : C.toSubgraph.verts) (huv : u ≠ v)
    (hnear : G.induce C.toSubgraph.verts=
      (⊤ : SimpleGraph C.toSubgraph.verts).deleteEdges {s(u,v)}) :
    ∀ i, 2 ≤ (coreVerts (p i) C.toSubgraph.verts).ncard := by
  classical
  let S := C.toSubgraph.verts
  have hsize : S.ncard=2*t+2 := by
    dsimp only [S]
    rw [Walk.verts_toSubgraph,cycle_support_ncard hC,hlen]
  have huv' : u.val ≠ v.val := fun h ↦ huv (Subtype.ext h)
  have hpair : ({u.val,v.val} : Set V) ⊆ S := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact u.property
    · exact (Set.mem_singleton_iff.mp hx) ▸ v.property
  have hrem := Set.ncard_diff_add_ncard_of_subset hpair
  have htwo : ({u.val,v.val} : Set V).ncard=2 := by simp [huv']
  rw [htwo,hsize] at hrem
  have ht : 1 ≤ t := by have h3 := hC.three_le_length; omega
  intro i
  have hsub : S \ {u.val,v.val} ⊆ coreVerts (p i) S := by
    intro x hx
    have hxu : x ≠ u.val := fun h ↦ hx.2 (Set.mem_insert_iff.mpr (Or.inl h))
    have hxv : x ≠ v.val := by
      intro h
      exact hx.2 (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr h))
    have hn : S \ {x} ⊆ G.neighborSet x := by
      intro y hy
      change (G.induce S).Adj ⟨x,hx.1⟩ ⟨y,hy.1⟩
      rw [hnear,deleteEdges_adj,top_adj]
      refine ⟨?_,?_⟩
      · intro he
        exact hy.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val he).symm)
      · intro he
        have he' : s((⟨x,hx.1⟩ : S),⟨y,hy.1⟩)=s(u,v) := Set.mem_singleton_iff.mp he
        rcases Sym2.eq_iff.mp he' with ⟨h,_⟩ | ⟨h,_⟩
        · exact hxu (congrArg Subtype.val h)
        · exact hxv (congrArg Subtype.val h)
    have hb := Set.ncard_mono hn
    have hsz := Set.ncard_diff_singleton_add_one hx.1
    rw [hsize] at hsz
    have hmem := high_degree_on_every_path C hC a b p hp hc x (by omega) i
    exact (mem_coreVerts (p i) S x).mpr ⟨hmem,hx.1⟩
  have hle := Set.ncard_mono hsub
  change 2 ≤ (coreVerts (p i) S).ncard
  omega

end Erdos583NearCompleteCarrierSupportDevelopment
