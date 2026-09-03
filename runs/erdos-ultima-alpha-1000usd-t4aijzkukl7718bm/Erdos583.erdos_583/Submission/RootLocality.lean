import Submission.Work

/-! A rooted single defect has a unique repeated vertex. Away from that
vertex every member is a forest, a stronger requirement than quota parity. -/
namespace Erdos583RootLocalityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.RootCapacity Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1600000

lemma root_unique {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    {r s : V} (hr : HasRoot T r) (ht : HasRoot T s) : r=s := by
  by_contra hn
  have h1 := rooted_incidence T r hs hr s
  have h2 := rooted_incidence T s hs ht s
  simp only [hn,↓reduceIte,mul_zero,mul_one,add_zero] at h1 h2
  omega

lemma members_off_root_acyclic {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hr : HasRoot T r) (j : Fin k) :
    (within (T.walk j).toSubgraph.spanningCoe ({r}ᶜ : Set V)).IsAcyclic := by
  obtain ⟨A,R,ρ,hρ,hn⟩ := hr
  have hx : (R.tail ρ).toSubgraph.Adj r (R.tail ρ).snd := by
    simpa only [hρ] using (R.tail ρ).toSubgraph_adj_snd hn
  obtain ⟨i,b,h,p,_,_,ht,he,hrep⟩ := rooted_exposed_rep R ρ hρ hx
  obtain ⟨hp,_,hothers⟩ := simple_tail_of_one_defect_rep T hs i h p ht he hrep
  by_cases hji : j=i
  · subst j
    apply (MatchingTrim.path_spanningCoe_isAcyclic p hp).anti
    intro x y hxy
    obtain ⟨hxy,hx,hy⟩ := hxy
    change (T.walk i).toSubgraph.Adj x y at hxy
    rw [he] at hxy
    simp only [Walk.toSubgraph,Subgraph.sup_adj,subgraphOfAdj_adj] at hxy
    rcases hxy with hxy|hxy
    · rcases Sym2.eq_iff.mp hxy with ⟨hxr,_⟩|⟨hyr,_⟩
      · exact (hx hxr.symm).elim
      · exact (hy hyr.symm).elim
    · exact hxy
  · exact (MatchingTrim.path_spanningCoe_isAcyclic (T.walk j) (hothers j hji)).anti (within_le _ _)

lemma member_cycle_contains_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (hs : T.score+1=G.edgeSet.ncard+k)
    (hr : HasRoot T r) (i : Fin k) {a : V} (C : G.Walk a a) (hc : C.IsCycle)
    (he : C.toSubgraph.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet) : r ∈ C.support := by
  classical
  by_contra hn
  let H := within (T.walk i).toSubgraph.spanningCoe ({r}ᶜ : Set V)
  have hH : H.IsAcyclic := members_off_root_acyclic T r hs hr i
  have hE : ∀ e ∈ C.edges, e ∈ H.edgeSet := by
    intro e heC
    induction e using Sym2.ind with
    | h x y =>
      refine ⟨he (C.mem_edges_toSubgraph.mpr heC),?_,?_⟩
      · rintro rfl
        exact hn (Walk.mem_support_of_mem_edges heC (by simp))
      · rintro rfl
        exact hn (Walk.mem_support_of_mem_edges heC (by simp))
  exact hH (C.transfer H hE) (hc.transfer hE)

end Erdos583RootLocalityDevelopment
