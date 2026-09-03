import Submission.Work
import Submission.TerminalTail
import Submission.LeafCubicEven
import Submission.LeafTipSeparation
import Submission.ShortLollipop

/-! Under the compatible rooted cycle/tail optimizations, the normal
remainder omits at most one ambient vertex. -/
namespace Erdos583NormalRemainderOneDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion
open Erdos583TerminalTailDevelopment Erdos583LeafCubicEvenDevelopment
open Erdos583LeafTipSeparationDevelopment Erdos583ShortLollipopDevelopment
open scoped Classical
set_option maxHeartbeats 1800000

lemma missing_cycle_and_finish_impossible {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length)
    {x : Fin n} (hxC : x ∈ L.cycle.support) (hxb : x ≠ L.finish)
    (hx : x ∉ (selectedGraph T (Finset.univ.erase L.index)).support)
    (hb : L.finish ∉ (selectedGraph T (Finset.univ.erase L.index)).support) : False := by
  classical
  have hbr : L.finish ≠ r := by
    intro heq
    have hh := NormalRemainder.missing_cycle_subsingleton hsmall hG hfail T r L hs hm hcases
      ⟨hxC,hx⟩ ⟨heq.symm ▸ L.cycle.start_mem_support,hb⟩
    exact hxb hh
  have hlen := shortest_private_finish_tail_length_one hsmall hG hfail T r L hs hm hmin hbr hb
  obtain ⟨hrb,_⟩ := one_edge_form L.tail hlen
  have hleaf := NormalRemainder.missing_finish_leaf T r L hs hm
    (G.mem_support.mpr ⟨r,hrb.symm⟩) hbr hb
  have hbound := TailEar.missing_normal_degree_bound T r L hs hm hx
  by_cases hxr : x=r
  · subst x
    simp only [↓reduceIte] at hbound
    exact cubic_root_no_leaf_neighbor hsmall hG hfail T r hs hm L.hasRoot (by omega) hrb hleaf
  · rw [if_neg hxr] at hbound
    have htwo : Nat.card (G.neighborSet x)=2 := by
      have hlo := NormalRemainder.cycle_degree_ge_two L.cycle L.isCycle hxC
      omega
    have htri : L.cycle.length=3 := by
      rcases hcases with h|h
      · exact h
      · have hh := h x hxC; omega
    have hxrAdj := NormalRemainder.triangle_support_adj L.cycle htri hxC L.cycle.start_mem_support hxr
    exact Set.disjoint_left.mp (leaf_tip_neighbors_disjoint hsmall hG hfail hleaf htwo) hrb.symm hxrAdj

lemma normal_support_compl_card_le_one {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hdeg : 3 ≤ Nat.card (G.neighborSet r))
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).supportᶜ.ncard ≤ 1 := by
  apply Set.ncard_le_one_iff_subsingleton.mpr
  intro x hx y hy
  by_contra hxy
  have hx' := NormalRemainder.missing_on_cycle_or_finish hsmall hG hfail T r L hs hm hmin hx
  have hy' := NormalRemainder.missing_on_cycle_or_finish hsmall hG hfail T r L hs hm hmin hy
  rcases hx' with hxC|hxb <;> rcases hy' with hyC|hyb
  · exact hxy (NormalRemainder.missing_cycle_subsingleton hsmall hG hfail T r L hs hm hcases ⟨hxC,hx⟩ ⟨hyC,hy⟩)
  · subst y
    exact missing_cycle_and_finish_impossible hsmall hG hfail T r L hs hm hdeg hcases hmin hxC hxy hx hy
  · subst x
    exact missing_cycle_and_finish_impossible hsmall hG hfail T r L hs hm hdeg hcases hmin hyC (fun h ↦ hxy h.symm) hy hx
  · exact hxy (hxb.trans hyb.symm)


lemma cubic_root_normal_support {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hdeg : Nat.card (G.neighborSet r)=3) (hq : T.quota r ≤ 2)
    (hcases : L.cycle.length=3 ∨ ∀ x ∈ L.cycle.support, 3 ≤ Nat.card (G.neighborSet x))
    (hmin : ∀ U : TrailFamily G k, ∀ M : LollipopEar.RootedCycleRep U r,
      U.score=T.score → (∀ x, U.quota x=T.quota x) → M.cycle=L.cycle → L.tail.length ≤ M.tail.length) :
    (selectedGraph T (Finset.univ.erase L.index)).support=({r}ᶜ : Set (Fin n)) := by
  classical
  have hqo : Odd (T.quota r) := (QuotaParity.quota_odd_iff T r).mpr (by rw [hdeg]; exact ⟨1,rfl⟩)
  have hq1 : T.quota r=1 := by obtain ⟨m,hm⟩ := hqo; omega
  have havoid := cubic_quota_one_others_avoid T r L hs hdeg hq1
  have hnone := NilSlot.max_score_nonpath_no_nil T hm ⟨L.index,L.member_not_path⟩
  have hr : r ∉ (selectedGraph T (Finset.univ.erase L.index)).support := by
    rw [selected_support_eq T _ (fun j _ ↦ hnone j)]
    rintro ⟨j,hj,hjr⟩
    exact havoid j (Finset.mem_erase.mp hj).1 hjr
  have hsub := Set.ncard_le_one_iff_subsingleton.mp
    (normal_support_compl_card_le_one hsmall hG hfail T r L hs hm (by omega) hcases hmin)
  ext x
  constructor
  · intro hx heq
    exact hr (heq ▸ hx)
  · intro hx
    by_contra hnot
    exact hx (hsub hnot hr)

end Erdos583NormalRemainderOneDevelopment
