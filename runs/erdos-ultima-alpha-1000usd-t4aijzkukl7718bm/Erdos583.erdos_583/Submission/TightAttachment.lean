import Submission.Work
import Submission.EdgeAbsorption

/-! A tight normal group cannot be incident to a one-edge normal member. -/
namespace Erdos583TightAttachmentDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberNormalExpansion
open Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583EdgeAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 2000000

lemma suffix_nonempty_at_tight_group {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (i j : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (hij : i ≠ j) (hi : ¬(T.walk i).IsPath)
    (F : Finset (Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)) (hiF : i ∉ F) (hjF : j ∉ F)
    (hc : SupportConnected (selectedGraph T F))
    (htight : 2*F.card=(selectedGraph T F).support.ncard+1)
    {w x b : Fin n} (h : G.Adj w x) (q : G.Walk x b)
    (hj : (T.walk j).toSubgraph=(Walk.cons h q).toSubgraph)
    (hw : w ∈ (selectedGraph T F).support) : ¬q.Nil := by
  classical
  have hFcard : F.card < ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ F,fun hh ↦ hiF (hh.symm ▸ Finset.mem_univ i)⟩)
    simpa only [Finset.card_univ,Fintype.card_fin] using hlt
  have horder : (selectedGraph T F).support.ncard+1 < n := by
    simp only [Fintype.card_fin,ceil_half] at hFcard
    omega
  obtain ⟨D,hD,hDc⟩ := attach_edge_partition (t := F.card) hsmall (selectedGraph T F) hc
    (x := x) hw horder (by omega)
  intro hn
  cases q with
  | nil =>
    have he : selectedGraph T (insert j F)=selectedGraph T F ⊔ edge w x := by
      ext u v
      change (∃ l ∈ insert j F, (T.walk l).toSubgraph.Adj u v) ↔
        (∃ l ∈ F, (T.walk l).toSubgraph.Adj u v) ∨ (edge w x).Adj u v
      simp only [Finset.mem_insert,or_and_right,exists_or,exists_eq_left,hj,
        Walk.toSubgraph_cons_nil_eq_subgraphOfAdj,subgraphOfAdj_adj,edge_adj]
      have hwx := h.ne
      aesop (add safe hwx)
    have hex : ∃ E : Finset (selectedGraph T (insert j F)).Subgraph,
        GoodDecomposition (selectedGraph T (insert j F)) E ∧ E.card ≤ F.card := by
      rw [he]
      exact ⟨D,hD,hDc⟩
    obtain ⟨E,hE,hEc⟩ := hex
    have hb := normal_group_cannot_save hfail T hs i hi (insert j F)
      (by simp [hiF,hij]) E hE
    rw [Finset.card_insert_of_notMem hjF] at hb
    omega
  | cons hq q => simp at hn

end Erdos583TightAttachmentDevelopment
