import Submission.Work

/-! A smallest odd-order counterexample has no leaf and hence no bridge.
The even-order case is deliberately not included in these conclusions. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583LeafReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma delete_leaf_connected {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {u v : V} (h : G.Adj u v) (hleaf : ∀ x, G.Adj u x → x=v) :
    (G.induce ({u}ᶜ : Set V)).Connected := by
  letI : Nonempty ↥({u}ᶜ : Set V) := ⟨⟨v,by simpa using h.ne.symm⟩⟩
  refine ⟨hG.preconnected.induce_of_degree_eq_one ?_⟩
  intro x hx
  have hx' : x=u := by simpa using hx
  subst x
  intro a ha b hb
  exact (hleaf a ha).trans (hleaf b hb).symm

lemma within_delete_leaf {V : Type*} {G : SimpleGraph V}
    {u v : V} (hleaf : ∀ x, G.Adj u x → x=v) :
    within G ({u}ᶜ : Set V)=G.deleteEdges {s(u,v)} := by
  ext x y
  simp only [within,deleteEdges_adj,Set.mem_compl_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxy,hxu,hyu⟩
    refine ⟨hxy,?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with ⟨rfl,_⟩|⟨_,rfl⟩
    · exact hxu rfl
    · exact hyu rfl
  · rintro ⟨hxy,hne⟩
    refine ⟨hxy,?_,?_⟩
    · rintro rfl
      have he := hleaf y hxy
      subst y
      exact hne rfl
    · rintro rfl
      have he := hleaf x hxy.symm
      subst x
      exact hne Sym2.eq_swap

lemma restore_deleted_leaf {V : Type*} {G : SimpleGraph V}
    {u v : V} (h : G.Adj u v) (hleaf : ∀ x, G.Adj u x → x=v)
    (D : Finset (G.induce ({u}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition (G.induce ({u}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  have hex := lift_induce_within ({u}ᶜ : Set V) D hD
  rw [within_delete_leaf hleaf] at hex
  obtain ⟨D',hD',hDc⟩ := hex
  obtain ⟨E,hE,hEc⟩ := restore_edge h hD'
  exact ⟨E,hE,hEc.trans (Nat.add_le_add_right hDc 1)⟩

lemma no_leaf_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (u : Fin n) : Nat.card (G.neighborSet u) ≠ 1 := by
  intro hdegree
  rw [Nat.card_coe_set_eq] at hdegree
  obtain ⟨v,hv⟩ := Set.ncard_eq_one.mp hdegree
  have h : G.Adj u v := by change v ∈ G.neighborSet u; rw [hv]; exact rfl
  have hleaf : ∀ x, G.Adj u x → x=v := by intro x hx; exact (hv ▸ hx : x ∈ ({v} : Set (Fin n)))
  have hnpos : 0 < n := (Fin.pos u)
  have hc : ({u}ᶜ : Set (Fin n)).ncard=n-1 := by rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G ({u}ᶜ : Set (Fin n)) (by rw [hc]; omega)
    (delete_leaf_connected hG h hleaf)
  obtain ⟨E,hE,hEc⟩ := restore_deleted_leaf h hleaf D hD
  apply hfail
  refine ⟨E,hE,?_⟩
  rw [hc,ceil_half] at hDc
  simp only [Fintype.card_fin,ceil_half]
  obtain ⟨k,hk⟩ := hn
  omega

lemma bridgeless_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) :
    ∀ e, ¬G.IsBridge e := by
  intro e hb
  induction e using Sym2.ind with
  | h u v =>
    rcases hsmall.bridge_even_order_or_leaf hG hfail hb with he | hu | hv
    · exact Nat.not_even_iff_odd.mpr hn he
    · exact no_leaf_of_odd_failure hsmall hn hG hfail u hu
    · exact no_leaf_of_odd_failure hsmall hn hG hfail v hv

end Erdos583LeafReductionDevelopment
