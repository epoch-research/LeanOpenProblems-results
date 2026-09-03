import Submission.Work
import Submission.BridgeGlue

/-! A smallest-order counterexample, followed by the existing edge-minimal
reduction. Minimality is global on finite graphs, not inherited parity. -/
open SimpleGraph Erdos583Work
namespace Erdos583VertexCriticalDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- All connected graphs of strictly smaller order meet their own budgets. -/
def SmallerOrders (n : ℕ) : Prop :=
  ∀ m < n, ∀ H : SimpleGraph (Fin m), H.Connected →
    ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ ⌈(m : ℚ)/2⌉₊

lemma SmallerOrders.on_finite {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hn : Fintype.card V < n) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  let e := (Fintype.equivFin V).symm
  let H := G.comap e
  have hH : H.Connected := (Iso.comap e G).connected_iff.mpr hG
  obtain ⟨D,hD,hDc⟩ := hsmall (Fintype.card V) hn H hH
  obtain ⟨E,hE,hEc⟩ := hD.map_comap_equiv e
  exact ⟨E,hE,hEc.trans hDc⟩

lemma SmallerOrders.on_induce {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V)
    (hn : S.ncard < n) (hG : (G.induce S).Connected) :
    ∃ D : Finset (G.induce S).Subgraph, GoodDecomposition (G.induce S) D ∧
      D.card ≤ ⌈(S.ncard : ℚ)/2⌉₊ := by
  classical
  have hc : Fintype.card S=S.ncard := by
    rw [←Nat.card_eq_fintype_card,Set.ncard_eq_toFinset_card']
    simp
  simpa only [hc] using hsmall.on_finite (G.induce S) (by omega) hG

lemma failure_has_minimal_order {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ n ≤ Fintype.card V, ∃ H : SimpleGraph (Fin n), H.Connected ∧
      (¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) ∧
      SmallerOrders n := by
  classical
  let P (n : ℕ) : Prop := ∃ H : SimpleGraph (Fin n), H.Connected ∧
    ¬∃ D : Finset H.Subgraph, GoodDecomposition H D ∧ D.card ≤ ⌈(n : ℚ)/2⌉₊
  let e := (Fintype.equivFin V).symm
  have hp : P (Fintype.card V) := by
    refine ⟨G.comap e,(Iso.comap e G).connected_iff.mpr hG,?_⟩
    rintro ⟨D,hD,hDc⟩
    obtain ⟨E,hE,hEc⟩ := hD.map_comap_equiv e
    exact hfail ⟨E,hE,hEc.trans hDc⟩
  have hex : ∃ n, P n := ⟨_,hp⟩
  obtain ⟨H,hH,hfailH⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,Nat.find_min' hex hp,H,hH,by simpa using hfailH,?_⟩
  intro m hm J hJ
  by_contra hf
  exact Nat.find_min hex hm ⟨J,hJ,hf⟩

/-- The new vertex-minimality applies after arbitrary spanning edge deletion;
it was chosen globally by order and so does not require parity inheritance. -/
lemma SmallerOrders.bridge_cut_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) : Even S.ncard ∧ Even Sᶜ.ncard := by
  apply Erdos583BridgeGlueDevelopment.failed_minimal_cut_even hG _ hfail S h hu hv hcross hS hcS
  intro U hU hconn
  exact hsmall.on_induce G U (by simpa using hU) hconn

lemma SmallerOrders.bridge_structure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    ∃ S : Set (Fin n), u ∈ S ∧ v ∉ S ∧
      (∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) ∧
      (S.ncard=1 ∨ Sᶜ.ncard=1 ∨ (Even S.ncard ∧ Even Sᶜ.ncard)) := by
  obtain ⟨S,hu,hv,hcross⟩ := Erdos583BridgeGlueDevelopment.bridge_cut hb
  refine ⟨S,hu,hv,hcross,?_⟩
  have hS : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,hu⟩
  have hcS : 0 < Sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v,hv⟩
  by_cases hs : S.ncard=1
  · exact Or.inl hs
  by_cases ht : Sᶜ.ncard=1
  · exact Or.inr (Or.inl ht)
  exact Or.inr (Or.inr (hsmall.bridge_cut_even hG hfail S (isBridge_iff.mp hb).1 hu hv hcross
    (by omega) (by omega)))

/-- In odd order, every bridge of a smallest-order failure is a leaf edge.
In even order the even-even cut possibility remains. -/
lemma SmallerOrders.bridge_even_order_or_leaf {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    Even n ∨ Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet v)=1 := by
  obtain ⟨S,hu,hv,hcross,hS|hS|⟨hS,hcS⟩⟩ := hsmall.bridge_structure hG hfail hb
  · exact Or.inr (Or.inl (Erdos583BridgeGlueDevelopment.cut_singleton_degree S
      (isBridge_iff.mp hb).1 hu hcross hS))
  · refine Or.inr (Or.inr (Erdos583BridgeGlueDevelopment.cut_singleton_degree Sᶜ
      (isBridge_iff.mp hb).1.symm hv ?_ hS))
    intro x hx y hy hxy
    have hy' : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hy' x hx hxy.symm).symm
  · have hn : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
    exact Or.inl (hn ▸ hS.add hcS)

end Erdos583VertexCriticalDevelopment
