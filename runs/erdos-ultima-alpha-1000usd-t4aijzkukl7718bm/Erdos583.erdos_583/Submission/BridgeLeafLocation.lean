import Submission.Work

/-! Leaves in a smallest-order failure with a non-leaf bridge. -/
open SimpleGraph Erdos583Work
namespace Erdos583BridgeLeafLocationDevelopment
open Erdos583Work.VertexCritical Erdos583Work.MarkedDouble Erdos583Work.BridgeGlue
open scoped Classical
set_option maxHeartbeats 1200000

/-- The adjacency part of the two-leaf restriction, without fixing the
ambient vertex type to `Fin n`. -/
lemma leaf_neighbors_adj_of_failure_finite {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] {G : SimpleGraph V} (hsize : Fintype.card V = n)
    (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    {u v a b : V} (huv : u ≠ v) (ha : G.Adj u a) (hb : G.Adj v b)
    (hu : ∀ x, G.Adj u x → x=a) (hv : ∀ x, G.Adj v x → x=b) : G.Adj a b := by
  classical
  let e : Fin n ≃ V := Fintype.equivOfCardEq (by simpa using hsize.symm)
  let J := G.comap e
  have hJ : J.Connected := (Iso.comap e G).connected_iff.mpr hG
  have hfJ : ¬∃ D : Finset J.Subgraph, GoodDecomposition J D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
    rintro ⟨D,hD,hDc⟩
    obtain ⟨E,hE,hEc⟩ := hD.map_comap_equiv e
    exact hfail ⟨E,hE,hEc.trans (by simpa only [Fintype.card_fin,←hsize] using hDc)⟩
  have hna : J.Adj (e.symm u) (e.symm a) := by simpa [J] using ha
  have hnb : J.Adj (e.symm v) (e.symm b) := by simpa [J] using hb
  have hnu : ∀ x, J.Adj (e.symm u) x → x=e.symm a := by
    intro x hx
    apply e.injective
    simpa using hu (e x) (by simpa [J] using hx)
  have hnv : ∀ x, J.Adj (e.symm v) x → x=e.symm b := by
    intro x hx
    apply e.injective
    simpa using hv (e x) (by simpa [J] using hx)
  have hh := (LeafPairReduction.leaf_neighbors_bridge_of_failure hsmall hJ hfJ
    (e.symm.injective.ne huv) hna hnb hnu hnv).2
  simpa [J] using (isBridge_iff.mp hh).1

/-- At exactly half the minimal order, a leaf not equal or adjacent to the
specified vertex supplies the marked budget. Its two copies otherwise
violate the two-leaf restriction in the joined double. -/
lemma marked_of_half_order_leaf_away {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (r : V)
    (hsize : 2*Fintype.card V=n) {u a : V} (hu : u ≠ r) (ha : a ≠ r)
    (hua : G.Adj u a) (hleaf : ∀ x, G.Adj u x → x=a) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧ MarkedAt D r := by
  classical
  let J := pairedCopies G {r}
  have hJ : J.Connected := pairedCopies_connected G hG {r} ⟨r,rfl⟩
  have hcard : Fintype.card (Bool × V)=n := by
    simpa only [Fintype.card_prod,Fintype.card_bool] using hsize
  have hleaf' (b : Bool) (x : Bool × V) (hx : J.Adj (b,u) x) : x=(b,a) := by
    rcases hx with ⟨he,hx⟩|⟨_,_,hr⟩
    · exact Prod.ext he.symm (hleaf x.2 hx)
    · exact (hu hr).elim
  have hex : ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧
      D.card ≤ ⌈(Fintype.card (Bool × V) : ℚ)/2⌉₊ := by
    by_contra hf
    have hh := leaf_neighbors_adj_of_failure_finite hsmall hcard hJ hf
      (show (false,u) ≠ (true,u) by simp)
      (show J.Adj (false,u) (false,a) from Or.inl ⟨rfl,hua⟩)
      (show J.Adj (true,u) (true,a) from Or.inl ⟨rfl,hua⟩)
      (hleaf' false) (hleaf' true)
    rcases hh with ⟨he,_⟩|⟨_,_,hr⟩
    · cases he
    · exact ha hr
  obtain ⟨D,hD,hDc⟩ := hex
  apply marked_of_double_bridge r hD
  simp only [Fintype.card_prod,Fintype.card_bool,ceil_half] at hDc
  omega

/-- A leaf in a balanced bridge side, other than the boundary vertex itself,
is adjacent to that boundary vertex. -/
lemma leaf_on_balanced_side_at_boundary {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hsize : 2*S.ncard=n)
    {w a : Fin n} (hw : w ∈ S) (hwu : w ≠ u)
    (hwa : G.Adj w a) (hleaf : ∀ x, G.Adj w x → x=a) : a=u := by
  classical
  by_contra hau
  have haS : a ∈ S := by
    by_contra haS
    exact hwu (hcross w hw a haS hwa).1
  have hconn := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  have hcard : Fintype.card S=S.ncard := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,hD,hDc,b,p,hp,hm⟩ := marked_of_half_order_leaf_away hsmall
    (G.induce S) hconn ⟨u,hu⟩ (by rw [hcard]; exact hsize)
    (u := ⟨w,hw⟩) (a := ⟨a,haS⟩)
    (fun he ↦ hwu (congrArg Subtype.val he)) (fun he ↦ hau (congrArg Subtype.val he))
    hwa (fun x hx ↦ Subtype.ext (hleaf x.val hx))
  exact hfail (MarkedBudgets.gallai_of_marked_bridge_side hsmall hG S h hu hv hcross hS
    hD p hp hm (by simpa only [hcard] using hDc))

/-- If a smallest failure has a non-leaf bridge, every leaf is attached to
one of its two endpoints. -/
lemma leaf_attached_to_nonleaf_bridge {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v))
    (hu : Nat.card (G.neighborSet u) ≠ 1) (hv : Nat.card (G.neighborSet v) ≠ 1)
    {w a : Fin n} (hwa : G.Adj w a) (hleaf : ∀ x, G.Adj w x → x=a) : a=u ∨ a=v := by
  classical
  have hdw : Nat.card (G.neighborSet w)=1 := by
    have he : G.neighborSet w={a} := by ext x; exact ⟨hleaf x,fun hh ↦ hh ▸ hwa⟩
    rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
  have hwu : w ≠ u := fun he ↦ hu (he ▸ hdw)
  have hwv : w ≠ v := fun he ↦ hv (he ▸ hdw)
  obtain ⟨S,huS,hvS,hcross,hbal⟩ := BalancedBridge.balanced_cut_of_nonleaf_bridge
    hsmall hG hfail hb hu hv
  have hspos : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,huS⟩
  have hsne : S.ncard ≠ 1 := fun hh ↦ hu (BridgeGlue.cut_singleton_degree S
    (isBridge_iff.mp hb).1 huS hcross hh)
  have hsum : S.ncard+Sᶜ.ncard=n := by simpa using S.ncard_add_ncard_compl
  by_cases hwS : w ∈ S
  · exact Or.inl (leaf_on_balanced_side_at_boundary hsmall hG hfail S
      (isBridge_iff.mp hb).1 huS hvS hcross (by omega) (by omega) hwS hwu hwa hleaf)
  · apply Or.inr
    apply leaf_on_balanced_side_at_boundary hsmall hG hfail Sᶜ
      (isBridge_iff.mp hb).1.symm hvS (not_not.mpr huS) _ (by omega) (by omega) hwS hwv hwa hleaf
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm

end Erdos583BridgeLeafLocationDevelopment
