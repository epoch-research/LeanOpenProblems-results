import Submission.Work

/-! Reduction to deleting triangle-free matching edges. -/
open SimpleGraph Erdos583Work
namespace Erdos583TriangleFreeMatchingDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Every edge of F has no common neighbor in H. -/
def TriangleFreeEdges {V : Type*} (H F : SimpleGraph V) : Prop :=
  ∀ ⦃a b⦄, F.Adj a b → ∀ x, ¬(H.Adj x a ∧ H.Adj x b)

lemma pairedCopies_vertical_no_common_neighbor {V : Type*}
    (G : SimpleGraph V) (S : Set V) {a b : Bool × V}
    (hab : a.1 ≠ b.1) (hv : a.2 = b.2) (x : Bool × V) :
    ¬((pairedCopies G S).Adj x a ∧ (pairedCopies G S).Adj x b) := by
  rintro ⟨(⟨hxa,hGxa⟩ | ⟨hxa,hva,_⟩), (⟨hxb,hGxb⟩ | ⟨hxb,hvb,_⟩)⟩
  · exact hab (hxa.symm.trans hxb)
  · exact G.loopless x.2 (by simpa only [hv,← hvb] using hGxa)
  · exact G.loopless x.2 (by simpa only [← hv,← hva] using hGxb)
  · have ha : a.1 = !x.1 := Bool.eq_not_iff.mpr hxa.symm
    have hb : b.1 = !x.1 := Bool.eq_not_iff.mpr hxb.symm
    exact hab (ha.trans hb.symm)

lemma pairedCopies_difference_triangleFree {V : Type*}
    (G : SimpleGraph V) (S T : Set V) :
    TriangleFreeEdges (pairedCopies G S) (pairedCopies G S \ pairedCopies G T) := by
  intro a b hab x
  rcases hab with ⟨(hh | ⟨hb,hv,_⟩),hn⟩
  · exact (hn (Or.inl hh)).elim
  · exact pairedCopies_vertical_no_common_neighbor G S hb hv x

universe u

/-- It suffices to handle connected matching deletions in which every deleted
edge is triangle-free in the original all-odd graph. -/
lemma gallai_of_triangleFree_matching_deletion
    (hcase : ∀ {W : Type u} [Fintype W] (H F : SimpleGraph W),
      (∀ w, Odd (Nat.card (H.neighborSet w))) → F ≤ H →
      (∀ w, (F.neighborSet w).Subsingleton) → TriangleFreeEdges H F →
      (H \ F).Connected →
      ∃ D : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) D ∧
        D.card ≤ ⌈(Fintype.card W : ℚ)/2⌉₊)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  by_cases heven : ∃ u, Even (Nat.card (G.neighborSet u))
  · obtain ⟨u,hu⟩ := heven
    let S : Set V := {v | Even (Nat.card (G.neighborSet v))}
    let H := pairedCopies G S
    let K := pairedCopies G {u}
    have hKH : K ≤ H := pairedCopies_mono G (by simpa [S] using hu)
    have heq : H \ (H \ K) = K := sdiff_sdiff_eq_self hKH
    have hc := hcase H (H \ K) (pairedCopies_even_odd G) sdiff_le
      (pairedCopies_sdiff_matching G S {u})
      (pairedCopies_difference_triangleFree G S {u})
    rw [heq] at hc
    obtain ⟨D,hD,hn⟩ := hc (pairedCopies_connected G hG {u} ⟨u,rfl⟩)
    apply erdos_583_of_double_bridge G u hD
    convert hn using 1
    norm_num [Fintype.card_prod]
  · have ho (v : V) : Odd (Nat.card (G.neighborSet v)) :=
      Nat.not_even_iff_odd.mp (fun hv ↦ heven ⟨v,hv⟩)
    have hc := hcase G ⊥ ho bot_le (by intro v a ha; exact ha.elim)
      (by intro a b hab; exact hab.elim)
    have heq : G \ ⊥ = G := by ext a b; simp
    rw [heq] at hc
    exact hc hG

/-- The terminal-weight selection hypothesis is only needed for triangle-free
matching edges; this theorem does not assert that hypothesis. -/
lemma gallai_of_triangleFree_terminal_weight
    (hselect : ∀ {W : Type u} [Fintype W] (H F : SimpleGraph W),
      (∀ w, Odd (Nat.card (H.neighborSet w))) → F ≤ H →
      (∀ w, (F.neighborSet w).Subsingleton) → TriangleFreeEdges H F →
      (H \ F).Connected →
      ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        (∀ K ∈ D, K.edgeSet.Nonempty) ∧ 2*D.card=Fintype.card W ∧
        F.edgeSet.ncard ≤ MatchingTrim.terminalWeight D F)
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  apply gallai_of_triangleFree_matching_deletion _ G hG
  intro W _ H F ho hFH hm ht hconn
  obtain ⟨D,hD,hne,hcard,hweight⟩ := hselect H F ho hFH hm ht hconn
  obtain ⟨E,hE,hbound⟩ := MatchingTrim.trim_decomposition_of_terminal_weight
    F hFH hm hD hne hweight
  refine ⟨E,hE,hbound.trans ?_⟩
  have hceil := Nat.le_ceil ((Fintype.card W : ℚ)/2)
  exact_mod_cast (show (D.card : ℚ) ≤ (⌈(Fintype.card W : ℚ)/2⌉₊ : ℚ) by
    have hc : 2*(D.card : ℚ)=Fintype.card W := by exact_mod_cast hcard
    linarith)

end Erdos583TriangleFreeMatchingDevelopment
