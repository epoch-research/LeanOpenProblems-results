import FormalConjecturesUtil
import Submission.RelativeExpansion

/-! An edge-expansion constant is also a lower bound on the size of a
vertex separator in a simple graph. Paths obtained this way have no fixed
length bound and are not asserted to be copies of a split pattern. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713ExpanderVertexConnectivity
open Erdos713SwitchGluing
variable {V : Type*}
set_option maxHeartbeats 2000000

lemma cut_upper_of_separator [Fintype V] (G : SimpleGraph V) (A S : Finset V)
    (hSep : ∀ x ∈ A, ∀ y, y ∉ A → G.Adj x y → y ∈ S) :
    Nat.card (cross G (A : Set V)).edgeSet ≤ A.card*S.card := by
  have hb : (cross G (A : Set V)).IsBipartiteWith (A : Set V) (Aᶜ : Finset V) := by
    refine ⟨by simpa only [coe_compl] using
      (show Disjoint (A : Set V) ((A : Set V)ᶜ) from disjoint_compl_right),?_⟩
    intro v w hvw
    change G.Adj v w ∧ _ at hvw
    simpa only [Finset.mem_coe,mem_compl] using hvw.2.imp id And.symm
  have hdeg (x : V) (hx : x ∈ A) : (cross G (A : Set V)).degree x ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    apply card_le_card
    intro y hy
    have hh : (cross G (A : Set V)).Adj x y := by simpa only [mem_neighborFinset] using hy
    have hyA : y ∉ A := by
      rcases hh.2 with ⟨_,hyA⟩ | ⟨_,hxA⟩
      · exact hyA
      · exact (hxA hx).elim
    exact hSep x hx y hyA hh.1
  have hh := sum_le_sum hdeg
  rw [isBipartiteWith_sum_degrees_eq_card_edges hb] at hh
  simpa only [sum_const,nsmul_eq_mul,edgeFinset_card,Fintype.card_eq_nat_card] using hh

lemma separator_card_ge [Fintype V] (G : SimpleGraph V) {L : ℝ}
    (hExp : ∀ A : Finset V, 2*A.card ≤ Fintype.card V →
      L*A.card ≤ (Nat.card (cross G (A : Set V)).edgeSet : ℝ))
    (A S : Finset V) (hA : 0 < A.card) (hhalf : 2*A.card ≤ Fintype.card V)
    (hSep : ∀ x ∈ A, ∀ y, y ∉ A → G.Adj x y → y ∈ S) : L ≤ (S.card : ℝ) := by
  have hn := cut_upper_of_separator G A S hSep
  have hr : (Nat.card (cross G (A : Set V)).edgeSet : ℝ) ≤ (S.card : ℝ)*A.card := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using hn)
  exact (mul_le_mul_iff_left₀ (show (0 : ℝ) < A.card by exact_mod_cast hA)).mp
    ((hExp A hhalf).trans hr)

/-- Deleting fewer than lambda vertices leaves a preconnected graph.
This is ordinary connectivity, not bounded-length split-root robustness. -/
theorem preconnected_after_deleting [Fintype V] (G : SimpleGraph V) {L : ℝ}
    (hExp : ∀ A : Finset V, 2*A.card ≤ Fintype.card V →
      L*A.card ≤ (Nat.card (cross G (A : Set V)).edgeSet : ℝ))
    (S : Finset V) (hS : (S.card : ℝ) < L) : (G.induce (S : Set V)ᶜ).Preconnected := by
  intro u v
  by_contra huv
  let F := G.induce (S : Set V)ᶜ
  let A := (univ : Finset V).filter (fun x => ∃ hx : x ∉ S, F.Reachable u ⟨x,hx⟩)
  have huA : u.val ∈ A := mem_filter.mpr ⟨mem_univ _,u.property,Reachable.refl u⟩
  have hvA : v.val ∉ A := by
    intro hv
    obtain ⟨_,hx,hr⟩ := mem_filter.mp hv
    exact huv hr
  have hSepA : ∀ x ∈ A, ∀ y, y ∉ A → G.Adj x y → y ∈ S := by
    intro x hx y hy hxy
    by_contra hyS
    obtain ⟨_,hxS,hr⟩ := mem_filter.mp hx
    have he : F.Adj ⟨x,hxS⟩ ⟨y,hyS⟩ := hxy
    exact hy (mem_filter.mpr ⟨mem_univ _,hyS,hr.trans he.reachable⟩)
  by_cases hhalf : 2*A.card ≤ Fintype.card V
  · exact (not_lt_of_ge (separator_card_ge G hExp A S
      (card_pos.mpr ⟨u.val,huA⟩) hhalf hSepA)) hS
  · let B := (univ : Finset V) \ (S ∪ A)
    have hmem (x : V) : x ∈ B ↔ x ∉ S ∧ x ∉ A := by simp only [B,mem_sdiff,mem_univ,
      mem_union,not_or,true_and]
    have hvB : v.val ∈ B := (hmem _).mpr ⟨v.property,hvA⟩
    have hdis : Disjoint A B := disjoint_left.mpr (fun x hx hB => (hmem x).mp hB |>.2 hx)
    have hcard : A.card+B.card ≤ Fintype.card V := by
      rw [← card_union_of_disjoint hdis]
      exact card_le_univ _
    have hSepB : ∀ x ∈ B, ∀ y, y ∉ B → G.Adj x y → y ∈ S := by
      intro x hx y hy hxy
      by_contra hyS
      have hyA : y ∈ A := by
        by_contra hya
        exact hy ((hmem y).mpr ⟨hyS,hya⟩)
      have hxA := ((hmem x).mp hx).2
      exact ((hmem x).mp hx).1 (hSepA y hyA x hxA hxy.symm)
    exact (not_lt_of_ge (separator_card_ge G hExp B S
      (card_pos.mpr ⟨v.val,hvB⟩) (by omega) hSepB)) hS

#print axioms cut_upper_of_separator
#print axioms separator_card_ge
#print axioms preconnected_after_deleting
end Erdos713ExpanderVertexConnectivity
