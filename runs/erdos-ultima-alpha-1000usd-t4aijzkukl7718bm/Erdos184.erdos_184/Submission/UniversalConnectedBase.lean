import Submission.UniversalParityBudget

/-! A linear cycle-and-edge bound when deletion of a universal vertex is connected. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open OddPaths Critical
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma universal_connected_base_bound (v : V) (hv : ∀ x : V, x ≠ v → G.Adj v x)
    (hc : (Base (G := G) v).Connected) : number G ≤ 3 * (Fintype.card V - 1) := by
  haveI : Nonempty (Rest v) := hc.nonempty
  let r : Rest v := Classical.choice hc.nonempty
  obtain ⟨F,hF,hacyc,hFcard,hodd⟩ := Vertex.exists_odd_complement_forest_except hc.preconnected r
  let R := Base (G := G) v \ F
  have hR : R ≤ Base (G := G) v := sdiff_le
  have hcov (a b : Rest v) (hab : (Base (G := G) v).Adj a b) :
      R.Adj a b ∨ s(a,b) ∈ F.edgeFinset := by
    by_cases h : F.Adj a b
    · exact Or.inr (SimpleGraph.mem_edgeFinset.mpr h)
    · exact Or.inl ⟨hab,h⟩
  have hrest : Fintype.card (Rest v) = Fintype.card V - 1 := by
    simp only [Rest,Fintype.card_subtype_compl,Fintype.card_unique]
  have hpos : 0 < Fintype.card (Rest v) := Fintype.card_pos
  by_cases hr : Odd (R.degree r)
  · have ho : ∀ x, Odd (Nat.card (R.neighborSet x)) := by
      intro x
      have hh : Odd (R.degree x) := by
        by_cases hx : x = r
        · exact hx ▸ hr
        · exact hodd x hx
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh
    have hb := odd_base_budget v hv R hR ho F.edgeFinset hcov
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hFcard hb hrest hpos ⊢
    omega
  · have he : Even (R.degree r) := Nat.not_odd_iff_even.mp hr
    have hb := leaf_base_budget v hv R hR r (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he) (by
        intro x hx
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hodd x hx) F.edgeFinset hcov
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hFcard hb hrest hpos ⊢
    omega

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.universal_connected_base_bound
