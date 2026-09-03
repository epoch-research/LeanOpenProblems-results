import Submission.OutsideTriangleNormalization
import Submission.CycleVertexLabeling

/-! Degree and order bounds outside a quadrilateral in a triangle-free
four-regular graph, under the no-two-edge-disjoint-cycles hypothesis. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.OutsideQuadrilateralData
open HighGirthCritical EvenCycleCore OutsideTriangleNormalization
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma adjacent_degree_sum_le_order (G : SimpleGraph V)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    {u v : V} (huv : G.Adj u v) : G.degree u + G.degree v ≤ Fintype.card V := by
  have hd : Disjoint (G.neighborSet u) (G.neighborSet v) := by
    apply Set.disjoint_left.mpr
    intro w huw hvw
    exact htri u v w huv hvw huw.symm
  have hc := Set.ncard_union_eq hd
  have hl := Set.ncard_le_ncard (Set.subset_univ (G.neighborSet u ∪ G.neighborSet v))
  rw [hc] at hl
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq,Set.ncard_univ] using hl

lemma four_le_order (G : SimpleGraph V) (hpos : 0 < Fintype.card V)
    (hmin : ∀ v, 2 ≤ G.degree v)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) :
    4 ≤ Fintype.card V := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp (lt_of_lt_of_le (by decide) (hmin v))
  have hh := adjacent_degree_sum_le_order G htri hw
  have hv := hmin v
  have hw := hmin w
  omega

lemma degree_two_vertex (G : SimpleGraph V) {n : ℕ}
    (hn : Fintype.card V = n) (hnhi : n ≤ 7)
    (hmin : ∀ v, 2 ≤ G.degree v) (he : G.edgeSet.ncard + 4 = 2*n) :
    ∃ v, G.degree v = 2 := by
  by_contra! hno
  have hs : (∑ _v : V, 3) ≤ ∑ v : V, G.degree v := by
    apply Finset.sum_le_sum
    intro v _
    have hv := hmin v
    have hv' := hno v
    omega
  have hh := G.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hn] at hs
  simp only [edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  omega

lemma quadrilateral_outside_data {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (hquad : C.verts.ncard = 4)
    (hout : NoTwoCycles (avoid G C.verts)) :
    let A := G.induce (G.support \ C.verts)
    let n := (G.support \ C.verts).ncard
    4 ≤ n ∧ n ≤ 7 ∧ (∀ v, 2 ≤ A.degree v ∧ A.degree v ≤ 3) ∧
      A.edgeSet.ncard + 4 = 2*n ∧ (∃ v, A.degree v = 2) := by
  let A := G.induce (G.support \ C.verts)
  let n := (G.support \ C.verts).ncard
  have hcard : Fintype.card ↥(G.support \ C.verts) = n := by
    simp only [n,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hCsup := CriticalOutsideCycles.cycle_verts_in_support C hc.2
  have hs := CountThreeOrder.support_bound_from_cycle hfour C hc hout
  have hn := Set.ncard_diff_add_ncard_of_subset hCsup
  have he := CycleOutsideBudget.outside_edges_formula hfour C hc hind
  rw [hquad] at he hs hn
  have hem := outside_induce_edges G C.verts
  have hen : A.edgeSet.ncard + 4 = 2*n := by dsimp only [A,n]; omega
  have hnhi : n ≤ 7 := by dsimp only [n]; omega
  have hmin (v : ↥(G.support \ C.verts)) : 2 ≤ A.degree v := by
    have hd := degree_avoid_add_lost G C.verts v.property.2
    have h4 := hfour v.val v.property.1
    have hl := CycleVertexLabeling.quadrilateral_neighbor_card C hc hquad htri v.val
    have hI := outside_induce_degree G C.verts v
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd h4 hI ⊢
    change 2 ≤ Nat.card ((G.induce (G.support \ C.verts)).neighborSet v)
    omega
  have hno : NoTwoCycles A := outside_induce_no_two G C.verts hout
  have hnlo : 4 ≤ n := by
    rw [← hcard]
    apply four_le_order A (by rw [hcard]; omega) hmin
    intro u v w huv hvw hwu
    exact htri u.val v.val w.val huv hvw hwu
  refine ⟨hnlo,hnhi,?_,hen,degree_two_vertex A hcard hnhi hmin hen⟩
  intro v
  refine ⟨hmin v,?_⟩
  have hh := NoTwoCyclesCore.degree_le_three_of_min_degree_two hno (fun v _ => hmin v) v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh

end Erdos184.OutsideQuadrilateralData
