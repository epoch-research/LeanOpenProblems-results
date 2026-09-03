import Submission.ContractionGapData
import Submission.ContractionGapLower

/-! Exact integral and fractional counts for the contraction obstruction.
This is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

lemma feedbackWeight_upper {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) :
    TightDual.CycleUpperWeight G (feedbackWeight v) := by
  intro u p hp
  rw [← cycle_edge_weight p hp,feedbackWeight_total]
  have hd := regular_two_spanning_degree p.toSubgraph (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using (cycle_coe_regular G hp).2) v
  have hb : p.toSubgraph.spanningCoe.degree v ≤ 2 := by
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
    split_ifs at hd <;> omega
  have hr : (p.toSubgraph.spanningCoe.degree v : ℝ) ≤ 2 := by exact_mod_cast hb
  linarith

lemma graph_dual_value : (∑ e ∈ graph.edgeFinset, feedbackWeight 1 e) = 3 := by
  have h := feedbackWeight_total graph 1
  have hd := graph_degree_one
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hd ⊢
  rw [hd] at h
  exact h.trans (by norm_num)

lemma contracted_dual_value : (∑ e ∈ contracted.edgeFinset, feedbackWeight 0 e) = 3 := by
  have h := feedbackWeight_total contracted 0
  have hd := contracted_degree_zero
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hd ⊢
  rw [hd] at h
  exact h.trans (by norm_num)

lemma contracted_cover_once : ∀ x y : Fin 29,
    (Finset.univ.filter (fun i : Fin 3 => s(x,y) ∈ (qwalk i).edges)).card =
      if contracted.Adj x y then 1 else 0 := by
  intro x
  fin_cases x <;> decide +kernel

lemma contracted_fractional_cover (e : Sym2 (Fin 29)) :
    (∑ i : Fin 3, if e ∈ (qwalk i).toSubgraph.edgeSet then (1 : ℝ) else 0) =
      if e ∈ contracted.edgeSet then 1 else 0 := by
  simp only [Walk.mem_edges_toSubgraph,Finset.sum_ite,Finset.sum_const_zero,add_zero,
    Finset.sum_const]
  induction e using Sym2.ind with | _ x y =>
    rw [contracted_cover_once]
    by_cases h : contracted.Adj x y <;> simp [h]

/-- A primal cycle-only fractional cover and a matching dual certificate.
This predicate provides explicit finite certificates, not an assumed LP theorem. -/
def ExactCycleFractionalValue {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ℝ) : Prop :=
  (∃ n : ℕ, ∃ H : Fin n → G.Subgraph, ∃ a : Fin n → ℝ,
    (∀ i, (H i).coe.Connected ∧ (H i).coe.IsRegularOfDegree 2) ∧
    (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = t ∧
    (∀ e, (∑ i, if e ∈ (H i).edgeSet then a i else 0) = if e ∈ G.edgeSet then 1 else 0)) ∧
  (∃ w : Sym2 V → ℝ, TightDual.CycleUpperWeight G w ∧ (∑ e ∈ G.edgeFinset, w e) = t)

lemma graph_exact_fractional : ExactCycleFractionalValue graph 3 := by
  refine ⟨⟨6,(fun i => (fwalk i).toSubgraph),(fun _ => 1/2),?_,?_,fractional_cost,?_⟩,
    ⟨feedbackWeight 1,feedbackWeight_upper graph 1,?_⟩⟩
  · intro i
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular graph (fwalk_cycle i)
  · intro i
    norm_num
  · intro e
    have h := fractional_cover e
    by_cases he : e ∈ graph.edgeSet <;> simpa only [he,if_true,if_false] using h
  · simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using graph_dual_value

lemma contracted_exact_fractional : ExactCycleFractionalValue contracted 3 := by
  refine ⟨⟨3,(fun i => (qwalk i).toSubgraph),(fun _ => 1),?_,?_,?_,?_⟩,
    ⟨feedbackWeight 0,feedbackWeight_upper contracted 0,?_⟩⟩
  · intro i
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular contracted (qwalk_cycle i)
  · intro i
    norm_num
  · norm_num
  · intro e
    have h := contracted_fractional_cover e
    by_cases he : e ∈ contracted.edgeSet <;> simpa only [he,if_true,if_false] using h
  · simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using contracted_dual_value

/-- One edge contraction can decrease the integral--fractional gap by two,
even when both the original and contracted graphs are simple and even.
This refutes a proposed unit-loss induction, not Erdős 184. -/
lemma single_contraction_gap_drop_two :
    graph.Adj 0 15 ∧ (∀ v, Even (graph.degree v)) ∧
    (∀ v, Even ((CertificateStructure.contract graph 0 15).degree v)) ∧
    ExactCycleFractionalValue graph 3 ∧
    ExactCycleFractionalValue (CertificateStructure.contract graph 0 15) 3 ∧
    number graph = 5 ∧ number (CertificateStructure.contract graph 0 15) = 3 := by
  refine ⟨closing_adj,?_,?_,graph_exact_fractional,
    contracted_exact_fractional,graph_number,contracted_number⟩
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using graph_even
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using contracted_even

#print axioms single_contraction_gap_drop_two
#print axioms graph_number
#print axioms base_paths_cover
#print axioms graph_upper
#print axioms contracted_number
#print axioms fractional_cover
end Erdos184Work.ContractionGap
