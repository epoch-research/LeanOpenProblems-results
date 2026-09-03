import Submission.FractionalDualCertificate

/-! Degree certificates and positive optimal-dual mixing. These lemmas do not
bound an integral rounding gap or justify a favorable edge contraction. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.DegreeDual
open FractionalCycles FractionalEnvelope FractionalDualCertificate
variable {V : Type*} [Fintype V]

noncomputable def vertexWeight (v : V) (e : Sym2 V) : ℝ :=
  if v ∈ e then 1/2 else 0

omit [Fintype V] in
lemma vertexWeight_nonneg (v : V) (e : Sym2 V) : 0 ≤ vertexWeight v e := by
  unfold vertexWeight
  split_ifs <;> norm_num

lemma vertexWeight_total (G : SimpleGraph V) (v : V) :
    weight (vertexWeight v) G = (G.degree v : ℝ)/2 := by
  simp only [weight,vertexWeight,← Finset.sum_filter,
    ← G.incidenceFinset_eq_filter v,Finset.sum_const,
    card_incidenceFinset_eq_degree,nsmul_eq_mul]
  ring

lemma vertexWeight_feasible (G : SimpleGraph V) (v : V) :
    Feasible G (vertexWeight v) := by
  intro H
  have hh := vertexWeight_total H.val.spanningCoe v
  rw [Subgraph.degree_spanningCoe,cycle_piece_degree] at hh
  have heq : pieceWeight (vertexWeight v) H =
      weight (vertexWeight v) H.val.spanningCoe := by
    simp only [pieceWeight,weight,SimpleGraph.edgeFinset,← Set.toFinite_toFinset]
  rw [heq,hh]
  split_ifs <;> norm_num

lemma weight_average (G : SimpleGraph V) (w z : Sym2 V → ℝ) :
    weight (fun e => (w e+z e)/2) G = (weight w G+weight z G)/2 := by
  simp only [weight,← Finset.sum_div,Finset.sum_add_distrib]

lemma feasible_average {G : SimpleGraph V} {w z : Sym2 V → ℝ}
    (hw : Feasible G w) (hz : Feasible G z) :
    Feasible G (fun e => (w e+z e)/2) := by
  intro H
  have hwH := hw H
  have hzH := hz H
  simp only [pieceWeight,← Finset.sum_div,Finset.sum_add_distrib]
  change (pieceWeight w H+pieceWeight z H)/2 ≤ 1
  linarith

/-- Mixing an optimal dual with an optimal degree certificate preserves
optimality. In particular, dual optimality does not force a small incident
edge weight merely because a graph has many vertices. -/
lemma average_optimal_degree {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (hw : Feasible G w) (hval : weight w G = optimum G) (v : V)
    (hdeg : (G.degree v : ℝ)/2 = optimum G) :
    Feasible G (fun e => (w e+vertexWeight v e)/2) ∧
      weight (fun e => (w e+vertexWeight v e)/2) G = optimum G := by
  refine ⟨feasible_average hw (vertexWeight_feasible G v),?_⟩
  rw [weight_average,vertexWeight_total,hval,hdeg]
  ring

omit [Fintype V] in
lemma average_vertex_pos {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (hpos : ∀ e ∈ G.edgeSet, 0 < w e) (v : V) (e : Sym2 V)
    (he : e ∈ G.edgeSet) : 0 < (w e+vertexWeight v e)/2 := by
  have hw := hpos e he
  have hz := vertexWeight_nonneg v e
  linarith

omit [Fintype V] in
lemma average_incident_gt_quarter {G : SimpleGraph V} {w : Sym2 V → ℝ}
    (hpos : ∀ e ∈ G.edgeSet, 0 < w e) (v : V) (e : Sym2 V)
    (he : e ∈ G.edgeSet) (hv : v ∈ e) :
    1/4 < (w e+vertexWeight v e)/2 := by
  have hw := hpos e he
  simp only [vertexWeight,if_pos hv]
  linarith

/-- A strictly positive optimal dual can be kept strictly positive while
raising every incident edge above one quarter at a degree-tight vertex.
No contraction assertion is part of this conclusion. -/
lemma exists_positive_optimal_incident_large {G : SimpleGraph V}
    {w : Sym2 V → ℝ} (hw : Feasible G w)
    (hval : weight w G = optimum G) (hpos : ∀ e ∈ G.edgeSet, 0 < w e)
    (v : V) (hdeg : (G.degree v : ℝ)/2 = optimum G) :
    ∃ z : Sym2 V → ℝ, Feasible G z ∧ weight z G = optimum G ∧
      (∀ e ∈ G.edgeSet, 0 < z e) ∧
      ∀ e ∈ G.edgeSet, v ∈ e → 1/4 < z e := by
  obtain ⟨hf,hz⟩ := average_optimal_degree hw hval v hdeg
  exact ⟨_,hf,hz,average_vertex_pos hpos v,average_incident_gt_quarter hpos v⟩

end Erdos184.DegreeDual
