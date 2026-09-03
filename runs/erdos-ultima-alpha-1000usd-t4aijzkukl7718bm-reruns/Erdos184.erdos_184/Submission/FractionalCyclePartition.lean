import Submission.FiniteFractionalDuality

/-! Every even finite graph has an exact fractional cycle partition of linear cost.
This does not assert the existence of an edge-disjoint integral partition of linear size. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
open WeightedPaths FractionalDuality
set_option maxHeartbeats 800000

noncomputable def indicator {I : Type*} (S : Finset I) : I → ℝ :=
  fun i => if i ∈ S then 1 else 0

lemma apply_indicator {I : Type*} [Fintype I] (f : (I → ℝ) →L[ℝ] ℝ) (S : Finset I) :
    f (indicator S) = ∑ i ∈ S, f (indicator {i}) := by
  have hv : indicator S = ∑ i ∈ S, indicator {i} := by
    ext j
    simp [indicator,Finset.sum_apply]
  rw [hv,map_sum]

variable {V : Type*} [Fintype V]

/-- The index type is the finite collection of all genuine cycle subgraphs. -/
abbrev CyclePiece (G : SimpleGraph V) :=
  {H : G.Subgraph // H.coe.Connected ∧ H.coe.IsRegularOfDegree 2}

/-- Fractional exact coverage, indexed by every cycle of the graph. -/
def IsFractionalPartition (G : SimpleGraph V) (t : CyclePiece G → ℝ) : Prop :=
  (∀ H, 0 ≤ t H) ∧ ∀ e ∈ G.edgeSet,
    (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H else 0) = 1

lemma dual_bound (G : SimpleGraph V) (hG : ∀ x, Even (G.degree x))
    (f : (Sym2 V → ℝ) →L[ℝ] ℝ)
    (hf : ∀ H : CyclePiece G, f (indicator H.val.edgeSet.toFinset) ≤ 1) :
    f (indicator G.edgeFinset) ≤ 2 * Fintype.card V := by
  let w : Sym2 V → ℝ := fun e => f (indicator {e})
  rw [apply_indicator]
  have hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1 := by
    intro u p hp
    let H : CyclePiece G := ⟨p.toSubgraph,cycle_subgraph_regular G hp⟩
    have hh := hf H
    rw [apply_indicator] at hh
    rw [walk_weight_eq_edge_sum w p hp.isTrail]
    simpa only [H,w,← Set.toFinite_toFinset] using hh
  have hh := signed_even_sum_le_twice_card G w hG hc
  simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset,w] using hh

/-- The harmless additive one avoids a separate empty-vertex case. -/
lemma exists_fractional_partition (G : SimpleGraph V) (hG : ∀ x, Even (G.degree x)) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ H, t H) ≤ 2 * Fintype.card V + 1 := by
  let v : CyclePiece G → (Sym2 V → ℝ) := fun H => indicator H.val.edgeSet.toFinset
  obtain ⟨t,ht,hcost,hsum⟩ := exists_nonnegative_combination_of_dual_bound
    v (indicator G.edgeFinset) (2 * Fintype.card V + 1) (by positivity)
      (fun f hf => (dual_bound G hG f hf).trans (by linarith))
  refine ⟨t,⟨ht,?_⟩,hcost⟩
  intro e he
  have hh := congrFun hsum e
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,v,indicator,
    Set.mem_toFinset,mul_ite,mul_one,mul_zero,mem_edgeFinset,if_pos he] using hh

lemma exists_fractional_partition_of_nonempty [Nonempty V]
    (G : SimpleGraph V) (hG : ∀ x, Even (G.degree x)) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ H, t H) ≤ 2 * Fintype.card V := by
  let v : CyclePiece G → (Sym2 V → ℝ) := fun H => indicator H.val.edgeSet.toFinset
  have hpos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨t,ht,hcost,hsum⟩ := exists_nonnegative_combination_of_dual_bound
    v (indicator G.edgeFinset) (2 * Fintype.card V) (by positivity) (dual_bound G hG)
  refine ⟨t,⟨ht,?_⟩,hcost⟩
  intro e he
  have hh := congrFun hsum e
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,v,indicator,
    Set.mem_toFinset,mul_ite,mul_one,mul_zero,mem_edgeFinset,if_pos he] using hh

/-- Uniform linear fractional cost, including the empty graph. -/
lemma exists_fractional_partition_linear (G : SimpleGraph V)
    (hG : ∀ x, Even (G.degree x)) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ H, t H) ≤ 2 * Fintype.card V := by
  cases isEmpty_or_nonempty V with
  | inl hV =>
    haveI := hV
    refine ⟨fun _ => 0,⟨fun _ => le_rfl,?_⟩,?_⟩
    · intro e he
      induction e using Sym2.inductionOn with | _ a b => exact isEmptyElim a
    · simp
  | inr hV =>
    haveI := hV
    exact exists_fractional_partition_of_nonempty G hG

end Erdos184.FractionalCycles
