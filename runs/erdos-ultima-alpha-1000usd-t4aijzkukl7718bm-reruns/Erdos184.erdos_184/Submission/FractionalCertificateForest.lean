import Submission.FractionalRankBound

/-!
At a fractional-envelope attainer, negative dual edges are a forest.
At a strict attainer, even the nonpositive dual edges are a forest.
These statements do not supply integral rounding.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCertificateForest
open FractionalDualCertificate FractionalEnvelope RankCritical BlockRankPotential
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

lemma acyclic_of_nonpositive_of_even_weight_pos {G A : SimpleGraph V}
    {w : Sym2 V → ℝ} (hAG : A ≤ G)
    (hpos : ∀ E : SimpleGraph V, E ≤ G → (∀ v, Even (E.degree v)) → E ≠ ⊥ →
      0 < weight w E)
    (hw : ∀ e ∈ A.edgeSet, w e ≤ 0) : A.IsAcyclic := by
  intro u p hp
  let E := p.toSubgraph.spanningCoe
  have hEA : E ≤ A := p.toSubgraph.spanningCoe_le
  have heE : ∀ v, Even (E.degree v) := even_cycle_spanning hp
  obtain ⟨e, he⟩ := cycle_edgeSet_nonempty p.toSubgraph
    (cycle_subgraph_regular A hp).1 (cycle_subgraph_regular A hp).2
  have hne : E ≠ ⊥ := by
    intro h
    have hh : e ∈ E.edgeSet := he
    rw [h, edgeSet_bot] at hh
    exact hh
  have hlo := hpos E (hEA.trans hAG) heE hne
  have hhi : weight w E ≤ 0 := by
    apply Finset.sum_nonpos
    intro f hf
    exact hw f (edgeSet_mono hEA (mem_edgeFinset.mp hf))
  exact (not_lt_of_ge hhi) hlo

lemma acyclic_of_negative_of_even_weight_nonneg {G A : SimpleGraph V}
    {w : Sym2 V → ℝ} (hAG : A ≤ G)
    (hnonneg : ∀ E : SimpleGraph V, E ≤ G → (∀ v, Even (E.degree v)) →
      0 ≤ weight w E)
    (hw : ∀ e ∈ A.edgeSet, w e < 0) : A.IsAcyclic := by
  intro u p hp
  let E := p.toSubgraph.spanningCoe
  have hEA : E ≤ A := p.toSubgraph.spanningCoe_le
  have heE : ∀ v, Even (E.degree v) := even_cycle_spanning hp
  obtain ⟨e, he⟩ := cycle_edgeSet_nonempty p.toSubgraph
    (cycle_subgraph_regular A hp).1 (cycle_subgraph_regular A hp).2
  have hlo := hnonneg E (hEA.trans hAG) heE
  have hhi : weight w E < 0 := by
    apply Finset.sum_neg
    · intro f hf
      exact hw f (edgeSet_mono hEA (mem_edgeFinset.mp hf))
    · exact ⟨e, mem_edgeFinset.mpr he⟩
  exact (not_lt_of_ge hlo) hhi

def nonpositiveEdges (G : SimpleGraph V) (w : Sym2 V → ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ w s(u,v) ≤ 0
  symm := fun _ _ h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := fun u h => G.loopless u h.1

def negativeEdges (G : SimpleGraph V) (w : Sym2 V → ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ w s(u,v) < 0
  symm := fun _ _ h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := fun u h => G.loopless u h.1

lemma nonpositiveEdges_le (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    nonpositiveEdges G w ≤ G := fun _ _ h => h.1

lemma negativeEdges_le (G : SimpleGraph V) (w : Sym2 V → ℝ) :
    negativeEdges G w ≤ G := fun _ _ h => h.1

lemma nonpositiveEdges_mem (G : SimpleGraph V) (w : Sym2 V → ℝ) (e : Sym2 V) :
    e ∈ (nonpositiveEdges G w).edgeSet ↔ e ∈ G.edgeSet ∧ w e ≤ 0 := by
  induction e using Sym2.inductionOn with | _ u v => rfl

lemma negativeEdges_mem (G : SimpleGraph V) (w : Sym2 V → ℝ) (e : Sym2 V) :
    e ∈ (negativeEdges G w).edgeSet ↔ e ∈ G.edgeSet ∧ w e < 0 := by
  induction e using Sym2.inductionOn with | _ u v => rfl

lemma negativeEdges_acyclic {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hmax : optimum G = envelope G) {w : Sym2 V → ℝ} (hw : Feasible G w)
    (hval : weight w G = optimum G) : (negativeEdges G w).IsAcyclic := by
  apply acyclic_of_negative_of_even_weight_nonneg (negativeEdges_le G w)
  · intro E hEG hE
    exact even_weight_nonneg he hmax hw hval hEG hE
  · intro e hee
    exact ((negativeEdges_mem G w e).mp hee).2

lemma nonpositiveEdges_acyclic {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hstrict : ∀ R : SimpleGraph V, R ≤ G → R ≠ G →
      (∀ v, Even (R.degree v)) → optimum R < optimum G)
    {w : Sym2 V → ℝ} (hw : Feasible G w) (hval : weight w G = optimum G) :
    (nonpositiveEdges G w).IsAcyclic := by
  apply acyclic_of_nonpositive_of_even_weight_pos (nonpositiveEdges_le G w)
  · intro E hEG hE hne
    exact even_weight_pos he hstrict hw hval hEG hE hne
  · intro e hee
    exact ((nonpositiveEdges_mem G w e).mp hee).2

/-- An attained envelope certificate whose nonpositive edges are a forest.
The edge count is bounded by the forest rank of the original ambient graph. -/
theorem exists_forest_certificate (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧
      ∃ w : Sym2 V → ℝ, Feasible H w ∧ weight w H = envelope G ∧
        (nonpositiveEdges H w).IsAcyclic ∧
        (nonpositiveEdges H w).edgeFinset.card ≤ graphRank G := by
  obtain ⟨H, hHG, heH, w, hw, hval, hpos⟩ := exists_strict_certificate G
  have hf : (nonpositiveEdges H w).IsAcyclic := by
    apply acyclic_of_nonpositive_of_even_weight_pos (nonpositiveEdges_le H w) hpos
    intro e hee
    exact ((nonpositiveEdges_mem H w e).mp hee).2
  refine ⟨H, hHG, heH, w, hw, hval, hf, ?_⟩
  have hh := rank_mono ((nonpositiveEdges_le H w).trans hHG)
  rw [forest_rank (nonpositiveEdges H w) hf] at hh
  exact hh

end Erdos184.FractionalCertificateForest
