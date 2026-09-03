import Submission.RigidityDegree

/-! Exact and approximate dual certificates on cycle-critical graphs.
Existence of an exact certificate for arbitrary even-minimal cores is not proved. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.TightDual
open Critical EvenCore Rigidity Weighted CycleCertificates
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A cycle-only upper certificate; signed edge weights are allowed. -/
def CycleUpperWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1

omit [Fintype V] in
lemma CycleUpperWeight.mono {w : Sym2 V → ℝ} (hw : CycleUpperWeight G w)
    {R : SimpleGraph V} (hRG : R ≤ G) : CycleUpperWeight R w := by
  intro u p hp
  simpa only [walkWeight,Walk.edges_mapLe_eq_edges] using hw u (p.mapLe hRG) (hp.mapLe hRG)

lemma piece_weight_le {w : Sym2 V → ℝ} {t : ℝ}
    (hw : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ t)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∑ e ∈ H.spanningCoe.edgeFinset, w e) ≤ t := by
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have he := cycle_edge_weight p hp w
  rw [hpH] at he
  exact he.trans_le (hw _ p hp)

lemma piece_weight_ge {w : Sym2 V → ℝ} {t : ℝ}
    (hw : ∀ u (p : G.Walk u u), p.IsCycle → t ≤ walkWeight w p)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    t ≤ ∑ e ∈ H.spanningCoe.edgeFinset, w e := by
  obtain ⟨v⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpH⟩ := LongRing.regular_cycle_walk_at H hH.1 (by
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hH.2) v.val v.property
  have he := cycle_edge_weight p hp w
  rw [hpH] at he
  exact (hw _ p hp).trans_eq he.symm

lemma decomposition_weight_eq (D : Finset G.Subgraph) (hd : IsDecomposition G D)
    (w : Sym2 V → ℝ) :
    (∑ e ∈ G.edgeFinset, w e) = ∑ H ∈ D, ∑ e ∈ H.spanningCoe.edgeFinset, w e := by
  have hg : subfamilyGraph D = G :=
    SimpleGraph.edgeSet_injective ((subfamilyGraph_edges D).trans hd.2)
  have he := subfamily_weight D hd.1 w
  rw [hg] at he
  exact he

lemma CycleUpperWeight.total_le_number {w : Sym2 V → ℝ} (hw : CycleUpperWeight G w)
    (heven : ∀ v, Even (G.degree v)) :
    (∑ e ∈ G.edgeFinset, w e) ≤ (number G : ℝ) := by
  obtain ⟨D,hD,hdec,hc⟩ := minimum_cycles heven
  rw [decomposition_weight_eq D hdec w]
  calc
    _ ≤ ∑ _H ∈ D, (1 : ℝ) := Finset.sum_le_sum (fun H hH => piece_weight_le hw H (hD H hH))
    _ = _ := by simp [hc]

/-- Every cycle in a cycle-critical even graph has weight at least one minus
its integral-minus-dual gap. No certificate exactness is assumed. -/
lemma cycle_weight_lower_of_critical {w : Sym2 V → ℝ}
    (hw : CycleUpperWeight G w) (heven : ∀ v, Even (G.degree v))
    (hcrit : CycleCritical G) {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    (∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1 ≤ walkWeight w p := by
  obtain ⟨D,hD,hdec,hc,hpD⟩ := hcrit.exposes_every_cycle hp
  have hcycles := minimal_even_decomposition_cycles heven D hD hdec (by
    intro E hE hdE
    rw [hc]
    exact number_le E hE hdE)
  have hsum := decomposition_weight_eq D hdec w
  have herase := Finset.sum_erase_add (s := D)
    (f := fun H => ∑ e ∈ H.spanningCoe.edgeFinset, w e) hpD
  have hbound : (∑ H ∈ D.erase p.toSubgraph, ∑ e ∈ H.spanningCoe.edgeFinset, w e) ≤
      ((D.erase p.toSubgraph).card : ℝ) := by
    calc
      _ ≤ ∑ _H ∈ D.erase p.toSubgraph, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        apply piece_weight_le hw H
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hcycles H (Finset.mem_of_mem_erase hH)
      _ = _ := by simp
  have hcount : ((D.erase p.toSubgraph).card : ℝ) + 1 = (number G : ℝ) := by
    exact_mod_cast (Finset.card_erase_add_one hpD).trans hc
  have hpw := cycle_edge_weight p hp w
  linarith

lemma unitWeight_of_critical_exact {w : Sym2 V → ℝ}
    (hw : CycleUpperWeight G w) (heven : ∀ v, Even (G.degree v))
    (hcrit : CycleCritical G)
    (hexact : (number G : ℝ) ≤ ∑ e ∈ G.edgeFinset, w e) : UnitCycleWeight G w := by
  intro u p hp
  have hlo := cycle_weight_lower_of_critical hw heven hcrit p hp
  have hhi := hw u p hp
  linarith

/-- Exact duality on a minimal core forces rigidity and sparsity.
The exactness assumption remains an explicit hypothesis. -/
lemma minimal_exact_dual_rigid_and_sparse {w : Sym2 V → ℝ}
    (hw : CycleUpperWeight G w) (heven : ∀ v, Even (G.degree v))
    (hmin : EvenMinimal G)
    (hexact : (number G : ℝ) ≤ ∑ e ∈ G.edgeFinset, w e) :
    CycleRigid G ∧ G.edgeFinset.card ≤ 2 * Fintype.card V ∧
      number G ≤ Fintype.card V - 1 := by
  have hu := unitWeight_of_critical_exact hw heven (hmin.cycleCritical heven) hexact
  exact ⟨hu.rigid heven,CertificateStructure.UnitCycleWeight.edge_bound hu,
    CertificateStructure.UnitCycleWeight.number_bound hu heven⟩

lemma strict_dual_gap_of_nonrigid {w : Sym2 V → ℝ}
    (hw : CycleUpperWeight G w) (heven : ∀ v, Even (G.degree v))
    (hcrit : CycleCritical G) (hnrig : ¬ CycleRigid G) :
    (∑ e ∈ G.edgeFinset, w e) < (number G : ℝ) := by
  by_contra h
  exact hnrig ((unitWeight_of_critical_exact hw heven hcrit (le_of_not_gt h)).rigid heven)

/-- Different cycle partitions of any even subgraph quantitatively force a
fractional dual gap in a cycle-critical ambient graph. -/
lemma partition_gap_bound {w : Sym2 V → ℝ}
    (hw : CycleUpperWeight G w) (heven : ∀ v, Even (G.degree v))
    (hcrit : CycleCritical G) {R : SimpleGraph V} (hRG : R ≤ G)
    (A B : Finset R.Subgraph)
    (hA : ∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hB : ∀ H ∈ B, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdA : IsDecomposition R A) (hdB : IsDecomposition R B) :
    (B.card : ℝ) - (A.card : ℝ) ≤
      (B.card : ℝ) * ((number G : ℝ) - ∑ e ∈ G.edgeFinset, w e) := by
  have hupper : (∑ e ∈ R.edgeFinset, w e) ≤ (A.card : ℝ) := by
    rw [decomposition_weight_eq A hdA w]
    calc
      _ ≤ ∑ _H ∈ A, (1 : ℝ) :=
        Finset.sum_le_sum (fun H hH => piece_weight_le (hw.mono hRG) H (hA H hH))
      _ = _ := by simp
  have hlower : ∀ u (p : R.Walk u u), p.IsCycle →
      (∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1 ≤ walkWeight w p := by
    intro u p hp
    simpa only [walkWeight,Walk.edges_mapLe_eq_edges] using
      cycle_weight_lower_of_critical hw heven hcrit (p.mapLe hRG) (hp.mapLe hRG)
  have hlow : (B.card : ℝ) * ((∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1) ≤
      ∑ e ∈ R.edgeFinset, w e := by
    rw [decomposition_weight_eq B hdB w]
    calc
      _ = ∑ _H ∈ B, ((∑ e ∈ G.edgeFinset, w e) - (number G : ℝ) + 1) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun H hH => piece_weight_ge hlower H (hB H hH))
  nlinarith

#print axioms cycle_weight_lower_of_critical
#print axioms minimal_exact_dual_rigid_and_sparse
#print axioms strict_dual_gap_of_nonrigid
#print axioms partition_gap_bound
end Erdos184Work.TightDual
