import Submission.TightDual

/-! A linear bound for the signed CYCLE-ONLY dual on even graphs.
This does not assert integral rounding or settle Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleDualBound
open Critical EvenCore Rigidity Weighted CycleCertificates TightDual
set_option maxHeartbeats 400000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An edge heavier than an entire permitted cycle is exceptional. -/
def heavyGraph (G : SimpleGraph V) (w : Sym2 V → ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ 1 < w s(u,v)
  symm := by intro u v h; simpa only [Sym2.eq_swap] using And.intro h.1.symm h.2
  loopless := by intro u h; exact G.loopless u h.1

lemma heavyGraph_le (w : Sym2 V → ℝ) : heavyGraph G w ≤ G := fun _ _ h => h.1

lemma heavyGraph_acyclic {w : Sym2 V → ℝ} (hw : CycleUpperWeight G w) :
    (heavyGraph G w).IsAcyclic := by
  intro u p hp
  have hupper := hw.mono (heavyGraph_le w) u p hp
  have hcard := cycle_edge_count (heavyGraph G w) hp
  have hlower : (p.length : ℝ) ≤ walkWeight w p := by
    calc
      _ = ∑ _e ∈ p.toSubgraph.spanningCoe.edgeFinset, (1 : ℝ) := by simp [hcard]
      _ ≤ ∑ e ∈ p.toSubgraph.spanningCoe.edgeFinset, w e := by
        apply Finset.sum_le_sum
        intro e he
        have h := SimpleGraph.edgeSet_mono p.toSubgraph.spanningCoe_le
          (SimpleGraph.mem_edgeFinset.mp he)
        induction e using Sym2.ind with | _ x y => exact h.2.le
      _ = _ := cycle_edge_weight p hp w
  have hthree : (3 : ℝ) ≤ p.length := by exact_mod_cast hp.three_le_length
  linarith

lemma heavyGraph_card_le {w : Sym2 V → ℝ} (hw : CycleUpperWeight G w) :
    (heavyGraph G w).edgeFinset.card ≤ Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V with
  | inl h =>
      have hcard := acyclic_card_edges_le (heavyGraph G w) (heavyGraph_acyclic hw)
      simpa using hcard
  | inr h =>
      have hcard := acyclic_card_edges_lt (heavyGraph G w) (heavyGraph_acyclic hw)
      omega

/-- In any edge-disjoint family, pieces meeting a fixed edge set inject into that set. -/
lemma card_meeting_edges_le (D : Finset G.Subgraph)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet))
    (F : SimpleGraph V) :
    (D.filter (fun H => ∃ e ∈ H.edgeSet, e ∈ F.edgeSet)).card ≤ F.edgeFinset.card := by
  let A := D.filter (fun H => ∃ e ∈ H.edgeSet, e ∈ F.edgeSet)
  have hex : ∀ H : A, ∃ e, e ∈ H.val.edgeSet ∧ e ∈ F.edgeSet := by
    intro H
    exact (Finset.mem_filter.mp H.property).2
  choose e he hf using hex
  let f : A → F.edgeSet := fun H => ⟨e H,hf H⟩
  have hinj : Function.Injective f := by
    intro H K h
    apply Subtype.ext
    by_contra hne
    have hdis := hd (Finset.mem_filter.mp H.property).1
      (Finset.mem_filter.mp K.property).1 hne
    have heq : e H = e K := congrArg Subtype.val h
    exact Set.disjoint_left.mp hdis (he H) (heq ▸ he K)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe,SimpleGraph.edgeFinset_card] using hc

/-- A cycle-only signed dual is linearly bounded on an even graph.
No per-edge upper bound and no integral optimality hypothesis are assumed. -/
lemma total_le_two_card_sub_one {w : Sym2 V → ℝ} (hw : CycleUpperWeight G w)
    (heven : ∀ v, Even (G.degree v)) :
    (∑ e ∈ G.edgeFinset, w e) ≤ 2 * (Fintype.card V - 1 : ℕ) := by
  obtain ⟨D,hD,hdec,hc⟩ := minimum_cycles heven
  let F := heavyGraph G w
  let A := D.filter (fun H => ∃ e ∈ H.edgeSet, e ∈ F.edgeSet)
  have hAD : A ⊆ D := Finset.filter_subset _ _
  have hcount : A.card ≤ Fintype.card V - 1 :=
    (card_meeting_edges_le D hdec.1 F).trans (heavyGraph_card_le hw)
  have hweightA : (∑ H ∈ A, ∑ e ∈ H.spanningCoe.edgeFinset, w e) ≤ (A.card : ℝ) := by
    calc
      _ ≤ ∑ _H ∈ A, (1 : ℝ) :=
        Finset.sum_le_sum (fun H hH => piece_weight_le hw H (hD H (hAD hH)))
      _ = _ := by simp
  let R := subfamilyGraph (D \ A)
  have hRG : R ≤ G := subfamilyGraph_le _
  have hedge : ∀ e ∈ R.edgeSet, w e ≤ 1 := by
    intro e he
    have hset := subfamilyGraph_edges (D \ A)
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp (hset ▸ he)
    obtain ⟨hHD,hHA⟩ := Finset.mem_sdiff.mp hH
    by_contra hn
    have heF : e ∈ F.edgeSet := by
      induction e using Sym2.ind with | _ x y =>
        exact ⟨H.adj_sub heH,lt_of_not_ge hn⟩
    exact hHA (Finset.mem_filter.mpr ⟨hHD,e,heH,heF⟩)
  have hweightR := signed_total_weight_le R w 1 (by norm_num) hedge (hw.mono hRG)
  have hdis : Set.PairwiseDisjoint ((D \ A : Finset G.Subgraph) : Set G.Subgraph)
      (fun H => H.edgeSet) := by
    intro H hH K hK hne
    exact hdec.1 (Finset.mem_sdiff.mp hH).1 (Finset.mem_sdiff.mp hK).1 hne
  have hsumR := subfamily_weight (D \ A) hdis w
  change (∑ e ∈ R.edgeFinset, w e) = _ at hsumR
  have hsplit := Finset.sum_sdiff (f := fun H => ∑ e ∈ H.spanningCoe.edgeFinset, w e) hAD
  have hsumG := decomposition_weight_eq D hdec w
  have hcountR : (A.card : ℝ) ≤ (Fintype.card V - 1 : ℕ) := by exact_mod_cast hcount
  simp only [one_mul] at hweightR
  linarith

#print axioms heavyGraph_acyclic
#print axioms total_le_two_card_sub_one
end Erdos184Work.CycleDualBound
