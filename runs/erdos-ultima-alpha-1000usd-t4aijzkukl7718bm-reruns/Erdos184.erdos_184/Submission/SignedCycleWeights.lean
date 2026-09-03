import Submission.WeightedGraphs
import Submission.ForestSeparatorGluing
import Submission.ShiftedPackingConnectivity

/-! Signed cycle-weight inequalities in even graphs imply a linear total-weight bound.
This is a fractional-dual estimate, not an integral cycle partition theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.WeightedPaths
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

lemma walk_weight_eq_edge_sum {G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    walkWeight w p = ∑ e ∈ p.toSubgraph.edgeSet.toFinset, w e := by
  have hf : p.toSubgraph.edgeSet.toFinset = p.edges.toFinset := by
    ext e
    simp only [Set.mem_toFinset,List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [hf,List.sum_toFinset w hp.edges_nodup]
  rfl

lemma cycle_piece_weight_le {G : SimpleGraph V} (w : Sym2 V → ℝ)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1)
    (H : G.Subgraph) (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∑ e ∈ H.edgeSet.toFinset, w e) ≤ 1 := by
  obtain ⟨u⟩ := hH.1.nonempty
  obtain ⟨p,hp,hpeq⟩ := CycleRing.cycle_piece_walk_at H hH.1 hH.2 u.val u.property
  rw [← hpeq]
  simpa only [walk_weight_eq_edge_sum w p hp.isTrail] using hc _ p hp

lemma sum_unionPieces (G : SimpleGraph V) (w : Sym2 V → ℝ) (D : Finset G.Subgraph)
    (hd : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet)) :
    (∑ e ∈ (unionPieces G D).edgeFinset, w e) = ∑ H ∈ D, ∑ e ∈ H.edgeSet.toFinset, w e := by
  have hdis : Set.PairwiseDisjoint (D : Set G.Subgraph) (fun H => H.edgeSet.toFinset) := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp (hd hH hK hne)
      (Set.mem_toFinset.mp heH) (Set.mem_toFinset.mp heK)
  have hu : D.biUnion (fun H => H.edgeSet.toFinset) = (unionPieces G D).edgeFinset := by
    ext e
    simpa using (Set.ext_iff.mp (unionPieces_edgeSet G D) e).symm
  rw [← hu,Finset.sum_biUnion hdis]

lemma sum_edges_sdiff {G A : SimpleGraph V} (w : Sym2 V → ℝ) (hA : A ≤ G) :
    (∑ e ∈ (G \ A).edgeFinset, w e) + (∑ e ∈ A.edgeFinset, w e) =
      ∑ e ∈ G.edgeFinset, w e := by
  rw [edgeFinset_sdiff]
  exact Finset.sum_sdiff (SimpleGraph.edgeFinset_mono hA)

omit [Fintype V] in
lemma cycle_weight_bound_mono {G A : SimpleGraph V} (w : Sym2 V → ℝ) (hA : A ≤ G)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    ∀ u (p : A.Walk u u), p.IsCycle → walkWeight w p ≤ 1 := by
  intro u p hp
  let f : A →g G := SimpleGraph.Hom.ofLE hA
  have hh := hc _ (p.map f) (hp.map Function.injective_id)
  simpa [weight_map,f] using hh

lemma nonnegative_even_sum_le_card (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hG : ∀ x, Even (G.degree x)) (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ Fintype.card V := by
  apply sum_edges_le_card G w hn _ hc
  obtain ⟨D,hD,hd⟩ := even_cycle_decomposition G hG
  intro e he
  rw [← hd.2] at he
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
  have hh := Finset.single_le_sum (s := H.edgeSet.toFinset) (f := w)
    (fun f hf => hn f (H.edgeSet_subset (Set.mem_toFinset.mp hf))) (Set.mem_toFinset.mpr heH)
  exact hh.trans (cycle_piece_weight_le w hc H (hD H hH))

/-- Negative cycle inequalities are needed only on an even subgraph of the
negative-edge graph; the negative edges left over form a forest. -/
lemma signed_even_sum_le_twice_card (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hG : ∀ x, Even (G.degree x))
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ 2 * Fintype.card V := by
  let N : SimpleGraph V := {
    Adj := fun a b => G.Adj a b ∧ w s(a,b) < 0
    symm := fun a b h => ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
    loopless := fun a h => G.loopless a h.1 }
  have hNG : N ≤ G := fun _ _ h => h.1
  have hN (e : Sym2 V) : e ∈ N.edgeSet ↔ e ∈ G.edgeSet ∧ w e < 0 := by
    induction e using Sym2.inductionOn with | _ a b => rfl
  obtain ⟨E,hEN,hE,hforest⟩ := ForestBoundaryBudget.even_part_with_forest_remainder N
  have hEG := hEN.trans hNG
  let R := G \ E
  have hRG : R ≤ G := sdiff_le
  have hR : ∀ x, Even (R.degree x) := even_sdiff_of_even hEG hG hE
  have hweightE : (∑ e ∈ E.edgeFinset, w e) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e he
    exact ((hN e).mp (SimpleGraph.edgeSet_mono hEN (SimpleGraph.mem_edgeFinset.mp he))).2.le
  let F := (N \ E).edgeSet
  have hFcard : F.ncard ≤ Fintype.card V := by
    cases isEmpty_or_nonempty V with
    | inl hV =>
      haveI := hV
      have hFe : F = ∅ := by
        ext e
        induction e using Sym2.inductionOn with | _ a b => exact isEmptyElim a
      simp [hFe]
    | inr hV =>
      haveI := hV
      have hh := forest_edge_card_lt_vertex_card (N \ E) hforest
      simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
        using hh.le
  obtain ⟨D,hD,hd⟩ := even_cycle_decomposition R (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hR x)
  obtain ⟨P,hPD,hPF,hres⟩ := ShiftedCritical.exists_packing_cover_edges (G := R) D hd F
  have hP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hD H (hPD hH)
  have hdis : Set.PairwiseDisjoint (P : Set R.Subgraph) (fun H => H.edgeSet) :=
    fun _ hH _ hK hHK => hd.1 (hPD hH) (hPD hK) hHK
  let U := unionPieces R P
  have hUR : U ≤ R := unionPieces_le R P
  have hweightU : (∑ e ∈ U.edgeFinset, w e) ≤ Fintype.card V := by
    calc
      _ = ∑ H ∈ P, ∑ e ∈ H.edgeSet.toFinset, w e := sum_unionPieces R w P hdis
      _ ≤ ∑ _H ∈ P, (1 : ℝ) := Finset.sum_le_sum (fun H hH =>
        cycle_piece_weight_le w (cycle_weight_bound_mono w hRG hc) H (by
          simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
            using hP H hH))
      _ = P.card := by simp
      _ ≤ Fintype.card V := by exact_mod_cast hPF.trans hFcard
  let A := R \ U
  have hAG : A ≤ G := (show A ≤ R from sdiff_le).trans hRG
  have hA : ∀ x, Even (A.degree x) := by
    intro x
    have hh := even_residual_of_cycle_packing R (by
      intro y
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hR y) P (by
        intro H hH
        simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
          using hP H hH) hdis x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh
  have hnonneg : ∀ e ∈ A.edgeSet, 0 ≤ w e := by
    intro e he
    by_contra! hn
    have hdel := SimpleGraph.edgeSet_mono hres he
    have hRmem := SimpleGraph.edgeSet_mono (show A ≤ R from sdiff_le) he
    change e ∈ (G \ E).edgeSet at hRmem
    rw [SimpleGraph.edgeSet_sdiff] at hRmem
    rw [SimpleGraph.edgeSet_deleteEdges] at hdel
    have hnot : e ∉ E.edgeSet := hRmem.2
    have hFmem : e ∈ F := by
      change e ∈ (N \ E).edgeSet
      rw [SimpleGraph.edgeSet_sdiff]
      exact ⟨(hN e).mpr ⟨hRmem.1,hn⟩,hnot⟩
    exact hdel.2 hFmem
  have hweightA := nonnegative_even_sum_le_card A w (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hA x) hnonneg (cycle_weight_bound_mono w hAG hc)
  have hsR : (∑ e ∈ A.edgeFinset, w e) + (∑ e ∈ U.edgeFinset, w e) =
      ∑ e ∈ R.edgeFinset, w e := by
    convert sum_edges_sdiff w hUR using 1 <;>
      simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset]
  have hsG : (∑ e ∈ R.edgeFinset, w e) + (∑ e ∈ E.edgeFinset, w e) =
      ∑ e ∈ G.edgeFinset, w e := by
    convert sum_edges_sdiff w hEG using 1
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hweightA hweightU hweightE hsR hsG ⊢
  linarith

end Erdos184.WeightedPaths
