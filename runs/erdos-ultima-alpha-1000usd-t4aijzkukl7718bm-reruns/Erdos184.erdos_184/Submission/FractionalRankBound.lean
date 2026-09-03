import Submission.BlockRankPotential
import Submission.FractionalDualCertificate

/-!
Rank-sensitive weighted and fractional cycle bounds. These bounds concern
fractional exact partitions, not integral cycle decompositions.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalRankBound
open WeightedPaths RankCritical BlockRankPotential
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma exists_supported_star_sum_le_one (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hG : G ≠ ⊥) (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ 1)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    ∃ u ∈ G.support, (∑ x, star G w u x) ≤ 1 := by
  have hsup : G.support.Nonempty := by
    by_contra hs
    apply hG
    apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
    intro u v huv
    exact hs ⟨u, v, huv⟩
  letI : Nonempty G.support := hsup.to_subtype
  let A := G.induce G.support
  let w' : Sym2 G.support → ℝ := w ∘ Sym2.map Subtype.val
  let f : A →g G := (SimpleGraph.Embedding.induce G.support).toHom
  have hedge (e : Sym2 G.support) (he : e ∈ A.edgeSet) :
      Sym2.map Subtype.val e ∈ G.edgeSet := by
    induction e using Sym2.inductionOn with | _ a b => exact he
  have hcA : ∀ x (p : A.Walk x x), p.IsCycle → walkWeight w' p ≤ 1 := by
    intro x p hp
    have hh := hc x.val (p.map f) (hp.map Subtype.val_injective)
    simpa only [weight_map] using hh
  obtain ⟨u, hu⟩ := exists_star_sum_le_one A w'
    (fun e he => hn _ (hedge e he)) (fun e he' => he _ (hedge e he')) hcA
  have hz : (∑ x : {x // x ∉ G.support}, star G w u.val x.val) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hnot : ¬G.Adj u.val x.val := fun h => x.property ⟨u.val, h.symm⟩
    simp only [WeightedPaths.star, if_neg hnot]
  have hs := Fintype.sum_subtype_add_sum_subtype (· ∈ G.support) (star G w u.val)
  rw [hz, add_zero] at hs
  refine ⟨u.val, u.property, ?_⟩
  rw [← hs]
  simpa only [WeightedPaths.star, A, w', Function.comp_apply, Sym2.map_mk, induce_adj] using hu

lemma sum_edges_delete_incidence (G : SimpleGraph V) (w : Sym2 V → ℝ) (u : V) :
    (∑ e ∈ (G.deleteIncidenceSet u).edgeFinset, w e) +
      (∑ x, star G w u x) = ∑ e ∈ G.edgeFinset, w e := by
  rw [star_sum_eq_incidence]
  have hf : (G.deleteIncidenceSet u).edgeFinset = G.edgeFinset \ G.incidenceFinset u := by
    ext e
    simp only [mem_edgeFinset, edgeSet_deleteIncidenceSet, Set.mem_diff,
      Finset.mem_sdiff, mem_incidenceFinset]
  rw [hf]
  exact Finset.sum_sdiff (G.incidenceFinset_subset u)

/-- The nonnegative weighted cycle and edge inequalities cost at most forest rank. -/
lemma nonnegative_sum_le_rank (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (he : ∀ e ∈ G.edgeSet, w e ≤ 1)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ graphRank G := by
  generalize hm : G.edgeFinset.card = m
  induction m using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hG : G = ⊥
    · have hz : G.edgeFinset = ∅ := by
        ext e
        simp only [mem_edgeFinset, hG, edgeSet_bot, Set.mem_empty_iff_false,
          Finset.notMem_empty]
      rw [hz, Finset.sum_empty]
      positivity
    obtain ⟨u, hu, hstar⟩ := exists_supported_star_sum_le_one G w hG hn he hc
    let A := G.deleteIncidenceSet u
    have hAG : A ≤ G := G.deleteIncidenceSet_le u
    have hd : 0 < G.degree u := (G.degree_pos_iff_mem_support u).mpr hu
    have hcard : A.edgeFinset.card < m := by
      have hh := G.card_edgeFinset_deleteIncidenceSet u
      have hle := G.degree_le_card_edgeFinset u
      dsimp only [A]
      omega
    have hb := ih _ hcard A (fun e he => hn _ (edgeSet_mono hAG he))
      (fun e he' => he _ (edgeSet_mono hAG he'))
      (cycle_weight_bound_mono w hAG hc) (by
        simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset])
    have hr : graphRank A + 1 ≤ graphRank G := by
      have hh := loss_pos_of_supported G u hu
      unfold vertexLoss at hh
      dsimp only [A]
      omega
    have hr' : (graphRank A : ℝ) + 1 ≤ graphRank G := by exact_mod_cast hr
    have hs := sum_edges_delete_incidence G w u
    change (∑ e ∈ A.edgeFinset, w e) + _ = _ at hs
    simp only [SimpleGraph.edgeFinset, ← Set.toFinite_toFinset] at hb hs ⊢
    linarith


lemma nonnegative_even_sum_le_rank (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hG : ∀ x, Even (G.degree x)) (hn : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ graphRank G := by
  apply nonnegative_sum_le_rank G w hn _ hc
  obtain ⟨D,hD,hd⟩ := even_cycle_decomposition G hG
  intro e he
  rw [← hd.2] at he
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
  have hh := Finset.single_le_sum (s := H.edgeSet.toFinset) (f := w)
    (fun f hf => hn f (H.edgeSet_subset (Set.mem_toFinset.mp hf))) (Set.mem_toFinset.mpr heH)
  exact hh.trans (cycle_piece_weight_le w hc H (hD H hH))


/-- Signed cycle inequalities cost at most twice spanning-forest rank. -/
lemma signed_even_sum_le_twice_rank (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hG : ∀ x, Even (G.degree x))
    (hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1) :
    (∑ e ∈ G.edgeFinset, w e) ≤ 2 * graphRank G := by
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
  have hFcard : F.ncard ≤ graphRank G := by
    have hf := forest_rank (N \ E) hforest
    have hm := rank_mono ((show N \ E ≤ N from sdiff_le).trans hNG)
    rw [hf] at hm
    simpa only [F, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using hm
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
  have hweightU : (∑ e ∈ U.edgeFinset, w e) ≤ graphRank G := by
    calc
      _ = ∑ H ∈ P, ∑ e ∈ H.edgeSet.toFinset, w e := sum_unionPieces R w P hdis
      _ ≤ ∑ _H ∈ P, (1 : ℝ) := Finset.sum_le_sum (fun H hH =>
        cycle_piece_weight_le w (cycle_weight_bound_mono w hRG hc) H (by
          simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
            using hP H hH))
      _ = P.card := by simp
      _ ≤ graphRank G := by exact_mod_cast hPF.trans hFcard
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
  have hweightA := nonnegative_even_sum_le_rank A w (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hA x) hnonneg (cycle_weight_bound_mono w hAG hc)
  have hsR : (∑ e ∈ A.edgeFinset, w e) + (∑ e ∈ U.edgeFinset, w e) =
      ∑ e ∈ R.edgeFinset, w e := by
    convert sum_edges_sdiff w hUR using 1 <;>
      simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset]
  have hsG : (∑ e ∈ R.edgeFinset, w e) + (∑ e ∈ E.edgeFinset, w e) =
      ∑ e ∈ G.edgeFinset, w e := by
    convert sum_edges_sdiff w hEG using 1
  have hrank : (graphRank A : ℝ) ≤ graphRank G := by
    exact_mod_cast rank_mono hAG
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hweightA hweightU hweightE hsR hsG ⊢
  linarith


/-- The attained fractional optimum has a component-sensitive linear bound. -/
lemma optimum_le_twice_rank (G : SimpleGraph V) (hG : ∀ v, Even (G.degree v)) :
    FractionalEnvelope.optimum G ≤ 2 * graphRank G := by
  obtain ⟨w, hw, hval⟩ := FractionalDualCertificate.attained G hG
  have hc : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ 1 := by
    intro u p hp
    let H : FractionalCycles.CyclePiece G := ⟨p.toSubgraph, cycle_subgraph_regular G hp⟩
    have hh := hw H
    rw [walk_weight_eq_edge_sum w p hp.isTrail]
    exact hh
  rw [← hval]
  exact signed_even_sum_le_twice_rank G w hG hc

/-- An actual nonnegative exact fractional partition, with the rank bound. -/
lemma exists_fractional_partition_rank (G : SimpleGraph V)
    (hG : ∀ v, Even (G.degree v)) :
    ∃ t : FractionalCycles.CyclePiece G → ℝ,
      FractionalCycles.IsFractionalPartition G t ∧
      (∑ H, t H) ≤ 2 * graphRank G := by
  obtain ⟨t, ht, hval⟩ := FractionalEnvelope.optimum_attained G hG
  exact ⟨t, ht, hval.le.trans (optimum_le_twice_rank G hG)⟩

/-- The same rank bound holds for the monotone fractional envelope. -/
lemma envelope_le_twice_rank (G : SimpleGraph V) :
    FractionalEnvelope.envelope G ≤ 2 * graphRank G := by
  apply FractionalEnvelope.envelope_le
  intro H hHG hH
  apply (optimum_le_twice_rank H hH).trans
  have hr : (graphRank H : ℝ) ≤ graphRank G := by exact_mod_cast rank_mono hHG
  linarith

end Erdos184.FractionalRankBound
