import Submission.RankCritical

/-!
Closed spanning subgraphs retain every original edge inside each of their
components. Rank-criticality forces any proper such subgraph to omit more
than 2C edges. This is a necessary cut condition, not a linear bound proof.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankCriticalCuts
open RankCritical
variable {V : Type*} [Fintype V]

/-- No original edge joins vertices connected in R without belonging to R. -/
def IsComponentClosed (G R : SimpleGraph V) : Prop :=
  ∀ u v, G.Adj u v → R.Reachable u v → R.Adj u v

lemma cycle_omits_zero_or_two (G R : SimpleGraph V) (hclosed : IsComponentClosed G R)
    (H : G.Subgraph) (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (hne : (H.edgeSet \ R.edgeSet).Nonempty) : 2 ≤ (H.edgeSet \ R.edgeSet).ncard := by
  by_contra hn
  have hs : (H.edgeSet \ R.edgeSet).Subsingleton :=
    Set.ncard_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨e,heH,heR⟩ := hne
  induction e using Sym2.ind with
  | h u v =>
    have huv : H.Adj u v := heH
    obtain ⟨p,hp,hpH⟩ := CycleRing.cycle_piece_walk_at H hc hr u (H.edge_vert huv)
    have hcy : H.spanningCoe.IsCycles := by
      rw [← hpH]
      exact hp.isCycles_spanningCoe_toSubgraph
    have hle : H.spanningCoe.deleteEdges {s(u,v)} ≤ R := by
      intro a b hab
      by_contra hnab
      have hab' := SimpleGraph.deleteEdges_adj.mp hab
      have heq : s(a,b) = s(u,v) := hs ⟨hab'.1,hnab⟩ ⟨heH,heR⟩
      exact hab'.2 (Set.mem_singleton_iff.mpr heq)
    exact heR (hclosed u v (H.adj_sub huv) ((hcy.reachable_deleteEdges huv).mono hle))

noncomputable def crossingPieces {G : SimpleGraph V} (D : Finset G.Subgraph)
    (R : SimpleGraph V) : Finset G.Subgraph := D.filter (fun H => (H.edgeSet \ R.edgeSet).Nonempty)

lemma crossingPieces_budget (G R : SimpleGraph V) (hclosed : IsComponentClosed G R)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    2 * (crossingPieces D R).card ≤ (G.edgeSet \ R.edgeSet).ncard := by
  let P := crossingPieces D R
  let F := fun H : G.Subgraph => (H.edgeSet \ R.edgeSet).toFinset
  have hdis : (P : Set G.Subgraph).PairwiseDisjoint F := by
    intro H hH K hK hne
    apply Finset.disjoint_left.mpr
    intro e heH heK
    exact Set.disjoint_left.mp
      (hd.1 ((Finset.mem_filter.mp hH).1) ((Finset.mem_filter.mp hK).1) hne)
      (Set.mem_toFinset.mp heH).1 (Set.mem_toFinset.mp heK).1
  have hcov : P.biUnion F = (G.edgeSet \ R.edgeSet).toFinset := by
    ext e
    simp only [Finset.mem_biUnion,F,Set.mem_toFinset]
    constructor
    · rintro ⟨H,hH,heH,heR⟩
      exact ⟨H.edgeSet_subset heH,heR⟩
    · rintro ⟨heG,heR⟩
      rw [← hd.2] at heG
      obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heG
      exact ⟨H,Finset.mem_filter.mpr ⟨hH,⟨e,heH,heR⟩⟩,heH,heR⟩
  have hsum : 2 * P.card ≤ ∑ H ∈ P, (F H).card := by
    calc
      2 * P.card = ∑ _H ∈ P, 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro H hH
        have hHD := (Finset.mem_filter.mp hH).1
        have hh := cycle_omits_zero_or_two G R hclosed H (hc H hHD).1 (hc H hHD).2
          (Finset.mem_filter.mp hH).2
        simpa only [F,← Set.ncard_eq_toFinset_card'] using hh
  rw [← Finset.card_biUnion hdis,hcov,← Set.ncard_eq_toFinset_card'] at hsum
  exact hsum

omit [Fintype V] in
lemma crossingPieces_residual_le (G R : SimpleGraph V) (D : Finset G.Subgraph)
    (hd : IsDecomposition G D) : G \ unionPieces G (crossingPieces D R) ≤ R := by
  intro u v huv
  by_contra hn
  have heG : s(u,v) ∈ G.edgeSet := huv.1
  rw [← hd.2] at heG
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp heG
  apply huv.2
  change s(u,v) ∈ (unionPieces G (crossingPieces D R)).edgeSet
  rw [unionPieces_edgeSet]
  exact Set.mem_iUnion₂.mpr ⟨H,Finset.mem_filter.mpr ⟨hH,⟨s(u,v),heH,hn⟩⟩,heH⟩

lemma closed_cut_lower {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (R : SimpleGraph V) (hRG : R ≤ G) (hclosed : IsComponentClosed G R) (hne : R ≠ G) :
    2 * C < (G.edgeSet \ R.edgeSet).ncard := by
  by_contra! hb
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  have hbudget := crossingPieces_budget G R hclosed D hc hd
  have hp : (crossingPieces D R).card ≤ C := by omega
  have hre := hG.small_packing_reachable (crossingPieces D R)
    (fun H hH => hc H ((Finset.mem_filter.mp hH).1))
    (fun H hH K hK hne => hd.1 ((Finset.mem_filter.mp hH).1)
      ((Finset.mem_filter.mp hK).1) hne) hp
  have hres := crossingPieces_residual_le G R D hd
  apply hne
  apply le_antisymm hRG
  intro u v huv
  exact hclosed u v huv (((hre u v).mpr huv.reachable).mono hres)

/-- A partition-sensitive strengthening: omitted edges must pay for twice
the number of extra components. This still does not exclude a critical graph. -/
lemma closed_partition_budget {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (R : SimpleGraph V) (hRG : R ≤ G) (hne : R ≠ G)
    (hclosed : IsComponentClosed G R) :
    2 * C * graphRank G < (G.edgeSet \ R.edgeSet).ncard + 2 * C * graphRank R := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  let P := crossingPieces D R
  have hres : G \ unionPieces G P ≤ R := crossingPieces_residual_le G R D hd
  have hneP : P.Nonempty := by
    by_contra hp
    have hP := Finset.not_nonempty_iff_eq_empty.mp hp
    apply hne
    apply le_antisymm hRG
    simpa [hP,unionPieces] using hres
  have hcost := hG.packing_cost P hneP
    (fun H hH => hc H (Finset.mem_filter.mp hH).1)
    (fun H hH K hK hne => hd.1 (Finset.mem_filter.mp hH).1
      (Finset.mem_filter.mp hK).1 hne)
  have hbudget := crossingPieces_budget G R hclosed D hc hd
  have hr := Nat.mul_le_mul_left C (rank_mono hres)
  simp only [Nat.mul_assoc]
  change 2 * P.card ≤ _ at hbudget
  omega

/-- Add back exactly the original edges within components of R. -/
def componentClosure (G R : SimpleGraph V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ R.Reachable u v
  symm := by intro u v h; exact ⟨h.1.symm,h.2.symm⟩
  loopless := by intro u h; exact h.1.ne rfl

omit [Fintype V] in
lemma closure_le (G R : SimpleGraph V) : componentClosure G R ≤ G := fun _ _ h => h.1

omit [Fintype V] in
lemma le_closure {G R : SimpleGraph V} (h : R ≤ G) : R ≤ componentClosure G R :=
  fun _ _ hab => ⟨h hab,hab.reachable⟩

omit [Fintype V] in
lemma closure_reachable (G R : SimpleGraph V) {u v : V}
    (h : (componentClosure G R).Reachable u v) : R.Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons h p ih => exact h.2.trans ih

omit [Fintype V] in
lemma closure_closed (G R : SimpleGraph V) : IsComponentClosed G (componentClosure G R) := by
  intro u v huv hr
  exact ⟨huv,closure_reachable G R hr⟩

lemma small_edge_deletion_reachable {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (F : Set (Sym2 V)) (hF : F.ncard ≤ 2 * C) (u v : V) (huv : G.Reachable u v) :
    (G.deleteEdges F).Reachable u v := by
  let R := G.deleteEdges F
  let A := componentClosure G R
  have hA : A = G := by
    by_contra hn
    have hh := closed_cut_lower hG A (closure_le G R) (closure_closed G R) hn
    have hs : G.edgeSet \ A.edgeSet ⊆ F := by
      intro e he
      by_contra hnot
      have heR : e ∈ R.edgeSet := by
        rw [show R.edgeSet = G.edgeSet \ F from G.edgeSet_deleteEdges F]
        exact ⟨he.1,hnot⟩
      exact he.2 (SimpleGraph.edgeSet_mono (le_closure (G.deleteEdges_le F)) heR)
    have hc := Set.ncard_le_ncard hs
    omega
  apply closure_reachable G R
  change A.Reachable u v
  rwa [hA]

lemma edge_reachable_lower {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (u v : V) (huv : G.Reachable u v) : G.IsEdgeReachable (2*C+1) u v := by
  intro F hF
  apply small_edge_deletion_reachable hG F ?_ u v huv
  have hh : F.ncard < 2*C+1 := by
    rw [Set.encard_eq_coe_toFinset_card,← Set.ncard_eq_toFinset_card'] at hF
    exact_mod_cast hF
  omega

end RankCriticalCuts
end Erdos184
