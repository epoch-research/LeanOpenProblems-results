import Submission.UnitWeightsPrivatePaths

/-!
A quantitative consequence of the K4 cycle relation. In an even graph where
every cycle extends to a minimum partition, any private-path K4 model forces
an additive integral/fractional gap of at least 1/4. This does not bound the
integral count from above and does not settle Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.UnitCycleWeights
open WeightedPaths FractionalCycles FractionalDualCertificate
open FractionalEnvelope CycleNumberSubmodularity
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Every individually optimally extendable cycle has dual slack bounded by
the global integral-minus-dual gap. The same certificate works for all cycles. -/
lemma cycle_slack_bound
    (ho : MinimalCounterexample.AllCyclesOptimal G)
    {w : Sym2 V → ℝ} (hw : Feasible G w) (H : CyclePiece G) :
    1 - pieceWeight w H ≤ (cycleNumber G : ℝ) - weight w G := by
  obtain ⟨D,hc,hd,hHD,hmin⟩ := ho H.val H.property
  have hcard : cycleNumber G = D.card :=
    cycleNumber_eq G D.card ⟨D,hc,hd,le_rfl⟩ hmin
  have hu : unionPieces G D = G := by
    apply edgeSet_injective
    rw [unionPieces_edgeSet]
    exact hd.2
  have hs := sum_unionPieces G w D hd.1
  rw [hu] at hs
  have hn : ∀ J ∈ D, 0 ≤ 1 - ∑ e ∈ J.edgeSet.toFinset, w e := by
    intro J hJ
    exact sub_nonneg.mpr (hw ⟨J,hc J hJ⟩)
  have hh := Finset.single_le_sum hn hHD
  rw [Finset.sum_sub_distrib] at hh
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← hs] at hh
  simpa only [pieceWeight,hcard,weight] using hh

lemma walk_slack_bound
    (ho : MinimalCounterexample.AllCyclesOptimal G)
    {w : Sym2 V → ℝ} (hw : Feasible G w)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) :
    1 - walkWeight w p ≤ (cycleNumber G : ℝ) - weight w G := by
  have hh := cycle_slack_bound ho hw ⟨p.toSubgraph,cycle_subgraph_regular G hp⟩
  simpa only [pieceWeight,← walk_weight_eq_edge_sum w p hp.isTrail] using hh

lemma feasible_walk_bound {w : Sym2 V → ℝ} (hw : Feasible G w)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : walkWeight w p ≤ 1 := by
  have hh := hw ⟨p.toSubgraph,cycle_subgraph_regular G hp⟩
  simpa only [pieceWeight,← walk_weight_eq_edge_sum w p hp.isTrail] using hh

namespace K4

lemma triangle_quadrilateral_relation (w : Sym2 (Fin 4) → ℝ) :
    walkWeight w c0 + walkWeight w c1 + walkWeight w c2 + walkWeight w c3 =
      walkWeight w c4 + walkWeight w c5 + walkWeight w c6 := by
  simp only [c0,c1,c2,c3,c4,c5,c6,weight_cons,weight_nil,add_zero]
  have h20 : s((2 : Fin 4),0) = s(0,2) := Sym2.eq_swap
  have h30 : s((3 : Fin 4),0) = s(0,3) := Sym2.eq_swap
  have h31 : s((3 : Fin 4),1) = s(1,3) := Sym2.eq_swap
  have h32 : s((3 : Fin 4),2) = s(2,3) := Sym2.eq_swap
  have h21 : s((2 : Fin 4),1) = s(1,2) := Sym2.eq_swap
  rw [h20,h30,h31,h32,h21]
  ring

lemma slack_gap (w : Sym2 (Fin 4) → ℝ) (δ : ℝ)
    (hlo : ∀ v (p : complete.Walk v v), p.IsCycle → 1 - walkWeight w p ≤ δ)
    (hhi : ∀ v (p : complete.Walk v v), p.IsCycle → walkWeight w p ≤ 1) :
    1 ≤ 4*δ := by
  have h0 := hlo _ c0 c0_cycle
  have h1 := hlo _ c1 c1_cycle
  have h2 := hlo _ c2 c2_cycle
  have h3 := hlo _ c3 c3_cycle
  have h4 := hhi _ c4 c4_cycle
  have h5 := hhi _ c5 c5_cycle
  have h6 := hhi _ c6 c6_cycle
  have hr := triangle_quadrilateral_relation w
  linarith

end K4

/-- A K4 subdivision quantitatively obstructs fractional exactness under
individual optimal extendability. It does not obstruct a linear count bound. -/
theorem all_optimal_K4_gap
    (he : ∀ v, Even (G.degree v))
    (ho : MinimalCounterexample.AllCyclesOptimal G)
    (M : PrivatePathLifting.Model K4.complete G) :
    optimum G + 1/4 ≤ (cycleNumber G : ℝ) := by
  obtain ⟨w,hw,hval⟩ := FractionalDualCertificate.attained G he
  have hh := K4.slack_gap (replacementWeight M w)
    ((cycleNumber G : ℝ) - weight w G) (by
      intro v p hp
      rw [← lift_weight M w p]
      exact walk_slack_bound ho hw (M.lift p) (M.lift_isCycle p hp)) (by
      intro v p hp
      rw [← lift_weight M w p]
      exact feasible_walk_bound hw (M.lift p) (M.lift_isCycle p hp))
  rw [hval] at hh
  linarith

lemma critical_K4_gap {k : ℕ} (hG : CountCritical.IsCountCritical k G)
    (M : PrivatePathLifting.Model K4.complete G) : optimum G + 1/4 ≤ (k : ℝ) := by
  have hh := all_optimal_K4_gap hG.1 hG.allCyclesOptimal M
  rwa [hG.2.1] at hh

end Erdos184.UnitCycleWeights
