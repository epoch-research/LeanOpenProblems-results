import FormalConjecturesUtil
import Submission.CycleNeighborhoodOverlap
import Submission.C8SplitPaths
import Submission.SaturationLinearWindow

/-! On the same exact near-order C8-free hosts, all but o(e(G)) ordered
host edges admit robust C9 witnesses and edge-disjoint split packings.
This is a necessary condition, not a rationality theorem. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713JointC8EdgeWitnesses
open Erdos713CycleNeighborhoodOverlap Erdos713C8SplitPaths
open Erdos713RobustContractionWitnesses Erdos713SplitEdgePacking
open Erdos713SaturationLinearWindow Erdos713Cloning
set_option maxHeartbeats 2000000

lemma cycle_eight_bipartite : (cycleGraph 8).IsBipartite := by
  refine ⟨Coloring.mk (fun z => (⟨z.val % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
  intro u v
  simp only [cycleGraph_adj]
  fin_cases u <;> fin_cases v <;> decide

lemma codegree_of_good_edge {V : Type*} [Fintype V] (G : SimpleGraph V) {t : ℝ}
    {u v : V} (ha : G.Adj u v) (hp : (u,v) ∉ badEdges G t) :
    (Nat.card (G.commonNeighbors u v) : ℝ) ≤ t := by
  by_contra hh
  exact hp (mem_filter.mpr ⟨mem_univ _,ha,lt_of_not_ge hh⟩)

/-- The exception is relative to the number of EDGES, not to n^2.
The same host retains the growing-window backward gaps and full folds. -/
theorem nearby_edge_witnesses {α c a : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a) (hac : 2*a < c*α)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∀ N D : ℕ, ∀ᶠ k : ℕ in atTop, ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧
        (1-δ)*(k : ℝ) < Fintype.card U ∧ (Fintype.card U : ℝ) < (1+δ)*k ∧
        (cycleGraph 8).Free J ∧ Nat.card J.edgeSet = extremalNumber (Fintype.card U) (cycleGraph 8) ∧
        (∀ v, D ≤ Nat.card (J.neighborSet v)) ∧
        (∀ v, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet v) : ℝ)) ∧
        (∀ v, SingleFold (cycleGraph 8) J v) ∧
        (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ θ*Fintype.card U →
          a*(r : ℝ)*(Fintype.card U : ℝ)^(α-1) <
            (extremalNumber (Fintype.card U) (cycleGraph 8) : ℝ)-
              (extremalNumber (Fintype.card U-r) (cycleGraph 8) : ℝ)) ∧
        ∃ B : Finset (U × U), (B.card : ℝ) ≤ ε*(Nat.card J.edgeSet : ℝ) ∧
          (∀ p ∈ B, J.Adj p.1 p.2) ∧
          ∀ u v, J.Adj u v → (u,v) ∉ B →
            RobustEdgeRoots (cycleGraph 8) J u v (a*(Fintype.card U : ℝ)^(α-1)) ∧
            EdgePacking (cycleGraph 8) J u v ⌊a*(Fintype.card U : ℝ)^(α-1)/36⌋₊ ∧
            ∀ T : Finset (Sym2 U), (T.card : ℝ) ≤ a*(Fintype.card U : ℝ)^(α-1) →
              ∃ p : J.Walk u u, p.IsCycle ∧ p.length = 9 ∧ s(u,v) ∈ p.edges ∧
                ∀ e ∈ p.edges, e ≠ s(u,v) → e ∉ T := by
  let b : ℝ := (2*a+c*α)/2
  have hb2a : 2*a < b := by dsimp [b]; linarith
  have hbc : b < c*α := by dsimp [b]; linarith
  have hab : a < b := by linarith
  have hb0 : 0 < b := ha0.trans hab
  have hp : 0 < α-1 := by linarith
  have hEdge : ∃ x y, (cycleGraph 8).Adj x y := ⟨0,1,by simp [cycleGraph_adj]⟩
  obtain ⟨θ,hθ0,hθ1,hSel⟩ := nearby_linear_saturated (cycleGraph 8)
    cycle_eight_bipartite hEdge ha ha2 hc hb0 hbc h
  refine ⟨θ,hθ0,hθ1,?_⟩
  intro δ ε hd hε N D
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (b-2*a)*(n : ℝ)^(α-1) :=
    (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (sub_pos.mpr hb2a)).eventually_ge_atTop _
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (hlarge.and (eventually_few_badEdges ha0 hp hε))
  filter_upwards [hSel (max N M) D δ hd] with k hk
  obtain ⟨U,hU,J,hnNM,hnlo,hnhi,hf,he,hD,hMin,hFold,hBack,hMulti⟩ := hk
  obtain ⟨hLarge,hBad⟩ := hM (Fintype.card U) ((le_max_right N M).trans hnNM)
  have hpow : 0 ≤ (Fintype.card U : ℝ)^(α-1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hab' : a*(Fintype.card U : ℝ)^(α-1) ≤ b*(Fintype.card U : ℝ)^(α-1) :=
    mul_le_mul_of_nonneg_right hab.le hpow
  have hGap : a*(Fintype.card U : ℝ)^(α-1)+a*(Fintype.card U : ℝ)^(α-1)+1 <
      (extremalNumber (Fintype.card U) (cycleGraph 8) : ℝ)-
        (extremalNumber (Fintype.card U-1) (cycleGraph 8) : ℝ) := by
    nlinarith only [hLarge,hBack]
  refine ⟨U,hU,J,(le_max_left N M).trans hnNM,hnlo,hnhi,hf,he,hD,
    fun v => hab'.trans (hMin v),hFold,?_,
    badEdges J (a*(Fintype.card U : ℝ)^(α-1)),hBad U J hf,?_,?_⟩
  · intro r hr1 hrθ
    have hm := mul_le_mul_of_nonneg_left hab' (Nat.cast_nonneg (α := ℝ) r)
    have hh := hMulti r hr1 hrθ
    nlinarith only [hm,hh]
  · intro p hp
    exact (mem_filter.mp hp).2.1
  · intro u v huv hgood
    have hCom := codegree_of_good_edge J huv hgood
    have hRobust := robust_of_backward_gap (cycleGraph 8) J hf he huv.ne hGap hCom
    refine ⟨hRobust,?_,?_⟩
    · apply packing_of_robust (cycleGraph 8) J u v hRobust
      have hflo := Nat.floor_le (show 0 ≤ a*(Fintype.card U : ℝ)^(α-1)/36 by positivity)
      norm_num only [Fintype.card_fin,Nat.reduceAdd,Nat.choose] at ⊢
      push_cast
      nlinarith only [hflo]
    · intro T hT
      exact nine_cycle_after_deleting hf he huv T (by linarith)

#print axioms nearby_edge_witnesses
end Erdos713JointC8EdgeWitnesses
