import FormalConjecturesUtil
import Submission.SharpPenaltyExpanders
import Submission.PenalizedContraction
import Submission.UniformEdgeCodegrees

/-! Robust edge contraction on the same sharp near-full penalized expanders.
This is a necessary condition for pure-power growth, not a rationality proof. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713SharpPenaltyEdgeExpanders
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713MergeDegreePenalty Erdos713SwitchGluing
open Erdos713UniformEdgePenalty Erdos713UniformEdgeCodegrees
open Erdos713CycleNeighborhoodOverlap Erdos713RobustContractionWitnesses
variable {W : Type*}
set_option maxHeartbeats 2000000

/-- Every constant preceding a, ε, ρ, σ is independent of all four accuracies.
The host is not changed after selection; no exact edge decrement is used. -/
theorem joint [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ κ ξ : ℝ, 0 < κ ∧ 0 < ξ ∧ ∀ a : ℝ, 0 < a → a < c*α →
      ∀ ε ρ σ : ℝ, 0 < ε → 0 < ρ → 0 < σ →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          ξ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
        ((safePairs H G).card : ℝ) ≤ ρ*(n : ℝ)^2 ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu ∧
          lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
          a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) ∧
          ∃ B : Finset (Fin n × Fin n), (B.card : ℝ) ≤ σ*edgesR G ∧
            (∀ p ∈ B, G.Adj p.1 p.2) ∧
            ∀ u v, G.Adj u v → (u,v) ∉ B →
              a*(n : ℝ)^(α-1)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
                2*lam*degreeR G u*degreeR G v < mu*(2*n-1) ∧
              RobustEdgeRoots H G u v (a*(n : ℝ)^(α-1)) := by
  obtain ⟨κ,ξ,hκ,hξ,hSelect⟩ := Erdos713SharpPenaltyExpanders.joint H hH hEdge ha ha2 hc h
  refine ⟨κ,ξ,hκ,hξ,?_⟩
  intro a ha0 hac ε ρ σ hε hρ hσ
  let b := (a+c*α)/2
  have hab : a < b := by dsimp [b]; linarith
  have hb : 0 < b := ha0.trans hab
  have hbc : b < c*α := by dsimp [b]; linarith
  let t := (b-a)/4
  have ht : 0 < t := by dsimp [t]; linarith
  obtain ⟨ηE,hηE,hPenalty⟩ := eventually_few_penalty_edges H ha hc ht
    (show 0 < σ*c/4 by positivity) h
  let η := min ε (min (c/2) (ηE/7))
  have hη : 0 < η := lt_min hε (lt_min (by positivity) (by positivity))
  have hηε : η ≤ ε := min_le_left _ _
  have hηc : η ≤ c/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηE' : η ≤ ηE/7 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨D,hD,hG⟩ := hSelect b hb hbc η ρ hη hρ
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp hPenalty
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp
    (eventually_few_codegree_edges H ha ha2 hc ht (show 0 < σ/2 by positivity) hD h)
  have hGrow : Tendsto (fun n : ℕ => (b-a)/2*(n : ℝ)^(α-1)) atTop atTop :=
    ((tendsto_rpow_atTop (show 0 < α-1 by linarith)).comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (by linarith)
  obtain ⟨K₃,hK₃⟩ := eventually_atTop.mp (hGrow.eventually_gt_atTop 1)
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hExp,hSafe,lam,mu,hlam,hmu,hOpt,hBudget,hEnergy,hSlope⟩ :=
    hG (max L (max K₁ (max K₂ K₃)))
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hn₁ : K₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : K₂ ≤ n := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn₃ : K₃ ≤ n := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hP : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hPβ : 0 ≤ (n : ℝ)^(α-1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hDenseε : (c-ε)*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c-ε ≤ c-η) hP).trans hDense
  have hDenseHalf : c/2*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c/2 ≤ c-η) hP).trans hDense
  have hDegA (v : Fin n) : a*(n : ℝ)^(α-1) ≤ degreeR G v :=
    (mul_le_mul_of_nonneg_right hab.le hPβ).trans (hDeg v).1
  have hSlopeA : a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) :=
    (mul_le_mul_of_nonneg_right hab.le hPβ).trans hSlope
  have hEnergyε : lam*energy G ≤ 7*ε*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*η ≤ 7*ε) hP)
  have hEnergyE : lam*energy G ≤ ηE*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*η ≤ ηE) hP)
  have hFewP := hK₁ n hn₁ (Fin n) G (Fintype.card_fin n) hFree lam hlam.le hEnergyE
  have hFewC := hK₂ n hn₂ (Fin n) G hFree (fun v => (hDeg v).2)
  let B := badEdges G (t*(n : ℝ)^(α-1)) ∪ badPenaltyEdges G lam (t*(n : ℝ)^(α-1))
  have hB : (B.card : ℝ) ≤ σ*edgesR G := by
    have hcard : (B.card : ℝ) ≤ (badEdges G (t*(n : ℝ)^(α-1))).card+
        (badPenaltyEdges G lam (t*(n : ℝ)^(α-1))).card := by exact_mod_cast card_union_le _ _
    have hHalf := mul_le_mul_of_nonneg_left hDenseHalf (show 0 ≤ σ/2 by positivity)
    nlinarith only [hcard,hFewP,hFewC,hHalf]
  refine ⟨n,G,hnL,hFree,hDenseε,(fun v => ⟨hDegA v,(hDeg v).2⟩),hExp,hSafe,
    lam,mu,hlam,hmu,hOpt,hBudget,hEnergyε,hSlopeA,B,hB,?_,?_⟩
  · intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact (mem_filter.mp hp).2.1
  · intro u v huv hnot
    have hnC : (u,v) ∉ badEdges G (t*(n : ℝ)^(α-1)) :=
      fun h => hnot (mem_union_left _ h)
    have hnP : (u,v) ∉ badPenaltyEdges G lam (t*(n : ℝ)^(α-1)) :=
      fun h => hnot (mem_union_right _ h)
    have hC : (Nat.card (G.commonNeighbors u v) : ℝ) ≤ t*(n : ℝ)^(α-1) := by
      by_contra hh
      exact hnC (mem_filter.mpr ⟨mem_univ _,huv,lt_of_not_ge hh⟩)
    have hP : 2*lam*degreeR G u*degreeR G v ≤ t*(n : ℝ)^(α-1) := by
      by_contra hh
      exact hnP (mem_filter.mpr ⟨mem_univ _,huv,lt_of_not_ge hh⟩)
    have hLarge := hK₃ n hn₃
    have hcost : a*(n : ℝ)^(α-1)+(Nat.card (G.commonNeighbors u v) : ℝ)+1+
        2*lam*degreeR G u*degreeR G v < mu*(2*n-1) := by
      dsimp only [t] at hC hP
      nlinarith only [hC,hP,hLarge,hSlope]
    refine ⟨hcost,?_⟩
    intro T hT
    apply Erdos713PenalizedContraction.witness_avoiding hOpt hlam.le huv.ne T
    simp only [Fintype.card_fin]
    linarith

#print axioms joint
end Erdos713SharpPenaltyEdgeExpanders
