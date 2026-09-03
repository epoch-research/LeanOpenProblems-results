import FormalConjecturesUtil
import Submission.GrowingBatchEstimates
import Submission.SharpPenaltyExpanders
import Submission.NearFullC8MergeInteractions

/-! Polynomially larger common-loss robustness on near-full C8-free hosts.
The degree cap precedes the loss coefficient and growth increment. The
batch size genuinely grows with order; no fixed-batch quantifier swap is used.
This is a necessary condition, not a rationality theorem. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713GrowingCommonBlockerC8
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713MergeDegreePenalty Erdos713SwitchGluing Erdos713UniformPairCost
open Erdos713CommonBlockerPairCount Erdos713MergeCostPropagation
open Erdos713GrowingBatchEstimates Erdos713SafeMergeBatch
set_option maxHeartbeats 2000000

/-- D precedes both δ and A. The positive increment satisfies δ<α-1
and δ+4(α-1)<1. The host and order threshold may depend on δ and A. -/
theorem joint {α c : ℝ} (ha : 1 < α) (ha2 : α < 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ ξ : ℝ, 0 < κ ∧ 0 < ξ ∧ ∀ b : ℝ, 0 < b → b < c*α →
      ∀ ε ρ : ℝ, 0 < ε → 0 < ρ → ∃ D : ℝ, 0 < D ∧
        ∀ δ : ℝ, 0 < δ → δ < α-1 → δ+4*(α-1) < 1 →
        ∀ A : ℝ, 0 < A → ∀ L : ℕ,
        ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
          L ≤ n ∧ (cycleGraph 8).Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
          (∀ v, b*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
          (∀ S : Finset (Fin n), 2*S.card ≤ n →
            ξ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
          ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal (cycleGraph 8) G lam mu ∧
            κ*(n : ℝ)^α ≤ netBudget G lam mu ∧ lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
            ∀ F : SimpleGraph (Fin n), F ≤ G →
              edgesR G ≤ edgesR F+A*(n : ℝ)^(α-1+δ) →
              ((safePairs (cycleGraph 8) F).card : ℝ) ≤ ρ*(n : ℝ)^2 := by
  obtain ⟨κ,ξ,hκ,hξ,hSelect⟩ := Erdos713SharpPenaltyExpanders.joint (cycleGraph 8)
    Erdos713NearFullC8MergeInteractions.cycle_eight_bipartite ⟨0,1,by decide⟩
    ha (by linarith : α < 2) hc h
  refine ⟨κ,ξ,hκ,hξ,?_⟩
  intro b hb hbc ε ρ hε hρ
  let s := b/4
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨η,hη,hCost⟩ := eventually_few_highCost (cycleGraph 8) ha (by linarith) hc hs
    (show 0 < ρ/2 by positivity) h
  let ζ := min ε (η/7)
  have hζ : 0 < ζ := lt_min hε (by positivity)
  have hζε : ζ ≤ ε := min_le_left _ _
  have hζη : ζ ≤ η/7 := min_le_right _ _
  obtain ⟨D,hD,hG⟩ := hSelect b hb hbc ζ 1 hζ (by norm_num)
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp hCost
  refine ⟨D,hD,?_⟩
  intro δ hδ hδβ hgap A hA L
  have hβ : 0 < α-1 := by linarith
  have hδ1 : δ < 1 := by linarith
  obtain ⟨K,hK,hBatch⟩ := eventually_batch hA hb hδ.le hδβ hδ1
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp
    (eventually_lossBound (C := D) hβ.le hK.le hgap (show 0 < ρ/2 by positivity))
  obtain ⟨K₃,hK₃⟩ := eventually_atTop.mp hBatch
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hExp,_hSafe,lam,mu,hlam,hmu,hOpt,hBudget,hEnergy,hSlope⟩ :=
    hG (max L (max K₁ (max K₂ (max K₃ 1))))
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hn₁ : K₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : K₂ ≤ n := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn₃ : K₃ ≤ n := ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn0 : 0 < n := by
    have hh : 1 ≤ n := ((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hn
    omega
  obtain ⟨k,hk,hBatchCost⟩ := hK₃ n hn₃
  have hP : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hDenseε : (c-ε)*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c-ε ≤ c-ζ) hP).trans hDense
  have hEnergyε : lam*energy G ≤ 7*ε*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ 7*ε) hP)
  have hEnergyη : lam*energy G ≤ η*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ η) hP)
  have hHigh := hK₁ n hn₁ G hFree lam hlam.le hEnergyη
  have hJointCost := hBatchCost mu hmu.le hSlope
  refine ⟨n,G,hnL,hFree,hDenseε,hDeg,hExp,
    lam,mu,hlam,hmu,hOpt,hBudget,hEnergyε,?_⟩
  intro F hFG hLoss
  let B := highCost G lam (s*(n : ℝ)^(α-1))
  let S := safePairs (cycleGraph 8) F \ B
  have hSafeS : ∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2 := by
    intro p hp
    simpa only [safePairs,mem_filter,mem_univ,true_and] using (mem_sdiff.mp hp).1
  have hCostS : ∀ p ∈ S, pairCost F lam p ≤ s*(n : ℝ)^(α-1) := by
    intro p hp
    have hh := (mem_sdiff.mp hp).2
    have hh' : pairCost G lam p ≤ s*(n : ℝ)^(α-1) := by
      simpa only [B,highCost,mem_filter,mem_univ,true_and,not_lt] using hh
    exact (pairCost_mono hFG hlam.le p).trans hh'
  letI : Nonempty (Fin n) := ⟨⟨0,hn0⟩⟩
  obtain ⟨v,hv⟩ := F.exists_maximal_degree_vertex
  have hCap : (F.maxDegree : ℝ) ≤ D*(n : ℝ)^(α-1) := by
    rw [hv]
    have hh := (degreeR_mono hFG v).trans (hDeg v).2
    simpa only [degreeR,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh
  have hSfinite := pair_count hOpt hlam.le hFG hLoss k n F.maxDegree (by simp)
    (fun v => (F.degree_le_maxDegree v).trans (by omega)) S hSafeS
    (fun p _ => ⟨F.degree_le_maxDegree p.1,F.degree_le_maxDegree p.2⟩) hCostS
    (by simpa only [Fintype.card_fin,s] using hJointCost)
  have hS : (S.card : ℝ) ≤ (ρ/2)*(n : ℝ)^2 :=
    (Nat.cast_le.mpr hSfinite).trans (hK₂ n hn₂ k F.maxDegree hk hCap)
  have hsub : safePairs (cycleGraph 8) F ⊆ S ∪ B := by
    intro p hp
    by_cases hb : p ∈ B
    · exact mem_union_right _ hb
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hp,hb⟩)
  have hCard : ((safePairs (cycleGraph 8) F).card : ℝ) ≤ S.card+B.card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le S B)
  change (B.card : ℝ) ≤ (ρ/2)*(n : ℝ)^2 at hHigh
  linarith

#print axioms joint
end Erdos713GrowingCommonBlockerC8
