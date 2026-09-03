import FormalConjecturesUtil
import Submission.SafeBatchAsymptotics
import Submission.SharpPenaltyExpanders
import Submission.NearFullC8MergeInteractions

/-! Robustness to any fixed degree-scale common loss on near-full C8-free
hosts. The degree cap is chosen before the loss coefficient. This remains
a necessary condition and does not prove rationality of the exponent. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713ArbitraryCommonBlockerC8
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713MergeDegreePenalty Erdos713SwitchGluing Erdos713UniformPairCost
open Erdos713CommonBlockerPairCount Erdos713MergeCostPropagation Erdos713SafeBatchAsymptotics
set_option maxHeartbeats 2000000

/-- D precedes the arbitrary loss coefficient A. All of the conclusions,
including the universal statement over retained spanning subgraphs, hold
on one selected host. The order threshold may depend on A. -/
theorem joint {α c : ℝ} (ha : 1 < α) (ha2 : α < 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ ξ : ℝ, 0 < κ ∧ 0 < ξ ∧ ∀ b : ℝ, 0 < b → b < c*α →
      ∀ ε ρ : ℝ, 0 < ε → 0 < ρ → ∃ D : ℝ, 0 < D ∧ ∀ A : ℝ, 0 < A → ∀ L : ℕ,
        ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
          L ≤ n ∧ (cycleGraph 8).Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
          (∀ v, b*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
          (∀ S : Finset (Fin n), 2*S.card ≤ n →
            ξ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
          ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal (cycleGraph 8) G lam mu ∧
            κ*(n : ℝ)^α ≤ netBudget G lam mu ∧ lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
            ∀ F : SimpleGraph (Fin n), F ≤ G →
              edgesR G ≤ edgesR F+A*(n : ℝ)^(α-1) →
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
  intro A _hA L
  obtain ⟨k,hk⟩ := exists_nat_gt (4*A/b)
  have hk' : A < (k : ℝ)*b/4 := by
    have hh := (div_lt_iff₀ hb).mp hk
    linarith
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp
    (eventually_pair_count k (C := D) (by linarith : α-1 < 1/4) (show 0 < ρ/2 by positivity))
  obtain ⟨K₃,hK₃⟩ := eventually_atTop.mp
    (eventually_batch_slope k hb hk' (by linarith : 0 < α-1))
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hExp,_hSafe,lam,mu,hlam,hmu,hOpt,hBudget,hEnergy,hSlope⟩ :=
    hG (max L (max K₁ (max K₂ K₃)))
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hn₁ : K₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : K₂ ≤ n := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn₃ : K₃ ≤ n := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn0 : 0 < n := (hK₃ n hn₃).1
  have hP : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hDenseε : (c-ε)*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c-ε ≤ c-ζ) hP).trans hDense
  have hEnergyε : lam*energy G ≤ 7*ε*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ 7*ε) hP)
  have hEnergyη : lam*energy G ≤ η*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ η) hP)
  have hHigh := hK₁ n hn₁ G hFree lam hlam.le hEnergyη
  have hJointCost := (hK₃ n hn₃).2 mu hmu.le hSlope
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
  have hS : (S.card : ℝ) ≤ (ρ/2)*(n : ℝ)^2 :=
    hK₂ n hn₂ G F lam mu (A*(n : ℝ)^(α-1)) (s*(n : ℝ)^(α-1))
      hOpt hlam.le hFG hLoss S hSafeS hCostS hJointCost F.maxDegree F.degree_le_maxDegree hCap
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
end Erdos713ArbitraryCommonBlockerC8
