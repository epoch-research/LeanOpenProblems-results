import FormalConjecturesUtil
import Submission.UniformPairCost
import Submission.SharpPenaltyExpanders
import Submission.NearFullC8MergeInteractions

/-! Common edge losses below twice the sharp merger slope still leave
almost all C8 mergers obstructed on the same near-full expanding host.
This is a necessary condition, not a rationality proof. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713SharpCommonBlockerC8
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713MergeDegreePenalty Erdos713SwitchGluing Erdos713UniformPairCost
open Erdos713CommonBlockerPairCount
set_option maxHeartbeats 2000000

lemma eventually_double_slope {a b β : ℝ} (ha : 0 < a) (hab : a < 2*b) (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ mu : ℝ,
      b*(n : ℝ)^β ≤ mu*(2*n-1) →
      a*(n : ℝ)^β+2*((2*b-a)/8*(n : ℝ)^β)+1 < mu*(4*n-4) := by
  let g := 2*b-a
  let r := (a+2*b)/2
  have hg : 0 < g := by dsimp [g]; linarith
  have hb : 0 < b := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨K,hK⟩ := exists_nat_gt (4*b/g)
  have hGrow : Tendsto (fun n : ℕ => g/4*(n : ℝ)^β) atTop atTop :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop K,hGrow.eventually_gt_atTop 1,
    eventually_gt_atTop (1 : ℕ)] with n hn hGrow hn1
  refine ⟨by omega,?_⟩
  intro mu hSlope
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hP : 0 ≤ (n : ℝ)^β := Real.rpow_nonneg (by positivity) _
  have hKn : (K : ℝ) ≤ n := by exact_mod_cast hn
  have hRatio : r*(2*n-1) ≤ b*(4*n-4) := by
    have hgb : 4*b < (K : ℝ)*g := (div_lt_iff₀ hg).mp hK
    have hgn := mul_le_mul_of_nonneg_right hKn hg.le
    dsimp [g,r] at *
    nlinarith only [hgb,hgn,hr]
  have hRat := mul_le_mul_of_nonneg_right hRatio hP
  have hSl := mul_le_mul_of_nonneg_right hSlope (show 0 ≤ (4 : ℝ)*n-4 by linarith)
  have hJoint : r*(n : ℝ)^β ≤ mu*(4*n-4) := by
    apply (mul_le_mul_iff_right₀ (show 0 < (2 : ℝ)*n-1 by linarith)).mp
    nlinarith only [hRat,hSl]
  dsimp only [g,r] at hGrow hJoint
  nlinarith only [hGrow,hJoint]

/-- The expansion and positive clone-budget constants precede every accuracy.
The same graph satisfies the conclusion for EVERY retained spanning subgraph
with the stated loss. Neither exact edge maximality nor cheap blockers are
asserted. -/
theorem joint {α c : ℝ} (ha : 1 < α) (ha2 : α < 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ ξ : ℝ, 0 < κ ∧ 0 < ξ ∧ ∀ a : ℝ, 0 < a → a < 2*c*α →
      ∀ ε ρ : ℝ, 0 < ε → 0 < ρ → ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ,
        ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
          L ≤ n ∧ (cycleGraph 8).Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
          (∀ v, (a/2)*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
          (∀ S : Finset (Fin n), 2*S.card ≤ n →
            ξ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
          ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal (cycleGraph 8) G lam mu ∧
            κ*(n : ℝ)^α ≤ netBudget G lam mu ∧ lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
            ∀ F : SimpleGraph (Fin n), F ≤ G →
              edgesR G ≤ edgesR F+a*(n : ℝ)^(α-1) →
              ((safePairs (cycleGraph 8) F).card : ℝ) ≤ ρ*(n : ℝ)^2 := by
  obtain ⟨κ,ξ,hκ,hξ,hSelect⟩ := Erdos713SharpPenaltyExpanders.joint (cycleGraph 8)
    Erdos713NearFullC8MergeInteractions.cycle_eight_bipartite ⟨0,1,by decide⟩
    ha (by linarith : α < 2) hc h
  refine ⟨κ,ξ,hκ,hξ,?_⟩
  intro a ha0 hac ε ρ hε hρ
  let b := (a+2*c*α)/4
  have hb : 0 < b := by dsimp [b]; positivity
  have hbc : b < c*α := by dsimp [b]; linarith
  have hab : a < 2*b := by dsimp [b]; linarith
  let s := (2*b-a)/8
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨η,hη,hCost⟩ := eventually_few_highCost (cycleGraph 8) ha (by linarith) hc hs
    (show 0 < ρ/2 by positivity) h
  let ζ := min ε (η/7)
  have hζ : 0 < ζ := lt_min hε (by positivity)
  have hζε : ζ ≤ ε := min_le_left _ _
  have hζη : ζ ≤ η/7 := min_le_right _ _
  obtain ⟨D,hD,hG⟩ := hSelect b hb hbc ζ 1 hζ (by norm_num)
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp hCost
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp
    (eventually_sparse (C := D) (by linarith : α-1 < 1/4) (show 0 < ρ/2 by positivity))
  obtain ⟨K₃,hK₃⟩ := eventually_atTop.mp
    (eventually_double_slope ha0 hab (by linarith : 0 < α-1))
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hExp,_hSafe,lam,mu,hlam,hmu,hOpt,hBudget,hEnergy,hSlope⟩ :=
    hG (max L (max K₁ (max K₂ K₃)))
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hn₁ : K₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : K₂ ≤ n := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn₃ : K₃ ≤ n := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hn
  have hn0 : 0 < n := (hK₃ n hn₃).1
  have hP : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hPβ : 0 ≤ (n : ℝ)^(α-1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hDenseε : (c-ε)*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c-ε ≤ c-ζ) hP).trans hDense
  have hDegA (v : Fin n) : (a/2)*(n : ℝ)^(α-1) ≤ degreeR G v :=
    (mul_le_mul_of_nonneg_right (by linarith : a/2 ≤ b) hPβ).trans (hDeg v).1
  have hEnergyε : lam*energy G ≤ 7*ε*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ 7*ε) hP)
  have hEnergyη : lam*energy G ≤ η*(n : ℝ)^α :=
    hEnergy.trans (mul_le_mul_of_nonneg_right (by linarith : 7*ζ ≤ η) hP)
  have hHigh := hK₁ n hn₁ G hFree lam hlam.le hEnergyη
  have hJointCost := (hK₃ n hn₃).2 mu hSlope
  refine ⟨n,G,hnL,hFree,hDenseε,(fun v => ⟨hDegA v,(hDeg v).2⟩),hExp,
    lam,mu,hlam,hmu,hOpt,hBudget,hEnergyε,?_⟩
  intro F hFG hLoss
  let B := highCost G lam (s*(n : ℝ)^(α-1))
  let S := safePairs (cycleGraph 8) F \ B
  have hSafeS : ∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2 := by
    intro p hp
    simpa only [safePairs,mem_filter,mem_univ,true_and] using (mem_sdiff.mp hp).1
  have hCostS : ∀ p ∈ S, pairCost G lam p ≤ s*(n : ℝ)^(α-1) := by
    intro p hp
    have hh := (mem_sdiff.mp hp).2
    simpa only [B,highCost,mem_filter,mem_univ,true_and,not_lt] using hh
  letI : Nonempty (Fin n) := ⟨⟨0,hn0⟩⟩
  obtain ⟨v,hv⟩ := F.exists_maximal_degree_vertex
  have hCap : (F.maxDegree : ℝ) ≤ D*(n : ℝ)^(α-1) := by
    rw [hv]
    have hh := (degreeR_mono hFG v).trans (hDeg v).2
    simpa only [degreeR,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh
  have hS : (S.card : ℝ) ≤ (ρ/2)*(n : ℝ)^2 :=
    hK₂ n hn₂ G F lam mu (a*(n : ℝ)^(α-1)) (s*(n : ℝ)^(α-1))
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

#print axioms eventually_double_slope
#print axioms joint
end Erdos713SharpCommonBlockerC8
