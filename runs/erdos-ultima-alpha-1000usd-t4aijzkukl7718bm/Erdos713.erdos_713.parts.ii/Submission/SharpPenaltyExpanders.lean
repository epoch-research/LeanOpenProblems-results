import FormalConjecturesUtil
import Submission.SharpPenaltyWitnesses
import Submission.NearFullIntrinsicExpansion
import Submission.NearFullMergeWitnesses

/-! Same-host sharp lower degree, expansion, clone budget, and few safe mergers.
These necessary conditions do not settle the rationality conjecture. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713SharpPenaltyExpanders
open Erdos713Cloning Erdos713DegreePenalty Erdos713DegreePenaltySupports
open Erdos713CloneResistance Erdos713MergeDegreePenalty
open Erdos713SharpPenaltyWitnesses Erdos713NearFullMergeWitnesses
open Erdos713NearFullIntrinsicExpansion Erdos713SwitchGluing
variable {W : Type*}
set_option maxHeartbeats 2000000

/-- The expansion and clone-budget constants are chosen before the requested
lower-degree coefficient, density accuracy, and safe-merger tolerance. -/
theorem joint [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ κ ξ : ℝ, 0 < κ ∧ 0 < ξ ∧ ∀ a : ℝ, 0 < a → a < c*α →
      ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          ξ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
        ((safePairs H G).card : ℝ) ≤ ρ*(n : ℝ)^2 ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu ∧
          lam*energy G ≤ 7*ε*(n : ℝ)^α ∧
          a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) := by
  obtain ⟨κ,hκ,hSharp⟩ := near_full_sharp_controlled H hH hEdge ha ha2 hc h
  obtain ⟨η,ξ,hη,hξ,hExpand⟩ := eventually_expanding_near_full H ha hc h
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp hExpand
  refine ⟨κ,ξ,hκ,hξ,?_⟩
  intro a ha0 hac ε ρ hε hρ
  let b := max a c
  have hb : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  let ζ := min ε (min η (a*ρ/28))
  have hζ : 0 < ζ := lt_min hε (lt_min hη (by positivity))
  have hζε : ζ ≤ ε := min_le_left _ _
  have hζη : ζ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hζρ : ζ ≤ a*ρ/28 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨D,hD,hSelect⟩ := hSharp b hb hbc ζ hζ
  obtain ⟨K₂,hK₂⟩ := eventually_atTop.mp (eventual_small_energy (D := D) ha2 ha0 hρ)
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,_hMass,lam,mu,hlam,hmu,hG,hBudget,hPenalty,hSlope⟩ :=
    hSelect (max L (max K₁ K₂))
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hn₁ : K₁ ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : K₂ ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have hPow : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) α
  have hPowβ : 0 ≤ (n : ℝ)^(α-1) := Real.rpow_nonneg (Nat.cast_nonneg n) (α-1)
  have hDenseε : (c-ε)*(n : ℝ)^α ≤ edgesR G :=
    (mul_le_mul_of_nonneg_right (by linarith : c-ε ≤ c-ζ) hPow).trans hDense
  have hDenseη : (c-η)*(n : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) := by
    exact (mul_le_mul_of_nonneg_right (by linarith : c-η ≤ c-ζ) hPow).trans hDense
  have hDegA (v : Fin n) : a*(n : ℝ)^(α-1) ≤ degreeR G v :=
    (mul_le_mul_of_nonneg_right (le_max_left a c) hPowβ).trans (hDeg v).1
  have hDegC (v : Fin n) : c/48*(n : ℝ)^(α-1) ≤
      (Nat.card (G.neighborSet v) : ℝ) := by
    have hcb : c/48 ≤ b := (by linarith : c/48 ≤ c).trans (le_max_right a c)
    exact (mul_le_mul_of_nonneg_right hcb hPowβ).trans (hDeg v).1
  have hExpansion := hK₁ n hn₁ (Fin n) G (Fintype.card_fin n) hFree hDenseη hDegC
  have hSlopeA : a*(n : ℝ)^(α-1) ≤ mu*(2*n-1) :=
    (mul_le_mul_of_nonneg_right (le_max_left a c) hPowβ).trans hSlope
  have hPenaltyρ : lam*energy G ≤ (a*ρ/4)*(n : ℝ)^α := by
    have hh : 7*ζ ≤ a*ρ/4 := by linarith
    exact hPenalty.trans (mul_le_mul_of_nonneg_right hh hPow)
  have hPenaltyε : lam*energy G ≤ 7*ε*(n : ℝ)^α := by
    have hh : 7*ζ ≤ 7*ε := by linarith
    exact hPenalty.trans (mul_le_mul_of_nonneg_right hh hPow)
  obtain ⟨hn1,hE⟩ := hK₂ n hn₂
  have hFew := few_safe_of_controls hn1 ha0 hG hlam.le hSlopeA
    (hE G (fun v => (hDeg v).2)) hPenaltyρ
  exact ⟨n,G,hnL,hFree,hDenseε,(fun v => ⟨hDegA v,(hDeg v).2⟩),hExpansion,hFew,
    lam,mu,hlam,hmu,hG,hBudget,hPenaltyε,hSlopeA⟩

#print axioms joint
end Erdos713SharpPenaltyExpanders
