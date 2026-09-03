import FormalConjecturesUtil
import Submission.RelativeExpansion

/-! Expansion from near-full density and a fixed positive minimum-degree
coefficient. Exact edge extremality is not required. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713NearFullIntrinsicExpansion
open Erdos713Cloning Erdos713SwitchGluing Erdos713RelativeExpansion
set_option maxHeartbeats 2000000

theorem eventually_expanding_near_full {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ η κ : ℝ, 0 < η ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = n →
        H.Free G → (c-η)*(n : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) →
        (∀ v, c/48*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) →
        ∀ S : Finset V, 2*S.card ≤ n →
          κ*S.card*(n : ℝ)^(α-1) ≤ (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
  classical
  let δ : ℝ := (1/768 : ℝ)^((α-1)⁻¹)
  have hd : 0 < δ := Real.rpow_pos_of_pos (by norm_num) _
  have hd1 : δ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.mpr (by linarith))
  have hdpow : δ^(α-1) = 1/768 := Real.rpow_inv_rpow (by norm_num) (by linarith)
  let k := expansionConstant α
  have hk : 0 < k := expansionConstant_pos ha
  have hk1 : k < 1 := by
    have hh := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) (α-1)
    dsimp only [k,expansionConstant]
    linarith
  let η := c*k*δ/8
  have hη : 0 < η := by dsimp [η]; positivity
  have hηc : η < c/2 := by
    have hh := mul_lt_mul_of_pos_left hk1 hc
    have hh' := mul_lt_mul_of_pos_left hd1 (mul_pos hc hk)
    dsimp only [η]
    nlinarith
  obtain ⟨B,hB,hUpper⟩ := linear_error_upper (fun n => extremalNumber n H)
    (extremal_zero H) (show 0 < c+η by positivity) (by linarith) h
  let κ := min (c/96) (c*k/2)
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  let b := min (c/384) (c*k*δ/4)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have htop : Tendsto (fun n : ℕ => b*(n : ℝ)^(α-1)) atTop atTop :=
    Tendsto.const_mul_atTop hb
      ((tendsto_rpow_atTop (by linarith : 0 < α-1)).comp tendsto_natCast_atTop_atTop)
  refine ⟨η,κ,hη,hκ,?_⟩
  filter_upwards [htop.eventually_ge_atTop B,
    eventually_gt_atTop (0 : ℕ)] with n hBn hn
  intro V instV G hcard hFree hE hDeg S hS
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hsNat : S.card ≤ n := by omega
  have hhalf : (2 : ℝ)*S.card ≤ n := by exact_mod_cast hS
  have hp : 0 < (n : ℝ)^(α-1) := Real.rpow_pos_of_pos hnR _
  have hBsmall : B ≤ c/384*(n : ℝ)^(α-1) := hBn.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hp.le)
  have hBlarge : B ≤ c*k*δ/4*(n : ℝ)^(α-1) := hBn.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le)
  by_cases hsmall : (S.card : ℝ) ≤ δ*n
  · have hmindeg (v : V) : c/48*(n : ℝ)^(α-1) ≤ (G.degree v : ℝ) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hDeg v
    have hSum := sum_le_sum (s := S) (fun v _ => hmindeg v)
    simp only [sum_const,nsmul_eq_mul] at hSum
    have hCut := degree_cut_bound H G hFree S
    have hCutR : (∑ v ∈ S, (G.degree v : ℝ)) ≤ 2*(extremalNumber S.card H : ℝ)+
        (Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by exact_mod_cast hCut
    have hUS : (extremalNumber S.card H : ℝ) ≤ 2*c*(S.card : ℝ)^α+B*S.card := by
      have hm := mul_le_mul_of_nonneg_right (show c+η ≤ 2*c by linarith)
        (Real.rpow_nonneg hsR α)
      exact (hUpper S.card).trans (by linarith)
    have hcut : c/48*(S.card : ℝ)*(n : ℝ)^(α-1) ≤
        4*c*(S.card : ℝ)^α+2*B*S.card+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
      nlinarith only [hSum,hCutR,hUS]
    have hout := small_cut_bound ha hc hnR.le hsR hd.le hsmall hdpow hBsmall hcut
    have hle := mul_le_mul_of_nonneg_right (min_le_left (c/96) (c*k/2))
      (show 0 ≤ (S.card : ℝ)*(n : ℝ)^(α-1) by positivity)
    calc
      _ = κ*((S.card : ℝ)*(n : ℝ)^(α-1)) := by ring
      _ ≤ c/96*((S.card : ℝ)*(n : ℝ)^(α-1)) := hle
      _ ≤ _ := by simpa only [mul_assoc] using hout
  · have hCut := edges_le_parts_and_cut H G hFree S
    rw [hcard] at hCut
    have hCutR : (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber S.card H : ℝ)+
        (extremalNumber (n-S.card) H : ℝ)+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) :=
      by exact_mod_cast hCut
    have hUS := hUpper S.card
    have hUT := hUpper (n-S.card)
    rw [Nat.cast_sub hsNat] at hUT
    have hcut : (c-η)*(n : ℝ)^α ≤ (c+η)*((S.card : ℝ)^α+((n : ℝ)-S.card)^α)+
        B*n+(Nat.card (cross G (S : Set V)).edgeSet : ℝ) := by
      nlinarith only [hE,hCutR,hUS,hUT]
    have hout := large_cut_bound ha hc hnR.le hsR hhalf (le_of_not_ge hsmall)
      hη.le (show η = c*expansionConstant α*δ/8 from rfl) hBlarge hcut
    have hle := mul_le_mul_of_nonneg_right (min_le_right (c/96) (c*k/2))
      (show 0 ≤ (S.card : ℝ)*(n : ℝ)^(α-1) by positivity)
    change c*k/2*(S.card : ℝ)*(n : ℝ)^(α-1) ≤ _ at hout
    calc
      _ = κ*((S.card : ℝ)*(n : ℝ)^(α-1)) := by ring
      _ ≤ c*k/2*((S.card : ℝ)*(n : ℝ)^(α-1)) := hle
      _ ≤ _ := by simpa only [mul_assoc] using hout

#print axioms eventually_expanding_near_full
end Erdos713NearFullIntrinsicExpansion
