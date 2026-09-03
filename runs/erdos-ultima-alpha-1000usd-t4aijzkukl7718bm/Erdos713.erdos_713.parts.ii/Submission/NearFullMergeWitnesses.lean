import FormalConjecturesUtil
import Submission.NearFullPenaltyWitnesses
import Submission.MergeDegreePenalty

/-! Near-full hosts with both degree bounds, positive clone budget, and
arbitrarily few individually safe mergers on the same host. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713NearFullMergeWitnesses
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713NearFullPenaltyWitnesses Erdos713MergeDegreePenalty
variable {W : Type*}
set_option maxHeartbeats 2000000

lemma eventual_small_energy {α D a ρ : ℝ} (ha : α < 2) (ha0 : 0 < a) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ ∀ G : SimpleGraph (Fin n),
      (∀ v, degreeR G v ≤ D*(n : ℝ)^(α-1)) →
      energy G ≤ (a*ρ/2)*(n : ℝ)^(α+1) := by
  have hz : Tendsto (fun n : ℕ => D^2*(n : ℝ)^(α-2)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (show 0 < 2-α by linarith)).comp
      tendsto_natCast_atTop_atTop).const_mul (D^2)
    simpa only [neg_sub,mul_zero] using hh
  filter_upwards [hz.eventually_le_const (show 0 < a*ρ/2 by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  refine ⟨hn1,?_⟩
  intro G hD
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have henergy : energy G ≤ (n : ℝ)*(D*(n : ℝ)^(α-1))^2 := by
    have hh := sum_le_sum (s := (univ : Finset (Fin n)))
      (fun v _ => pow_le_pow_left₀ (degreeR_nonneg G v) (hD v) 2)
    simpa only [energy,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have heq : (n : ℝ)*(D*(n : ℝ)^(α-1))^2=(D^2*(n : ℝ)^(α-2))*(n : ℝ)^(α+1) := by
    calc
      _ = D^2*((n : ℝ)^(1 : ℝ)*(n : ℝ)^((α-1)*(2 : ℕ))) := by
        rw [Real.rpow_one,Real.rpow_mul_natCast hnR.le]
        ring
      _ = D^2*(n : ℝ)^(2*α-1) := by
        rw [← Real.rpow_add hnR]
        congr 2
        ring
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hnR]
        congr 2
        ring
  exact henergy.trans (heq.le.trans (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hnR.le _)))

lemma few_safe_of_controls {n : ℕ} {H : SimpleGraph W} {G : SimpleGraph (Fin n)}
    {α a ρ lam mu : ℝ} (hn : 1 ≤ n) (ha : 0 < a)
    (hg : GlobalOptimal H G lam mu) (hlam : 0 ≤ lam)
    (hSlope : a*(n : ℝ)^(α-1) ≤ mu*(2*n-1))
    (hEnergy : energy G ≤ (a*ρ/2)*(n : ℝ)^(α+1))
    (hPenalty : lam*energy G ≤ (a*ρ/4)*(n : ℝ)^α) :
    ((safePairs H G).card : ℝ) ≤ ρ*(n : ℝ)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hBudget := safePairs_energy_budget hg hlam
  simp only [Fintype.card_fin] at hBudget
  have hSlope' := mul_le_mul_of_nonneg_right hSlope (Nat.cast_nonneg (safePairs H G).card)
  have hp : 2*(n : ℝ)*(lam*energy G) ≤ (a*ρ/2)*(n : ℝ)^(α+1) := by
    calc
      _ ≤ 2*(n : ℝ)*((a*ρ/4)*(n : ℝ)^α) :=
        mul_le_mul_of_nonneg_left hPenalty (by positivity)
      _ = (a*ρ/2)*((n : ℝ)^α*(n : ℝ)^(1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hnR]
  have hSum : (1+2*lam*(n : ℝ))*energy G ≤ (a*ρ)*(n : ℝ)^(α+1) := by
    nlinarith only [hEnergy,hp]
  have hpow : (n : ℝ)^(α-1)*(n : ℝ)^2=(n : ℝ)^(α+1) := by
    rw [← Real.rpow_two,← Real.rpow_add hnR]
    congr 1
    ring
  have hbound : (a*(n : ℝ)^(α-1))*((safePairs H G).card : ℝ) ≤
      (a*(n : ℝ)^(α-1))*(ρ*(n : ℝ)^2) := by
    calc
      _ ≤ _ := hSlope'.trans (hBudget.trans hSum)
      _ = _ := by rw [← hpow]; ring
  exact (mul_le_mul_iff_right₀ (mul_pos ha (Real.rpow_pos_of_pos hnR _))).mp hbound

/-- Both tolerances are chosen after the positive lower-degree and clone
budget constants, and before the fixed maximum-degree coefficient. No
pruning or change of host follows selection. -/
theorem near_full_few_safe_mergers [Fintype W] (H : SimpleGraph W) (hH : H.IsBipartite)
    (hEdge : ∃ v w, H.Adj v w) {α c : ℝ} (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
      ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ H.Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        ((safePairs H G).card : ℝ) ≤ ρ*(n : ℝ)^2 ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal H G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu := by
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_joint_controlled H hH hEdge ha ha2 hc h
  refine ⟨a,κ,ha',hκ,?_⟩
  intro ε ρ hε hρ
  let ζ : ℝ := min ε (a*ρ/28)
  have hζ : 0 < ζ := lt_min hε (by positivity)
  obtain ⟨D,hD,hD'⟩ := hs ζ hζ
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventual_small_energy (D := D) ha2 ha' hρ)
  refine ⟨D,hD,?_⟩
  intro L
  obtain ⟨n,G,hn,hFree,hDense,hDeg,_,lam,mu,hlam,hmu,hG,hBudget,hPenalty,hSlope⟩ := hD' (max L K)
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hnK : K ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hn1,hE⟩ := hK n hnK
  have hDense' : (c-ε)*(n : ℝ)^α ≤ edgesR G := by
    have hm := mul_nonneg (sub_nonneg.mpr (min_le_left ε (a*ρ/28)))
      (Real.rpow_nonneg (Nat.cast_nonneg n) α)
    change 0 ≤ (ε-ζ)*(n : ℝ)^α at hm
    nlinarith only [hDense,hm]
  have hPenalty' : lam*energy G ≤ (a*ρ/4)*(n : ℝ)^α := by
    have hh : 7*ζ ≤ a*ρ/4 := by have ht := min_le_right ε (a*ρ/28); change ζ ≤ _ at ht; linarith
    exact hPenalty.trans (mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (Nat.cast_nonneg n) α))
  have hFew := few_safe_of_controls hn1 ha' hG hlam.le hSlope (hE G (fun v => (hDeg v).2)) hPenalty'
  exact ⟨n,G,hnL,hFree,hDense',hDeg,hFew,lam,mu,hlam,hmu,hG,hBudget⟩

#print axioms few_safe_of_controls
#print axioms near_full_few_safe_mergers
end Erdos713NearFullMergeWitnesses
