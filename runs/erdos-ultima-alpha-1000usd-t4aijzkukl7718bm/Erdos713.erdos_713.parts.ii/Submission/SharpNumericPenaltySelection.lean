import FormalConjecturesUtil
import Submission.NumericPenaltySelection

/-! Sharp slope control for normalized degree-penalty selection.
This is a supporting estimate, not a rationality theorem. -/
open Filter
open scoped Topology
namespace Erdos713SharpNumericPenaltySelection
open Erdos713PowerPotential Erdos713NumericPenaltySelection
set_option maxHeartbeats 2000000

lemma selection_errors_window {α c ε ρ : ℝ} (ha : 0 < α) (ha2 : α < 2)
    (hc : 0 < c) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ η < c ∧ η ≤ c*(1-α/2)/20 ∧ 4*η ≤ ε ∧
      ∀ t e p : ℝ, 0 ≤ t → 0 ≤ p →
        c*(1-α/2)-2*η ≤ e-p-c*α/2*t^2 → e ≤ (c+η)*t^α+η →
        1/2 < t ∧ t < 2 ∧ (c-ε)*t^α ≤ e ∧ p ≤ 7*η ∧
        e ≤ 5*(c+1) ∧ |t-1| < ρ := by
  obtain ⟨η₀,hη₀,hη₀1,hη₀c,hη₀M,hη₀ε,hbase⟩ :=
    selection_errors_strong ha ha2 hc hε
  obtain ⟨δ,hδ,_,hstable⟩ := stable_maximum ha ha2 hc
    (lt_min hρ (by norm_num : (0 : ℝ) < 1)) (min_le_right ρ 1)
  let η := min η₀ (δ/4)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hηle : η ≤ η₀ := min_le_left _ _
  have hηδ : 4*η ≤ δ := by
    have hh := min_le_right η₀ (δ/4)
    change η ≤ δ/4 at hh
    linarith
  refine ⟨η,hη,hηle.trans hη₀1,hηle.trans_lt hη₀c,hηle.trans hη₀M,
    (mul_le_mul_of_nonneg_left hηle (by norm_num)).trans hη₀ε,?_⟩
  intro t e p ht hp hpot he
  have htα : 0 ≤ t^α := Real.rpow_nonneg ht α
  have hcoef := mul_le_mul_of_nonneg_right hηle htα
  have hpot₀ : c*(1-α/2)-2*η₀ ≤ e-p-c*α/2*t^2 := by linarith
  have he₀ : e ≤ (c+η₀)*t^α+η₀ := by nlinarith only [he,hcoef,hηle]
  obtain ⟨htlo,hthi,hdense,_,hedge⟩ := hbase t e p ht hp hpot₀ he₀
  have ht4 : t^α ≤ 4 := by
    have hbase := Real.rpow_le_rpow ht hthi.le ha.le
    have hexp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) ha2.le
    exact hbase.trans (by simpa only [Real.rpow_two,
      show (2 : ℝ)^2 = 4 by norm_num] using hexp)
  have hphi : c*t^α-c*α/2*t^2 ≤ c*(1-α/2) := phi_le ha.le ha2.le hc.le ht
  have hηpow := mul_le_mul_of_nonneg_left ht4 hη.le
  have hpen : p ≤ 7*η := by nlinarith only [hpot,he,hphi,hηpow]
  have hclose : |t-1| < min ρ 1 := by
    apply hstable t ht
    have hcoef' := mul_nonneg (show 0 ≤ δ-η by linarith) htα
    nlinarith only [hpot,he,hp,hcoef',hηδ,hη.le]
  exact ⟨htlo,hthi,hdense,hpen,hedge,hclose.trans_le (min_le_left _ _)⟩

/-- The lower-slope coefficient can be any fixed a below c*α. -/
theorem selection_errors_sharp {α c ε a : ℝ} (ha : 1 < α) (ha2 : α < 2)
    (hc : 0 < c) (hε : 0 < ε) (haSlope : a < c*α) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ η < c ∧ η ≤ c*(1-α/2)/20 ∧ 4*η ≤ ε ∧
      ∀ t e p : ℝ, 0 ≤ t → 0 ≤ p →
        c*(1-α/2)-2*η ≤ e-p-c*α/2*t^2 → e ≤ (c+η)*t^α+η →
        1/2 < t ∧ t < 2 ∧ (c-ε)*t^α ≤ e ∧ p ≤ 7*η ∧
        e ≤ 5*(c+1) ∧ a*t^(α-1)+η ≤ c*α*t := by
  let ψ : ℝ → ℝ := fun t => c*α*t-a*t^(α-1)
  let γ := (c*α-a)/2
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hψ : Continuous ψ := by
    dsimp [ψ]
    fun_prop (disch := linarith)
  have hψ1 : ψ 1 = 2*γ := by
    dsimp [ψ,γ]
    simp only [Real.one_rpow,mul_one]
    ring
  have hneigh : ∀ᶠ t : ℝ in 𝓝 1, γ < ψ t :=
    hψ.continuousAt.tendsto.eventually_const_lt (by rw [hψ1]; linarith)
  obtain ⟨ρ,hρ,hρψ⟩ := Metric.eventually_nhds_iff.mp hneigh
  let ε' := min ε γ
  have hε' : 0 < ε' := lt_min hε hγ
  obtain ⟨η,hη,hη1,hηc,hηM,hηε',hnumeric⟩ :=
    selection_errors_window (by linarith : 0 < α) ha2 hc hε' hρ
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hηε : 4*η ≤ ε := hηε'.trans hε'le
  have hηγ : η ≤ γ := by
    have hh : ε' ≤ γ := min_le_right _ _
    linarith
  refine ⟨η,hη,hη1,hηc,hηM,hηε,?_⟩
  intro t e p ht hp hpot he
  obtain ⟨htlo,hthi,hdense,hpen,hedge,hclose⟩ := hnumeric t e p ht hp hpot he
  have hψt : γ < ψ t := hρψ (by simpa only [Real.dist_eq] using hclose)
  have hdense' : (c-ε)*t^α ≤ e := by
    have hh := mul_le_mul_of_nonneg_right (show c-ε ≤ c-ε' by linarith)
      (Real.rpow_nonneg ht α)
    exact hh.trans hdense
  refine ⟨htlo,hthi,hdense',hpen,hedge,?_⟩
  dsimp [ψ] at hψt
  linarith

#print axioms selection_errors_window
#print axioms selection_errors_sharp
end Erdos713SharpNumericPenaltySelection
