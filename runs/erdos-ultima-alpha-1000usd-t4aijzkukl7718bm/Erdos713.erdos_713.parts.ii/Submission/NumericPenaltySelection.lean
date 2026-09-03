import FormalConjecturesUtil
import Submission.PowerPotentialStability

/-! Normalized estimates for selecting degree-penalized graph witnesses. -/
open Filter
open scoped Topology
namespace Erdos713NumericPenaltySelection
open Erdos713PowerPotential
set_option maxHeartbeats 1000000

/-- All constants are fixed before the normalized candidate order and
objective are chosen. Here p represents the nonnegative energy penalty. -/
theorem selection_errors_strong {α c ε : ℝ} (ha : 0 < α) (ha2 : α < 2) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ η < c ∧ η ≤ c*(1-α/2)/20 ∧ 4*η ≤ ε ∧
      ∀ t e p : ℝ, 0 ≤ t → 0 ≤ p →
        c*(1-α/2)-2*η ≤ e-p-c*α/2*t^2 → e ≤ (c+η)*t^α+η →
        1/2 < t ∧ t < 2 ∧ (c-ε)*t^α ≤ e ∧ p ≤ 7*η ∧ e ≤ 5*(c+1) := by
  let M := c*(1-α/2)
  have hM : 0 < M := mul_pos hc (by linarith)
  have ha0 : 0 ≤ α := ha.le
  let ψ : ℝ → ℝ := fun t => (c-ε)*t^α-c*α/2*t^2
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop (disch := positivity)
  have hψ1 : ψ 1 = M-ε := by dsimp [ψ,M]; simp only [Real.one_rpow,one_pow]; ring
  have hneigh : ∀ᶠ t : ℝ in 𝓝 1, ψ t < M-ε/2 :=
    hψ.continuousAt.tendsto.eventually_lt_const (by rw [hψ1]; linarith)
  obtain ⟨r,hr,hrψ⟩ := Metric.eventually_nhds_iff.mp hneigh
  let r' := min r (1/2 : ℝ)
  have hr' : 0 < r' := lt_min hr (by norm_num)
  have hr'1 : r' ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨δ,hδ,_,hStable⟩ := stable_maximum ha ha2 hc hr' hr'1
  let ζ := min δ (min ε (min M (min c 1)))
  have hζ : 0 < ζ := lt_min hδ (lt_min hε (lt_min hM (lt_min hc (by norm_num))))
  have hζb : ζ ≤ δ ∧ ζ ≤ ε ∧ ζ ≤ M ∧ ζ ≤ c ∧ ζ ≤ 1 := by
    simpa only [le_min_iff] using (show ζ ≤ min δ (min ε (min M (min c 1))) from le_rfl)
  let η := ζ/100
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/4 := by dsimp [η]; linarith [hζb.2.2.2.2]
  have hηc : η < c := by dsimp [η]; linarith [hζb.2.2.2.1]
  have hηM : η ≤ M/20 := by dsimp [η]; linarith [hζb.2.2.1]
  have hηδ : 4*η ≤ δ := by dsimp [η]; linarith [hζb.1]
  have hηε : 4*η ≤ ε := by dsimp [η]; linarith [hζb.2.1]
  refine ⟨η,hη,hη1,hηc,hηM,hηε,?_⟩
  intro t e p ht hp hpot he
  have hpow0 : 0 ≤ t^α := Real.rpow_nonneg ht α
  have horder : |t-1| < r' := by
    apply hStable t ht
    have hcoef := mul_nonneg (show 0 ≤ δ-η by linarith) hpow0
    change M-δ ≤ _
    change M-2*η ≤ _ at hpot
    nlinarith only [hpot,he,hp,hcoef,hηδ,hη.le]
  have hhalf : |t-1| < 1/2 := horder.trans_le (min_le_right _ _)
  have hlow : 1/2 < t := by have hh := (abs_lt.mp hhalf).1; linarith
  have hhigh : t < 2 := by have hh := (abs_lt.mp hhalf).2; linarith
  have hpow : t^α ≤ 4 := by
    have htwo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha2.le
    have hbase := Real.rpow_le_rpow ht hhigh.le ha.le
    exact hbase.trans (by simpa only [Real.rpow_two, show (2 : ℝ)^2 = 4 by norm_num] using htwo)
  have hclose : ψ t < M-ε/2 := hrψ (by
    rw [Real.dist_eq]
    exact horder.trans_le (min_le_left _ _))
  have hdense : (c-ε)*t^α ≤ e := by
    dsimp [ψ] at hclose
    change M-2*η ≤ _ at hpot
    linarith
  have hphi : c*t^α-c*α/2*t^2 ≤ M := phi_le ha.le ha2.le hc.le ht
  have hηpow := mul_le_mul_of_nonneg_left hpow hη.le
  have hpen : p ≤ 7*η := by
    change M-2*η ≤ _ at hpot
    nlinarith only [hpot,he,hphi,hηpow]
  have hupper : e ≤ 5*(c+1) := by
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ c+η by positivity)
    nlinarith only [he,hh,hη1,hc.le]
  exact ⟨hlow,hhigh,hdense,hpen,hupper⟩

/-- The original API, with the extra smallness estimate discarded. -/
theorem selection_errors {α c ε : ℝ} (ha : 0 < α) (ha2 : α < 2) (hc : 0 < c)
    (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ η < c ∧ η ≤ c*(1-α/2)/20 ∧
      ∀ t e p : ℝ, 0 ≤ t → 0 ≤ p →
        c*(1-α/2)-2*η ≤ e-p-c*α/2*t^2 → e ≤ (c+η)*t^α+η →
        1/2 < t ∧ t < 2 ∧ (c-ε)*t^α ≤ e ∧ p ≤ 7*η ∧ e ≤ 5*(c+1) := by
  obtain ⟨η,hη,hη1,hηc,hηM,_,hs⟩ := selection_errors_strong ha ha2 hc hε
  exact ⟨η,hη,hη1,hηc,hηM,hs⟩

#print axioms selection_errors_strong
#print axioms selection_errors
end Erdos713NumericPenaltySelection
