import Submission.RetentionRows

/-! Count-dependent retention coefficients. These are auxiliary lemmas, not a
proof of the odd covering conjecture. A decreasing cap is permitted only if it
stays constant on the zero-loss part of the count interval. -/
namespace Erdos7AdaptiveRetentionRows
open Erdos7RetentionRows
set_option maxHeartbeats 1000000

lemma live_baseline_le (p c k : ℝ) :
    1-liveLoss p c k-c/p ≤ c*(1-k/(p-1)-1/p) := by
  have h := le_max_left (1-c+c*k/(p-1)) (0 : ℝ)
  dsimp [liveLoss]
  calc
    _ ≤ 1-(1-c+c*k/(p-1))-c/p := by linarith
    _ = _ := by ring

lemma live_baseline_eq_of_active (p c k : ℝ)
    (h : c*(1-k/(p-1)) ≤ 1) :
    1-liveLoss p c k-c/p = c*(1-k/(p-1)-1/p) := by
  have hh : 0 ≤ 1-c+c*k/(p-1) := by
    calc
      0 ≤ 1-c*(1-k/(p-1)) := sub_nonneg.mpr h
      _ = _ := by ring
  rw [liveLoss, max_eq_left hh]
  ring

/-- The baseline coefficient remains ordered when the cap decreases in the
positive-loss region. A cap drop in the zero-loss region is NOT allowed by
this lemma. -/
theorem live_baseline_adaptive_order (p ck cl k l : ℝ)
    (hp : 1 < p) (hcl : 0 ≤ cl) (hcap : cl ≤ ck) (hkl : k ≤ l)
    (hl : l ≤ (p-1)*(1-1/p))
    (hdrop : ck=cl ∨ ck*(1-k/(p-1)) ≤ 1) :
    1-liveLoss p cl l-cl/p ≤ 1-liveLoss p ck k-ck/p := by
  have hck : 0 ≤ ck := hcl.trans hcap
  rcases hdrop with he | ha
  · subst cl
    have hm := liveLoss_monotone p ck hp hck hkl
    linarith
  · rw [live_baseline_eq_of_active p ck k ha]
    have hq : 0 < p-1 := by linarith
    have hdiv : l/(p-1) ≤ 1-1/p := (div_le_iff₀ hq).mpr (by
      simpa only [mul_comm] using hl)
    have hA : 0 ≤ 1-l/(p-1)-1/p := by linarith
    have hB : 1-l/(p-1)-1/p ≤ 1-k/(p-1)-1/p := by
      have hh := div_le_div_of_nonneg_right hkl hq.le
      linarith
    calc
      _ ≤ cl*(1-l/(p-1)-1/p) := live_baseline_le p cl l
      _ ≤ ck*(1-l/(p-1)-1/p) := mul_le_mul_of_nonneg_right hcap hA
      _ ≤ ck*(1-k/(p-1)-1/p) := mul_le_mul_of_nonneg_left hB hck

/-- Ordered rows for an arbitrary finite count domain. The cap may be a
step function, provided every decrease starts after its live loss is active. -/
theorem adaptive_rows_antitoneOn (p K : ℝ) (T : Set ℝ) (c : ℝ → ℝ)
    (hp : 1 < p) (hK : K ≤ (p-1)*(1-1/p))
    (hc0 : ∀ k ∈ T, 0 ≤ c k) (hcp : ∀ k ∈ T, c k ≤ p)
    (hc : AntitoneOn c T)
    (hdrop : ∀ k ∈ T, ∀ l ∈ T, k ≤ l → l ≤ K →
      c k=c l ∨ c k*(1-k/(p-1)) ≤ 1) :
    AntitoneOn (fun k => baseline p (c k) K k) T ∧
    AntitoneOn (fun k => density (c k) K k) T := by
  constructor
  · intro k hk l hl hkl
    by_cases hlK : l ≤ K
    · simp only [baseline, if_pos hlK, if_pos (hkl.trans hlK)]
      exact live_baseline_adaptive_order p (c k) (c l) k l hp
        (hc0 l hl) (hc hk hl hkl) hkl (hlK.trans hK)
        (hdrop k hk l hl hkl hlK)
    · simp only [baseline, if_neg hlK]
      exact baseline_nonneg p (c k) K k hp (hc0 k hk) (hcp k hk) hK
  · intro k hk l hl hkl
    by_cases hlK : l ≤ K
    · simp only [density, if_pos hlK, if_pos (hkl.trans hlK)]
      exact hc hk hl hkl
    · simp only [density, if_neg hlK]
      exact density_nonneg (c k) K k (hc0 k hk)

/-- A useful sufficient condition: keep the cap on a plateau, then let it
 decrease only after the plateau's zero-loss threshold. For pairs straddling
 the threshold, the proof passes through the threshold rather than claiming
 the left endpoint already has positive loss. -/
theorem plateau_baseline_antitoneOn (p K t c₀ : ℝ) (T : Set ℝ) (c : ℝ → ℝ)
    (hp : 1 < p) (hc₀ : 0 ≤ c₀) (hK : K ≤ (p-1)*(1-1/p))
    (hc0 : ∀ k ∈ T, 0 ≤ c k) (hcp : ∀ k ∈ T, c k ≤ p)
    (hc : AntitoneOn c T) (hupper : ∀ k ∈ T, c k ≤ c₀)
    (hplateau : ∀ k ∈ T, k ≤ t → c k=c₀)
    (hthreshold : c₀*(1-t/(p-1)) ≤ 1) :
    AntitoneOn (fun k => baseline p (c k) K k) T := by
  intro k hk l hl hkl
  by_cases hlK : l ≤ K
  · simp only [baseline, if_pos hlK, if_pos (hkl.trans hlK)]
    by_cases hlt : l ≤ t
    · rw [hplateau k hk (hkl.trans hlt), hplateau l hl hlt]
      have hh := liveLoss_monotone p c₀ hp hc₀ hkl
      linarith
    by_cases hkt : k ≤ t
    · rw [hplateau k hk hkt]
      have htl : t ≤ l := le_of_lt (lt_of_not_ge hlt)
      calc
        _ ≤ 1-liveLoss p c₀ t-c₀/p :=
          live_baseline_adaptive_order p c₀ (c l) t l hp (hc0 l hl)
            (hupper l hl) htl (hlK.trans hK) (Or.inr hthreshold)
        _ ≤ _ := by
          have hh := liveLoss_monotone p c₀ hp hc₀ hkt
          linarith
    · have hq : 0 < p-1 := by linarith
      have ht : t ≤ k := le_of_lt (lt_of_not_ge hkt)
      have hdiv := div_le_div_of_nonneg_right ht hq.le
      have hkcut : k/(p-1) ≤ 1-1/p := (div_le_iff₀ hq).mpr (by
        simpa only [mul_comm] using (hkl.trans (hlK.trans hK)))
      have hkp : 0 ≤ 1-k/(p-1) := by
        have hh : 0 ≤ 1/p := by positivity
        linarith
      have hactive : c k*(1-k/(p-1)) ≤ 1 := by
        calc
          _ ≤ c₀*(1-k/(p-1)) := mul_le_mul_of_nonneg_right (hupper k hk) hkp
          _ ≤ c₀*(1-t/(p-1)) := mul_le_mul_of_nonneg_left (by linarith) hc₀
          _ ≤ 1 := hthreshold
      exact live_baseline_adaptive_order p (c k) (c l) k l hp
        (hc0 l hl) (hc hk hl hkl) hkl (hlK.trans hK) (Or.inr hactive)
  · simp only [baseline, if_neg hlK]
    exact baseline_nonneg p (c k) K k hp (hc0 k hk) (hcp k hk) hK

#print axioms plateau_baseline_antitoneOn
#print axioms adaptive_rows_antitoneOn
end Erdos7AdaptiveRetentionRows
