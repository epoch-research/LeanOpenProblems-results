import Submission.PrimeBandDensity
import Submission.LogarithmicSignedReduction

/-! Every positive level of the locally normalized prime logarithm has
arbitrarily small surrounding upper natural density. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma normalizedPrimeLog_self_band (n : ℕ) (hn : 1 < n) (a δ : ℝ)
    (h : |normalizedPrimeLog n n-a| ≤ δ) : logPrimeBandEvent (a-δ) (a+δ) n := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hp : (0 : ℝ)<Nat.maxPrimeFac n := by exact_mod_cast maxPrimeFac_pos_of_pos n (by omega)
  have hlo := (abs_le.mp h).1
  have hup := (abs_le.mp h).2
  have h₁ : a-δ ≤ normalizedPrimeLog n n := by linarith
  have h₂ : normalizedPrimeLog n n ≤ a+δ := by linarith
  rw [normalizedPrimeLog,le_div_iff₀ hl] at h₁
  rw [normalizedPrimeLog,div_le_iff₀ hl] at h₂
  refine ⟨hn,?_,?_⟩
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hnR _) hp).mp
    simpa only [Real.log_rpow hnR,primeLog] using h₁
  · apply (Real.log_le_log_iff hp (Real.rpow_pos_of_pos hnR _)).mp
    simpa only [Real.log_rpow hnR,primeLog] using h₂

/-- A positive level has no atom in upper natural density. The width is
chosen before the averaging endpoint, and it is positive. -/
theorem prime_log_level_nonatomic (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ N : ℕ in atTop,
      (((range N).filter (fun n => 1<n ∧ |normalizedPrimeLog n n-a| ≤ δ)).card : ℝ)/N ≤ ε := by
  classical
  let r := min (1/4 : ℝ) (ε/512)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hr₁ : r ≤ 1/4 := min_le_left _ _
  have hrε : r ≤ ε/512 := min_le_right _ _
  let u := a-a*r
  let v := a+a*r
  let t := 1-r
  have hu : 0 < u := by dsimp [u]; nlinarith
  have huv : u ≤ v := by dsimp [u,v]; nlinarith
  have ht : 0 < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have htu : 0 < t*u := mul_pos ht hu
  have hden : a/4 ≤ t*u := by
    have h₁ : a/2 ≤ u := by dsimp [u]; nlinarith
    have h₂ : 1/2 ≤ t := by dsimp [t]; linarith
    nlinarith
  have hnum : v-t*u ≤ 3*a*r := by
    have hsq : 0 ≤ a*r^2 := mul_nonneg ha.le (sq_nonneg r)
    dsimp [v,t,u]
    nlinarith
  have hb : 8*(v-t*u)/(t*u) ≤ 128*r := by
    apply (div_le_iff₀ htu).mpr
    have hm := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ)≤128*r)
    nlinarith
  obtain hbound := logPrimeBandEvent_eventually_ratio_le u v t hu huv ht ht1 (ε/2) (by positivity)
  refine ⟨a*r,mul_pos ha hr,?_⟩
  filter_upwards [hbound] with N hbound
  have hsub : (range N).filter (fun n => 1<n ∧ |normalizedPrimeLog n n-a| ≤ a*r) ⊆
      (range N).filter (logPrimeBandEvent u v) := by
    intro n hn
    obtain ⟨hnN,hn1,hnear⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN,normalizedPrimeLog_self_band n hn1 a (a*r) hnear⟩
  have hc := div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (Nat.cast_nonneg (α := ℝ) N)
  linarith

#print axioms prime_log_level_nonatomic
end Erdos371
