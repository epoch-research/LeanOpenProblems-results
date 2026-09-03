import Submission.PrimeSetMertens

/-! Reciprocal mass above the cardinality scale. The upper cutoff is
k log k rather than a fixed power of k, and the prime-sum error is explicit. -/
namespace Erdos970.WeightedMertens
open Finset Real Filter
set_option maxHeartbeats 1200000

noncomputable def budgetScaleTail (x : ℝ) : ℝ :=
  (log (log x)+2*(boundConstant+1)+1)/log x

lemma budgetScaleTail_nonneg (x : ℝ) (hx : 1 ≤ log x) : 0 ≤ budgetScaleTail x := by
  have hlog : 0 ≤ log (log x) := log_nonneg hx
  have := boundConstant_pos
  unfold budgetScaleTail
  positivity

/-- For at most k primes above k, the reciprocal mass is
(log log k + O(1))/log k, with one absolute explicit constant. -/
theorem prime_set_tail_at_budget (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : 2 ≤ k) (hlog : 1 ≤ log (k : ℝ)) (hcard : P.card ≤ k) :
    (∑ p ∈ P.filter (fun p : ℕ => k < p), 1/(p : ℝ)) ≤ budgetScaleTail k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hl0 : 0 < log (k : ℝ) := by linarith only [hlog]
  have ha : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hab : (k : ℝ) ≤ (k : ℝ)*log (k : ℝ) := by nlinarith only [hlog,hk0]
  have hh := prime_set_tail P hP ha hab
  have hf : P.filter (fun p : ℕ => (k : ℝ) < (p : ℝ)) = P.filter (fun p : ℕ => k < p) := by
    ext p
    simp only [mem_filter,Nat.cast_lt]
  rw [hf] at hh
  have hll : 0 ≤ log (log (k : ℝ)) := log_nonneg hlog
  have hid : log ((k : ℝ)*log (k : ℝ)) = log (k : ℝ)+log (log (k : ℝ)) :=
    log_mul hk0.ne' hl0.ne'
  have hratio : 0 < log ((k : ℝ)*log (k : ℝ))/log (k : ℝ) := by
    rw [hid]
    positivity
  have hdiff : log (log ((k : ℝ)*log (k : ℝ)))-log (log (k : ℝ)) ≤
      log (log (k : ℝ))/log (k : ℝ) := by
    rw [← log_div (by rw [hid]; positivity) hl0.ne']
    apply (log_le_sub_one_of_pos hratio).trans_eq
    rw [hid]
    field_simp <;> ring
  have hc : (P.card : ℝ)/((k : ℝ)*log (k : ℝ)) ≤ 1/log (k : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos hk0 hl0) hl0).mpr
    have hkr : (P.card : ℝ) ≤ k := by exact_mod_cast hcard
    nlinarith only [mul_le_mul_of_nonneg_right hkr hl0.le]
  simp only [one_div] at hh ⊢
  unfold budgetScaleTail
  have he : (log (log (k : ℝ))+2*(boundConstant+1)+1)/log (k : ℝ) =
      log (log (k : ℝ))/log (k : ℝ)+2*(boundConstant+1)/log (k : ℝ)+1/log (k : ℝ) := by ring
  rw [he]
  linarith only [hh,hdiff,hc]

lemma budgetScaleTail_tendsto_zero : Tendsto budgetScaleTail atTop (nhds 0) := by
  have hlog : Tendsto log atTop atTop := tendsto_log_atTop
  have hmain : Tendsto (fun x : ℝ => log (log x)/log x) atTop (nhds 0) :=
    by
      have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
      simp only [rpow_one] at hh
      exact hh.comp hlog
  have hconstant : Tendsto (fun x : ℝ => (2*(boundConstant+1)+1)/log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hh := hmain.add hconstant
  norm_num only [zero_add] at hh
  convert hh using 1
  funext x
  unfold budgetScaleTail
  ring

#print axioms prime_set_tail_at_budget
#print axioms budgetScaleTail_tendsto_zero
end Erdos970.WeightedMertens
