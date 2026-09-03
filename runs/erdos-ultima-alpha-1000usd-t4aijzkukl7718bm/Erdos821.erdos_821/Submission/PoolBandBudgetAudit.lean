import FormalConjecturesUtil

/-!
# A lower bound for the retained-pool band budget

This audits a specific nonnegative upper-sieve majorant, not the actual
number of rejected primes. It is NOT a disproof of Erdős 821. Finer bands
alone cannot force an arbitrary-root cutoff at the same two levels.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 2000000

noncomputable def poolBandBudget (x A : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, A i*(1/x i-1/x (i+1))

lemma log_ratio_le_band_budget (u v ell A : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hell : 0 < ell) (hA : v/ell ≤ A) :
    Real.log (v/u)/ell ≤ A*(1/u-1/v) := by
  have hv : 0 < v := hu.trans_le huv
  have hΔ : 0 ≤ 1/u-1/v := sub_nonneg.mpr (one_div_le_one_div_of_le hu huv)
  calc
    _ ≤ (v/u-1)/ell := div_le_div_of_nonneg_right
      (Real.log_le_sub_one_of_pos (div_pos hv hu)) hell.le
    _ = (v/ell)*(1/u-1/v) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hΔ

/-- Each endpoint coefficient y/lambda dominates the logarithmic
increment. This lower bound holds for every finite monotone partition. -/
theorem poolBandBudget_ge_log_ratio (x A : ℕ → ℝ) (ell : ℝ) (hell : 0 < ell)
    (hx : ∀ i, 0 < x i) (hmono : Monotone x) (n : ℕ)
    (hA : ∀ i ∈ range n, x (i+1)/ell ≤ A i) :
    Real.log (x n/x 0)/ell ≤ poolBandBudget x A n := by
  induction n with
  | zero => simp [poolBandBudget,(hx 0).ne']
  | succ n ih =>
    have hi := ih (fun i hi => hA i (mem_range.mpr (by have := mem_range.mp hi; omega)))
    have hn := log_ratio_le_band_budget (x n) (x (n+1)) ell (A n)
      (hx n) (hmono (by omega)) hell (hA n (mem_range.mpr (by omega)))
    have he : Real.log (x (n+1)/x 0)/ell =
        Real.log (x n/x 0)/ell+Real.log (x (n+1)/x n)/ell := by
      rw [Real.log_div (hx (n+1)).ne' (hx 0).ne',
        Real.log_div (hx n).ne' (hx 0).ne',Real.log_div (hx (n+1)).ne' (hx n).ne']
      ring
    rw [he]
    apply (_root_.add_le_add hi hn).trans_eq
    simp only [poolBandBudget,sum_range_succ]

/-- A successful budget at fixed sieve exponent L and remaining endpoint
at least tau forces a positive lower bound on the proposed smooth cutoff. -/
theorem poolBandBudget_forces_cutoff (x A : ℕ → ℝ) (ell L τ : ℝ)
    (hell : 0 < ell) (hlevel : ell ≤ L)
    (hx : ∀ i, 0 < x i) (hmono : Monotone x) (n : ℕ)
    (hA : ∀ i ∈ range n, x (i+1)/ell ≤ A i)
    (hend : τ ≤ x n) (hbudget : poolBandBudget x A n < 1) :
    τ*Real.exp (-L) < x 0 := by
  have hb := (poolBandBudget_ge_log_ratio x A ell hell hx hmono n hA).trans_lt hbudget
  have hlog : Real.log (x n/x 0) < L := by
    have h := (div_lt_iff₀ hell).mp hb
    linarith
  have he := (Real.log_lt_iff_lt_exp (div_pos (hx n) (hx 0))).mp hlog
  have hm := (div_lt_iff₀ (hx 0)).mp he
  have hbound : τ/Real.exp L < x 0 := (div_lt_iff₀ (Real.exp_pos L)).mpr (by
    simpa only [mul_comm] using hend.trans_lt hm)
  simpa only [Real.exp_neg,div_eq_mul_inv] using hbound

/-- At an initial half-level and successor sieve exponent at most 1/4,
no finite band refinement can certify a cutoff below exp(-1/4)/2 through
this particular budget. The actual arithmetic count is not bounded below. -/
theorem half_level_pool_budget_cutoff (x A : ℕ → ℝ)
    (hx : ∀ i, 0 < x i) (hmono : Monotone x) (n : ℕ)
    (hA : ∀ i ∈ range n, 4*x (i+1) ≤ A i)
    (hend : (1/2 : ℝ) ≤ x n) (hbudget : poolBandBudget x A n < 1) :
    Real.exp (-1/4 : ℝ)/2 < x 0 := by
  have h := poolBandBudget_forces_cutoff x A (1/4) (1/4) (1/2)
    (by norm_num) le_rfl hx hmono n
    (fun i hi => by convert hA i hi using 1; ring)
    hend hbudget
  simpa only [neg_div,div_eq_mul_inv,mul_comm,one_mul,neg_mul] using h

end Erdos821.AnalyticSieve
