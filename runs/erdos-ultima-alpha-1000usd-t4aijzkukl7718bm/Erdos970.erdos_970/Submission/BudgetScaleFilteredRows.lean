import Submission.BudgetScalePrimeTail
import Submission.CoreFilteredSelberg

/-! A logarithmically vanishing budget for the actual large-prime deletion
rows at quadratic length. All row rounding and upper-sieve costs are charged. -/
namespace Erdos970.GapAverages
open Finset Real Filter WeightedMertens
set_option maxHeartbeats 1800000

lemma filteredDeletionBudget_le_constant_rows (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m R : ℕ) (hR : 0 < R)
    (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q) (r : Phase P) :
    filteredDeletionBudget P Q hQP m r ≤
      (m : ℝ)/log (R+1)*(∑ p ∈ P\Q, 1/(p : ℝ))+
        ((P\Q).card : ℝ)*(1/log (R+1)+(exp 2*R/log (R+1))^2) := by
  classical
  have hh := filteredDeletionBudget_le_sharp_rows P Q hQP hP m (fun _ => R)
    (fun _ _ => hR) (fun _ _ => hfull) r
  apply hh.trans_eq
  rw [sum_coe_sort P (fun p : ℕ => if p ∈ Q then 0 else
    ((m : ℝ)/p+1)/log (R+1)+(exp 2*R/log (R+1))^2)]
  have hf := sum_filter (s := P) (fun p : ℕ => p ∉ Q)
    (fun p : ℕ => ((m : ℝ)/p+1)/log (R+1)+(exp 2*R/log (R+1))^2)
  simp only [ite_not] at hf
  rw [← hf,filter_notMem_eq_sdiff]
  rw [mul_sum]
  have he (p : ℕ) : ((m : ℝ)/p+1)/log (R+1)+(exp 2*R/log (R+1))^2 =
      (m : ℝ)/log (R+1)*(1/(p : ℝ))+(1/log (R+1)+(exp 2*R/log (R+1))^2) := by ring
  simp_rw [he]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul]
  ring

/-- Finite quantitative bound, uniform in all phases and without an upper
bound on any individual tail prime. -/
theorem filteredDeletionBudget_le_budget_scale (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (k m R : ℕ) (hk : 2 ≤ k) (hlk : 1 ≤ log (k : ℝ))
    (hcard : (P\Q).card ≤ k) (hlarge : ∀ p ∈ P\Q, k < p)
    (hR : 0 < R) (hfull : ∀ a, a.Prime → a ≤ R → a ∈ Q) (r : Phase P) :
    filteredDeletionBudget P Q hQP m r ≤
      (m : ℝ)/log (R+1)*budgetScaleTail k+
        (k : ℝ)*(1/log (R+1)+(exp 2*R/log (R+1))^2) := by
  have ht := prime_set_tail_at_budget (P\Q) (fun p hp => hP p (mem_sdiff.mp hp).1) k hk hlk hcard
  rw [filter_eq_self.mpr hlarge] at ht
  have hl : 0 < log (R+1 : ℝ) := log_pos (by exact_mod_cast (show 1 < R+1 by omega))
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (m : ℝ)/log (R+1)))
    (mul_le_mul_of_nonneg_right (show ((P\Q).card : ℝ) ≤ k by exact_mod_cast hcard)
      (show 0 ≤ 1/log (R+1)+(exp 2*R/log (R+1))^2 by positivity))
  exact (filteredDeletionBudget_le_constant_rows P Q hQP hP m R hR hfull r).trans hh

lemma fourth_row_algebra (x l L M a B : ℝ) (hx : 0 < x) (hl : 1 ≤ l)
    (hlL : l ≤ L) (hM : x^8 ≤ M) (ha : 0 ≤ a) (hB : 0 ≤ B) :
    M/L*B+x^4*(1/L+(a*x/L)^2) ≤
      (B+1/x^4+a^2/x^2)*(M/l) := by
  have hl0 : 0 < l := by linarith only [hl]
  have hL0 : 0 < L := hl0.trans_le hlL
  have hM0 : 0 ≤ M := (pow_nonneg hx.le _).trans hM
  have hmain := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hM0 hl0 hlL) hB
  have hi := one_div_le_one_div_of_le hl0 hlL
  have hsq : 1/L^2 ≤ 1/l := by
    apply one_div_le_one_div_of_le hl0
    nlinarith only [hl,hlL]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (a*x)^2 by positivity)
  have hcost : x^4*(1/L+(a*x/L)^2) ≤ x^4/l*(1+a^2*x^2) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hi hm) (pow_nonneg hx.le 4)
    convert hh using 1 <;> ring
  have hscale := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hM hl0.le)
    (show 0 ≤ 1/x^4+a^2/x^2 by positivity)
  have he : (1/x^4+a^2/x^2)*(x^8/l)=x^4/l*(1+a^2*x^2) := by field_simp <;> ring
  rw [he] at hscale
  have hh := add_le_add hmain (hcost.trans hscale)
  convert hh using 1 <;> ring

noncomputable def fourthScaleDeletionRatio (t : ℝ) : ℝ :=
  budgetScaleTail (t^4)+1/t^4+(exp 2)^2/t^2

lemma fourthScaleDeletionRatio_tendsto_zero :
    Tendsto fourthScaleDeletionRatio atTop (nhds 0) := by
  have ht4 : Tendsto (fun t : ℝ => t^4) atTop atTop := tendsto_pow_atTop (by norm_num)
  have ht2 : Tendsto (fun t : ℝ => t^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hh := ((budgetScaleTail_tendsto_zero.comp ht4).add (ht4.const_div_atTop 1)).add
    (ht2.const_div_atTop ((exp 2)^2))
  simpa only [zero_add,fourthScaleDeletionRatio] using hh

/-- At cardinality t^4 and interval length at least t^8, all selected tail
primes larger than t^4 together remove only a vanishing multiple of m/log t.
The core must contain the primes through t; no lower count is assumed. -/
theorem filteredDeletionBudget_le_fourth_scale (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (t m : ℕ) (ht : 3 ≤ t) (hm : t^8 ≤ m)
    (hcard : (P\Q).card ≤ t^4) (hlarge : ∀ p ∈ P\Q, t^4 < p)
    (hfull : ∀ a, a.Prime → a ≤ t → a ∈ Q) (r : Phase P) :
    filteredDeletionBudget P Q hQP m r ≤ fourthScaleDeletionRatio t*((m : ℝ)/log t) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hlt : 1 ≤ log (t : ℝ) := (le_log_iff_exp_le ht0).mpr (exp_one_lt_three.le.trans ht3)
  have ht4 : 2 ≤ t^4 := by
    have hh := Nat.pow_le_pow_left (show 2 ≤ t by omega) 4
    norm_num at hh
    omega
  have hl4 : 1 ≤ log (t^4 : ℕ) := by
    rw [Nat.cast_pow,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlt]
  have hh := filteredDeletionBudget_le_budget_scale P Q hQP hP (t^4) m t ht4 hl4
    hcard hlarge (by omega) hfull r
  have halg := fourth_row_algebra (t : ℝ) (log t) (log (t+1 : ℝ)) (m : ℝ) (exp 2)
    (budgetScaleTail (t^4)) ht0 hlt (log_le_log ht0 (by linarith)) (by exact_mod_cast hm)
    (exp_pos 2).le (budgetScaleTail_nonneg _ (by simpa only [Nat.cast_pow] using hl4))
  simp only [Nat.cast_pow] at hh
  exact hh.trans halg

/-- The vanishing coefficient is uniform over all allowed finite prime sets,
all phases, and every interval length above the quadratic scale. -/
theorem eventually_filteredDeletionBudget_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, ∀ P Q : Finset ℕ, ∀ hQP : Q ⊆ P,
      (∀ p ∈ P, p.Prime) → ∀ m : ℕ, t^8 ≤ m →
      (P\Q).card ≤ t^4 → (∀ p ∈ P\Q, t^4 < p) →
      (∀ a, a.Prime → a ≤ t → a ∈ Q) → ∀ r : Phase P,
      filteredDeletionBudget P Q hQP m r ≤ ε*((m : ℝ)/log t) := by
  have he := (fourthScaleDeletionRatio_tendsto_zero.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_lt_nhds hε)
  filter_upwards [he,eventually_ge_atTop 3] with t ht h3
  intro P Q hQP hP m hm hcard hlarge hfull r
  apply (filteredDeletionBudget_le_fourth_scale P Q hQP hP t m h3 hm hcard hlarge hfull r).trans
  exact mul_le_mul_of_nonneg_right ht.le
    (div_nonneg (Nat.cast_nonneg m) (log_natCast_nonneg t))

#print axioms filteredDeletionBudget_le_fourth_scale
#print axioms eventually_filteredDeletionBudget_small
end Erdos970.GapAverages
