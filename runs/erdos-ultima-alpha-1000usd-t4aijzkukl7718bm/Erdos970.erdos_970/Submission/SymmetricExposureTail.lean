import Submission.EssentialCoverProbability

/-! Quantitative exponential control of the factorial elementary-symmetric
exposure bound when all but a small core have reciprocal sum at most one half.
The Jacobsthal input is explicit and can be supplied by existing polynomial
bounds. No quadratic worst-case conclusion is asserted. -/
namespace Erdos970.GapAverages
open Finset Real

lemma symmetric_generating_bound (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ j * (∑ Q ∈ P.powersetCard j, ∏ p ∈ Q, w p) ≤ ∏ p ∈ P, (1 + x * w p) := by
  rw [mul_sum, prod_one_add]
  calc
    _ = ∑ Q ∈ P.powersetCard j, ∏ p ∈ Q, x * w p := by
      apply sum_congr rfl
      intro Q hQ
      rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hQ).2]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro Q hQ
        exact mem_powerset.mpr (mem_powersetCard.mp hQ).1
      · intro Q hQ hnot
        exact prod_nonneg (fun p hp => mul_nonneg hx (hw p (mem_powerset.mp hQ hp)))

lemma generating_core_tail_bound (P S : Finset ℕ) (hS : S ⊆ P)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (x : ℝ) (hx : 0 ≤ x) (hhalf : (∑ p ∈ P \ S, w p) ≤ 1 / 2) :
    (∏ p ∈ P, (1 + x * w p)) ≤ (1 + x) ^ S.card * exp (x / 2) := by
  have hcore : (∏ p ∈ S, (1 + x * w p)) ≤ (1 + x) ^ S.card := by
    rw [← prod_const]
    apply prod_le_prod
    · intro p hp
      exact add_nonneg (by norm_num) (mul_nonneg hx (hw p (hS hp)).1)
    · intro p hp
      have hh := mul_le_mul_of_nonneg_left (hw p (hS hp)).2 hx
      linarith
  have htail : (∏ p ∈ P \ S, (1 + x * w p)) ≤ exp (x / 2) := by
    calc
      _ ≤ ∏ p ∈ P \ S, exp (x * w p) := by
        apply prod_le_prod
        · intro p hp
          exact add_nonneg (by norm_num) (mul_nonneg hx (hw p (mem_sdiff.mp hp).1).1)
        · intro p hp
          linarith only [add_one_le_exp (x * w p)]
      _ = exp (x * ∑ p ∈ P \ S, w p) := by rw [← exp_sum, mul_sum]
      _ ≤ _ := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hhalf hx])
  have he := prod_sdiff (s₁ := S) (s₂ := P) hS (f := fun p => 1 + x * w p)
  rw [← he, mul_comm]
  exact mul_le_mul hcore htail
    (prod_nonneg (fun p hp => add_nonneg (by norm_num)
      (mul_nonneg hx (hw p (mem_sdiff.mp hp).1).1))) (by positivity)

/-- An elementary factorial saving, with a deliberately generous constant. -/
lemma factorial_two_mul_exp_le (n : ℕ) :
    ((2 * n).factorial : ℝ) * exp (2 * (n : ℝ)) ≤
      (4 * (n : ℝ)) ^ (2 * n) * exp (-(n : ℝ) / 16) := by
  have hfac : ((2 * n).factorial : ℝ) ≤ (2 * (n : ℝ) ^ 2) ^ n := by
    have hh := (Nat.factorial_two_mul_le n).trans
      (Nat.mul_le_mul_left ((2 * n) ^ n) (Nat.factorial_le_pow n))
    have hh' : ((2 * n).factorial : ℝ) ≤ (2 * (n : ℝ)) ^ n * (n : ℝ) ^ n := by
      exact_mod_cast hh
    simpa only [← mul_pow, show (2 * (n : ℝ)) * n = 2 * (n : ℝ) ^ 2 by ring] using hh'
  have he : exp (2 : ℝ) ≤ 8 * exp (-(1 : ℝ) / 16) := by
    have hl : (2 : ℝ) ≤ 3 * log 2 - 1 / 16 := by linarith only [log_two_gt_d9]
    have hh := exp_le_exp.mpr hl
    have hlog : exp (3 * log 2) = (8 : ℝ) := by
      change exp ((3 : ℕ) * log 2) = 8
      rw [exp_nat_mul, exp_log (by norm_num)]
      norm_num
    rw [exp_sub, hlog] at hh
    rw [neg_div, exp_neg, ← div_eq_mul_inv]
    exact hh
  have hbase : 2 * (n : ℝ) ^ 2 * exp 2 ≤
      16 * (n : ℝ) ^ 2 * exp (-(1 : ℝ) / 16) := by
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)]
  have hden : (4 * (n : ℝ)) ^ (2 * n) = (16 * (n : ℝ) ^ 2) ^ n := by
    rw [pow_mul]
    congr 1
    ring
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) ^ n * exp (2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hfac (exp_pos _).le
    _ = (2 * (n : ℝ) ^ 2 * exp 2) ^ n := by
      simp only [mul_pow, ← exp_nat_mul]
      congr 2
      ring
    _ ≤ (16 * (n : ℝ) ^ 2 * exp (-(1 : ℝ) / 16)) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    _ = _ := by
      rw [hden, mul_pow, ← exp_nat_mul]
      congr 2
      ring

/-- A bound for 2n-1 primes gives exponential phase-tail decay, with an
explicit penalty depending on the retained small-prime core. -/
theorem coveredFraction_le_core_exponential (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (m n : ℕ) (hn : 0 < n)
    (hb : IsJacobsthalBound (2 * n - 1) m)
    (hhalf : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ 1 / 2) :
    coveredFraction P m ≤
      exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ)) - (n : ℝ) / 16) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨by positivity, inv_le_one_of_one_le₀ hp1⟩
  have he := symmetric_generating_bound P (fun p => (p : ℝ)⁻¹)
    (fun p hp => (hw p hp).1) (2 * n) (4 * n) (by positivity)
  have hg := generating_core_tail_bound P S hS (fun p => (p : ℝ)⁻¹) hw (4 * n) (by positivity) hhalf
  have hfac := factorial_two_mul_exp_le n
  have hc := coveredFraction_le_factorial_symmetric P hP m (2 * n) hb
  have hpos : 0 < (4 * (n : ℝ)) ^ (2 * n) := by positivity
  have hcore : 0 ≤ (1 + 4 * (n : ℝ)) ^ S.card := by positivity
  have hbound : (4 * (n : ℝ)) ^ (2 * n) * coveredFraction P m ≤
      (4 * (n : ℝ)) ^ (2 * n) *
        ((1 + 4 * (n : ℝ)) ^ S.card * exp (-(n : ℝ) / 16)) := by
    have ha := mul_le_mul_of_nonneg_left hc hpos.le
    have hb' := mul_le_mul_of_nonneg_left (he.trans hg) (Nat.cast_nonneg (2 * n).factorial)
    have hd := mul_le_mul_of_nonneg_left hfac hcore
    norm_num only [show 4 * (n : ℝ) / 2 = 2 * (n : ℝ) by ring] at hb'
    nlinarith only [ha, hb', hd]
  have hh := (mul_le_mul_iff_right₀ hpos).mp hbound
  apply hh.trans_eq
  have hpow : (1 + 4 * (n : ℝ)) ^ S.card =
      exp ((S.card : ℝ) * log (1 + 4 * (n : ℝ))) := by
    rw [exp_nat_mul, exp_log (by positivity)]
  rw [hpow, ← exp_add]
  congr 1
  ring

#print axioms factorial_two_mul_exp_le
#print axioms coveredFraction_le_core_exponential
end Erdos970.GapAverages
