import Submission.SymmetricExposureTail

/-! Sharpening the factorial exposure estimate permits every reciprocal tail
budget below one. These estimates do not assert the quadratic conjecture. -/
namespace Erdos970.GapAverages
open Finset Real

lemma log_factorial_upper (j : ℕ) (hj : 0 < j) :
    log (j.factorial : ℝ) ≤ (j : ℝ)*log j - j + 1 + log j/2 := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have ha := Stirling.log_stirlingSeq'_antitone (show 0 ≤ j-1 from Nat.zero_le _)
  change log (Stirling.stirlingSeq ((j-1)+1)) ≤ log (Stirling.stirlingSeq 1) at ha
  rw [Nat.sub_add_cancel hj, Stirling.log_stirlingSeq_formula,
    Stirling.stirlingSeq_one, log_div (exp_ne_zero _) (by positivity), log_exp,
    log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    log_mul (by norm_num : (2 : ℝ) ≠ 0) hjR.ne',
    log_div hjR.ne' (exp_ne_zero _), log_exp] at ha
  linarith

lemma generating_core_tail_bound_of_le (P S : Finset ℕ) (hS : S ⊆ P)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (x δ : ℝ) (hx : 0 ≤ x) (htail : (∑ p ∈ P \ S, w p) ≤ δ) :
    (∏ p ∈ P, (1+x*w p)) ≤ (1+x)^S.card * exp (x*δ) := by
  have hc : (∏ p ∈ S, (1+x*w p)) ≤ (1+x)^S.card := by
    rw [← prod_const]
    apply prod_le_prod
    · intro p hp
      exact add_nonneg (by norm_num) (mul_nonneg hx (hw p (hS hp)).1)
    · intro p hp
      have hh := mul_le_mul_of_nonneg_left (hw p (hS hp)).2 hx
      linarith
  have ht : (∏ p ∈ P \ S, (1+x*w p)) ≤ exp (x*δ) := by
    calc
      _ ≤ ∏ p ∈ P \ S, exp (x*w p) := by
        apply prod_le_prod
        · intro p hp
          exact add_nonneg (by norm_num) (mul_nonneg hx (hw p (mem_sdiff.mp hp).1).1)
        · intro p hp
          linarith only [add_one_le_exp (x*w p)]
      _ = exp (x*∑ p ∈ P \ S, w p) := by rw [← exp_sum, mul_sum]
      _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_left htail hx)
  rw [← prod_sdiff hS (f := fun p => 1+x*w p), mul_comm]
  exact mul_le_mul hc ht (prod_nonneg (fun p hp =>
    add_nonneg (by norm_num) (mul_nonneg hx (hw p (mem_sdiff.mp hp).1).1))) (by positivity)

/-- The logarithmic factorial overhead is explicit. In particular, a fixed
reciprocal budget δ<1 gives exponential decay when the core is small enough. -/
theorem coveredFraction_le_general_core (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (m j : ℕ) (hj : 0 < j)
    (hb : IsJacobsthalBound (j-1) m) (δ : ℝ) (hδ : 0 < δ)
    (htail : (∑ p ∈ P \ S, (p : ℝ)⁻¹) ≤ δ) :
    coveredFraction P m ≤ exp ((S.card : ℝ)*log (1+(j : ℝ)/δ) +
      1 + log j/2 + (j : ℝ)*log δ) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  let x := (j : ℝ)/δ
  have hx : 0 < x := div_pos hjR hδ
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1 := by
    exact ⟨by positivity, inv_le_one_of_one_le₀ (by exact_mod_cast (hP p hp).one_le)⟩
  have he := symmetric_generating_bound P (fun p => (p : ℝ)⁻¹)
    (fun p hp => (hw p hp).1) j x hx.le
  have hg := generating_core_tail_bound_of_le P S hS _ hw x δ hx.le htail
  have hc := coveredFraction_le_factorial_symmetric P hP m j hb
  have hfac : (j.factorial : ℝ) ≤ exp ((j : ℝ)*log j-j+1+log j/2) := by
    rw [← exp_log (by exact_mod_cast Nat.factorial_pos j : (0 : ℝ) < j.factorial)]
    exact exp_le_exp.mpr (log_factorial_upper j hj)
  have hpre : x^j * coveredFraction P m ≤
      exp ((j : ℝ)*log j-j+1+log j/2) * ((1+x)^S.card * exp (x*δ)) := by
    have h1 := mul_le_mul_of_nonneg_left hc (pow_nonneg hx.le j)
    have h2 := mul_le_mul_of_nonneg_left (he.trans hg) (Nat.cast_nonneg j.factorial)
    calc
      _ ≤ (j.factorial : ℝ)*((1+x)^S.card*exp (x*δ)) := by nlinarith only [h1,h2]
      _ ≤ _ := mul_le_mul_of_nonneg_right hfac (by positivity)
  have hpow : x^j = exp ((j : ℝ)*log x) := by rw [exp_nat_mul, exp_log hx]
  have hcore : (1+x)^S.card = exp ((S.card : ℝ)*log (1+x)) := by
    rw [exp_nat_mul, exp_log (by positivity)]
  rw [hpow, hcore] at hpre
  have hdiv : coveredFraction P m ≤
      (exp ((j : ℝ)*log j-j+1+log j/2) *
        (exp ((S.card : ℝ)*log (1+x)) * exp (x*δ))) / exp ((j : ℝ)*log x) :=
    (le_div_iff₀ (exp_pos ((j : ℝ)*log x))).mpr (by
      simpa only [mul_comm] using hpre)
  apply hdiv.trans_eq
  rw [← exp_add, ← exp_add, ← exp_sub]
  congr 1
  dsimp only [x]
  rw [log_div hjR.ne' hδ.ne']
  field_simp
  ring

#print axioms coveredFraction_le_general_core
end Erdos970.GapAverages
