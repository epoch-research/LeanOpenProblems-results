import Submission.VaughanPrimeKernel

/-! Signed short-divisor cancellation with growing Vaughan cutoffs. Keeping
the inverse logarithm in the second short term removes a logarithmic loss.
Separation between the modulus bound and the prime cutoff permits polynomially
growing short cutoffs. No cancellation of the remaining long term is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma truncated_moebius_mangoldt_abs_le_log (U V q : ℕ) :
    |(arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt) q| ≤ Real.log q := by
  have he : Real.log q = ∑ uv ∈ q.divisorsAntidiagonal,
      (ArithmeticFunction.zeta uv.1 : ℝ)*ArithmeticFunction.vonMangoldt uv.2 := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f q) ArithmeticFunction.zeta_mul_vonMangoldt
    simpa only [ArithmeticFunction.mul_apply,ArithmeticFunction.natCoe_apply,ArithmeticFunction.log_apply] using hh.symm
  rw [ArithmeticFunction.mul_apply,he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro uv huv
  have huv := Nat.mem_divisorsAntidiagonal.mp huv
  have hu0 : uv.1 ≠ 0 := by intro h; simp [h] at huv; omega
  have hz : (ArithmeticFunction.zeta uv.1 : ℝ) = 1 := by
    simp [ArithmeticFunction.zeta_apply,hu0]
  rw [hz,one_mul,abs_mul]
  have hmu : |arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) uv.1| ≤ 1 := by
    rw [arithmeticTruncate_apply]
    split_ifs
    · simp only [ArithmeticFunction.intCoe_apply]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := uv.1))
    · norm_num
  have hl : |arithmeticTruncate V ArithmeticFunction.vonMangoldt uv.2| ≤
      ArithmeticFunction.vonMangoldt uv.2 := by
    rw [arithmeticTruncate_apply]
    split_ifs
    · exact (abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg).le
    · simpa using (ArithmeticFunction.vonMangoldt_nonneg (n := uv.2))
  exact (mul_le_mul hmu hl (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma truncated_moebius_mangoldt_sum_abs (U V : ℕ) :
    (∑ q ∈ Icc 1 (U*V),
      |(arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticTruncate V ArithmeticFunction.vonMangoldt) q|) ≤
      (U*V : ℕ)*Real.log (U*V : ℕ) := by
  calc
    _ ≤ ∑ _q ∈ Icc 1 (U*V), Real.log (U*V : ℕ) := by
      apply sum_le_sum
      intro q hq
      exact (truncated_moebius_mangoldt_abs_le_log U V q).trans
        (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hq).1) (by exact_mod_cast (mem_Icc.mp hq).2))
    _ = _ := by simp

lemma shortZetaPrimeKernel_log_bound (U : ℕ) (f : ArithmeticFunction ℝ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hS : ∀ b ∈ S, 0 < b) (hC : 1 ≤ C) :
    |shortZetaPrimeKernel U f P S C F| ≤
      6*(P.card : ℝ)*S.card*(∑ u ∈ Icc 1 U, |f u|)/Real.log (C+1 : ℕ) := by
  have hlog : 0 < Real.log (C+1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1<C+1))
  rw [shortZetaPrimeKernel_expansion]
  calc
    _ ≤ ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, |f u| *(6/Real.log (C+1 : ℕ)) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro p hp
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro u hu
      rw [abs_mul]
      have hu1 := (mem_Icc.mp hu).1
      have hh := oppositeProgressionSign_weighted_bound p (b*u) (C/u) (F b/u)
        (hP p hp) (Nat.mul_pos (hS b hb) hu1)
        (fun v => 1/Real.log (u*v : ℕ)) (1/Real.log (C+1 : ℕ)) (by positivity)
        (fun v hv => by
          have huv : C+1 ≤ u*v := by
            have := (Nat.div_lt_iff_lt_mul hu1).mp (mem_Ioc.mp hv).1
            nlinarith
          have hl : Real.log (C+1 : ℕ) ≤ Real.log (u*v : ℕ) := Real.log_le_log (by positivity : (0 : ℝ)<(C+1 : ℕ))
            (by exact_mod_cast huv)
          exact ⟨div_nonneg (by norm_num) (hlog.le.trans hl),one_div_le_one_div_of_le hlog hl⟩)
        (Or.inr (inverseLogFactor_antitone u C (F b) hu1 hC))
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact hh.trans_eq (by ring)
    _ = _ := by
      simp only [← sum_mul,sum_const,nsmul_eq_mul]
      ring

/-- If U*V is below the prime cutoff, both short terms have a bound with no
logarithmic factor. The sign inside each progression is retained. -/
theorem mangoldtKernel_growing_vaughan_error_bound (U V : ℕ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U*V ≤ C)
    (hP : ∀ p ∈ P, 0 < p) (hS : ∀ b ∈ S, 0 < b) :
    |mangoldtCutoffSkew P S C F-vaughanLongKernel U V P S C F| ≤
      12*(P.card : ℝ)*S.card*(U*V : ℕ) := by
  have hVC : V ≤ C := (by nlinarith : V ≤ U*V).trans hUV
  have hC : 1 ≤ C := hV.trans hVC
  have hlog : 0 < Real.log (C+1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1<C+1))
  have hfirst := shortLogPrimeKernel_bound U P S C F hP hS hC
  have hsecond := shortZetaPrimeKernel_log_bound (U*V)
    (arithmeticTruncate U ArithmeticFunction.moebius*arithmeticTruncate V ArithmeticFunction.vonMangoldt)
    P S C F hP hS hC
  have hsum := truncated_moebius_mangoldt_sum_abs U V
  have hlogUV : Real.log (U*V : ℕ) ≤ Real.log (C+1 : ℕ) :=
    Real.log_le_log (by positivity : (0 : ℝ)<(U*V : ℕ)) (by exact_mod_cast (by omega : U*V ≤ C+1))
  have hcoef : (∑ u ∈ Icc 1 (U*V),
      |(arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
        arithmeticTruncate V ArithmeticFunction.vonMangoldt) u|)/Real.log (C+1 : ℕ) ≤ (U*V : ℕ) := by
    apply (div_le_iff₀ hlog).mpr
    exact hsum.trans (mul_le_mul_of_nonneg_left hlogUV (Nat.cast_nonneg _))
  have hs : |shortZetaPrimeKernel (U*V)
      (arithmeticTruncate U ArithmeticFunction.moebius*arithmeticTruncate V ArithmeticFunction.vonMangoldt)
      P S C F| ≤ 6*(P.card : ℝ)*S.card*(U*V : ℕ) := by
    apply hsecond.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcoef
      (by positivity : (0 : ℝ) ≤ 6*P.card*S.card)
  have hUr : (U : ℝ) ≤ (U*V : ℕ) := by exact_mod_cast (by nlinarith : U ≤ U*V)
  have hf := hfirst.trans (mul_le_mul_of_nonneg_left hUr (by positivity : (0 : ℝ)≤6*P.card*S.card))
  rw [mangoldtKernel_vaughan_decomposition U V P S C F hVC,add_sub_cancel_right]
  exact (abs_sub _ _).trans ((add_le_add hf hs).trans_eq (by ring))

/-- Cardinality form of the normalized error. No prime-counting estimate is
needed: it holds for arbitrary positive moduli and arbitrary endpoints F. -/
theorem mangoldtKernel_growing_vaughan_ratio_bound (U V N : ℕ)
    (P : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (hN : 0 < N) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U*V ≤ C)
    (hP : ∀ p ∈ P, 0 < p) :
    |(mangoldtCutoffSkew P (Icc 1 (N/(C+1))) C F-
        vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F)/N| ≤
      12*(P.card : ℝ)*(U*V : ℕ)/(C+1 : ℕ) := by
  have hb := mangoldtKernel_growing_vaughan_error_bound U V P (Icc 1 (N/(C+1))) C F
    hU hV hUV hP (fun b hb => (mem_Icc.mp hb).1)
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hb
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  rw [abs_div,abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := N) (n := C+1))
    (by positivity : (0 : ℝ)≤12*P.card*(U*V : ℕ))
  convert hh using 1 <;> ring

/-- Growing cutoffs are valid whenever the explicit cardinality budget
vanishes. The resulting long kernel, not its absolute majorant, remains. -/
theorem mangoldtKernel_growing_vaughan_remainder_tendsto (U V C : ℕ → ℕ)
    (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℕ)
    (hcut : ∀ᶠ N : ℕ in atTop, 1 ≤ U N ∧ 1 ≤ V N ∧ U N*V N ≤ C N)
    (hP : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P N, 0 < p)
    (hbudget : Tendsto (fun N => ((P N).card : ℝ)*(U N*V N : ℕ)/(C N+1 : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun N => (mangoldtCutoffSkew (P N) (Icc 1 (N/(C N+1))) (C N) (F N)-
      vaughanLongKernel (U N) (V N) (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N)
      atTop (𝓝 0) := by
  have ht := hbudget.const_mul 12
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hcut,hP,eventually_gt_atTop (0 : ℕ)] with N hc hp hN
  rw [Real.norm_eq_abs]
  simpa only [mul_div_assoc,mul_assoc] using
    mangoldtKernel_growing_vaughan_ratio_bound (U N) (V N) N (P N) (C N) (F N) hN hc.1 hc.2.1 hc.2.2 hp

#print axioms mangoldtKernel_growing_vaughan_error_bound
#print axioms mangoldtKernel_growing_vaughan_remainder_tendsto
end Erdos371
