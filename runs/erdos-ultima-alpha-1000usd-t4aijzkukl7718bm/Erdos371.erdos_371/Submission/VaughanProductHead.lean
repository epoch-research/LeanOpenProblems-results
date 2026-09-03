import Submission.PowerSeparatedPrimeKernel

/-! Signed cancellation of the bounded-product part INSIDE the long Vaughan
convolution. The remaining kernel has core divisor product greater than T;
no cancellation of that surviving large-product kernel is asserted. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def vaughanCore (U V : ℕ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)-arithmeticTruncate U ArithmeticFunction.moebius)*
    (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt)

lemma vaughanCore_abs_le_log (U V q : ℕ) : |vaughanCore U V q| ≤ Real.log q := by
  have he : Real.log q = ∑ uv ∈ q.divisorsAntidiagonal,
      (ArithmeticFunction.zeta uv.1 : ℝ)*ArithmeticFunction.vonMangoldt uv.2 := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f q) ArithmeticFunction.zeta_mul_vonMangoldt
    simpa only [ArithmeticFunction.mul_apply,ArithmeticFunction.natCoe_apply,ArithmeticFunction.log_apply] using hh.symm
  rw [vaughanCore,ArithmeticFunction.mul_apply,he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro uv huv
  have huv := Nat.mem_divisorsAntidiagonal.mp huv
  have hu0 : uv.1 ≠ 0 := by intro h; simp [h] at huv; omega
  have hz : (ArithmeticFunction.zeta uv.1 : ℝ) = 1 := by
    simp [ArithmeticFunction.zeta_apply,hu0]
  rw [hz,one_mul,abs_mul]
  have hmu : |((ArithmeticFunction.moebius : ArithmeticFunction ℝ)-
      arithmeticTruncate U ArithmeticFunction.moebius) uv.1| ≤ 1 := by
    change |(ArithmeticFunction.moebius uv.1 : ℝ)-
      (if uv.1≤U then (ArithmeticFunction.moebius uv.1 : ℝ) else 0)| ≤ 1
    split_ifs
    · simp
    · simpa only [sub_zero] using
        (show |(ArithmeticFunction.moebius uv.1 : ℝ)| ≤ 1 by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := uv.1)))
  have hl : |(ArithmeticFunction.vonMangoldt-
      arithmeticTruncate V ArithmeticFunction.vonMangoldt) uv.2| ≤
      ArithmeticFunction.vonMangoldt uv.2 := by
    change |ArithmeticFunction.vonMangoldt uv.2-
      (if uv.2≤V then ArithmeticFunction.vonMangoldt uv.2 else 0)| ≤ _
    split_ifs
    · simpa only [sub_self,abs_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := uv.2))
    · simp only [sub_zero,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,le_refl]
  exact (mul_le_mul hmu hl (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

lemma arithmetic_sum_abs_le_log (f : ArithmeticFunction ℝ) (T : ℕ)
    (hf : ∀ d, |f d| ≤ Real.log d) :
    (∑ d ∈ Icc 1 T, |f d|) ≤ (T : ℝ)*Real.log T := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 T, Real.log T := by
      apply sum_le_sum
      intro d hd
      exact (hf d).trans (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hd).1)
        (by exact_mod_cast (mem_Icc.mp hd).2))
    _ = _ := by simp

/-- Every logarithmically bounded divisor coefficient has this signed head
bound. The complementary variable is unweighted apart from an inverse log. -/
lemma logarithmic_divisor_head_bound (f : ArithmeticFunction ℝ) (T C : ℕ)
    (P S : Finset ℕ) (F : ℕ → ℕ) (hf : ∀ d, |f d| ≤ Real.log d)
    (hT : 1 ≤ T) (hTC : T ≤ C)
    (hP : ∀ p ∈ P, 0<p) (hS : ∀ b ∈ S, 0<b) :
    |shortZetaPrimeKernel T f P S C F| ≤ 6*(P.card : ℝ)*S.card*T := by
  have hC : 1 ≤ C := hT.trans hTC
  have hlog : 0 < Real.log (C+1 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1<C+1))
  have hb := shortZetaPrimeKernel_log_bound T f P S C F hP hS hC
  have hs := arithmetic_sum_abs_le_log f T hf
  have hl : Real.log T ≤ Real.log (C+1 : ℕ) := Real.log_le_log
    (by exact_mod_cast hT) (by exact_mod_cast (by omega : T≤C+1))
  have hq : (∑ d ∈ Icc 1 T, |f d|)/Real.log (C+1 : ℕ) ≤ T := by
    apply (div_le_iff₀ hlog).mpr
    exact hs.trans (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg T))
  exact hb.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ)≤6*P.card*S.card))

noncomputable def vaughanProductTailKernel (U V T : ℕ) (P S : Finset ℕ)
    (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  normalizedArithmeticKernel P S C F
    ((vaughanCore U V-arithmeticTruncate T (vaughanCore U V))*ArithmeticFunction.zeta)

lemma vaughanLong_sub_product_tail (U V T : ℕ) (P S : Finset ℕ)
    (C : ℕ) (F : ℕ → ℕ) :
    vaughanLongKernel U V P S C F-vaughanProductTailKernel U V T P S C F =
      shortZetaPrimeKernel T (vaughanCore U V) P S C F := by
  rw [vaughanProductTailKernel,sub_mul,normalizedArithmeticKernel_sub]
  change normalizedArithmeticKernel P S C F (vaughanCore U V*ArithmeticFunction.zeta)-
    (normalizedArithmeticKernel P S C F (vaughanCore U V*ArithmeticFunction.zeta)-
      shortZetaPrimeKernel T (vaughanCore U V) P S C F) = _
  ring

/-- This removes a portion of the long term itself, uniformly in the
original truncations U,V. No absolute mass bound on the whole tail is used. -/
theorem vaughanLong_product_head_bound (U V T : ℕ) (P S : Finset ℕ)
    (C : ℕ) (F : ℕ → ℕ) (hT : 1 ≤ T) (hTC : T ≤ C)
    (hP : ∀ p ∈ P, 0<p) (hS : ∀ b ∈ S, 0<b) :
    |vaughanLongKernel U V P S C F-vaughanProductTailKernel U V T P S C F| ≤
      6*(P.card : ℝ)*S.card*T := by
  rw [vaughanLong_sub_product_tail]
  exact logarithmic_divisor_head_bound _ T C P S F (vaughanCore_abs_le_log U V) hT hTC hP hS

lemma vaughanLong_product_head_ratio_bound (U V T N C : ℕ) (P : Finset ℕ)
    (F : ℕ → ℕ) (hN : 0<N) (hT : 1 ≤ T) (hTC : T ≤ C) (hP : ∀ p ∈ P, 0<p) :
    |(vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F-
      vaughanProductTailKernel U V T P (Icc 1 (N/(C+1))) C F)/N| ≤
        6*(P.card : ℝ)*T/(C+1 : ℕ) := by
  have hb := vaughanLong_product_head_bound U V T P (Icc 1 (N/(C+1))) C F
    hT hTC hP (fun b hb => (mem_Icc.mp hb).1)
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hb
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  rw [abs_div,abs_of_pos hNr]
  apply (div_le_iff₀ hNr).mpr
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ) (m := N) (n := C+1))
    (by positivity : (0 : ℝ)≤6*P.card*T)
  convert hh using 1 <;> ring

/-- An explicit power-saving bound for the removed core-product head. -/
theorem vaughanLong_product_head_power_bound (U V T N C : ℕ) (P : Finset ℕ)
    (F : ℕ → ℕ) (a b τ : ℝ) (hN : 1≤N) (hT : 1≤T) (hTC : T≤C)
    (hPpos : ∀ p ∈ P, 0<p) (hP : (P.card : ℝ)≤(N : ℝ)^a)
    (hC : (N : ℝ)^b≤C) (hTpow : (T : ℝ)≤(N : ℝ)^τ) :
    |(vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F-
      vaughanProductTailKernel U V T P (Icc 1 (N/(C+1))) C F)/N| ≤
        6*(N : ℝ)^(-(b-a-τ)) := by
  have hh := vaughanLong_product_head_ratio_bound U V T N C P F hN hT hTC hPpos
  have hp := vaughan_cardinality_budget_power_bound N T 1 C P a b τ 0 hN hP hC hTpow (by simp)
  simp only [Nat.mul_one,sub_zero] at hp
  exact hh.trans (by simpa only [mul_div_assoc,mul_assoc] using
    mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ)≤6))

/-- The core-product cutoff can be floor(N^τ) for ANY τ<b-a, independently
of the original U,V. This may be much larger than their product. -/
theorem vaughanLong_polynomial_product_head_zero (a b τ : ℝ)
    (ha : 0≤a) (hτ : 0<τ) (hgap : a+τ<b)
    (U V C : ℕ → ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℕ)
    (hP : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P N, 0<p)
    (hsize : ∀ᶠ N : ℕ in atTop, (P N).card≤(N : ℝ)^a ∧ (N : ℝ)^b≤C N) :
    Tendsto (fun N => (vaughanLongKernel (U N) (V N) (P N) (Icc 1 (N/(C N+1))) (C N) (F N)-
      vaughanProductTailKernel (U N) (V N) (vaughanPowerCutoff τ N)
        (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N) atTop (𝓝 0) := by
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0<b-a-τ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 6
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hP,hsize,eventually_ge_atTop (1 : ℕ)] with N hp hs hN
  have hT := vaughanPowerCutoff_pos τ hτ.le N hN
  have hTC : vaughanPowerCutoff τ N ≤ C N := by
    have hh := (vaughanPowerCutoff_le τ N).trans
      ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith : τ≤b)).trans hs.2)
    exact_mod_cast hh
  rw [Real.norm_eq_abs]
  exact vaughanLong_product_head_power_bound (U N) (V N) _ N (C N) (P N) (F N) a b τ
    hN hT hTC hp hs.1 hs.2 (vaughanPowerCutoff_le τ N)

/-- The actual signed prime kernel can be reduced to the large-core-product
kernel, with polynomial choices for all three cutoffs. This theorem asserts
only the vanishing of their difference, not of either kernel separately. -/
theorem cutoffPrimeSkew_polynomial_product_tail_remainder_tendsto (a b γ τ : ℝ)
    (ha : 0≤a) (hγ : 0<γ) (hτ : 0<τ) (hgapγ : a+2*γ<b) (hgapτ : a+τ<b)
    (B C : ℕ → ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℕ)
    (harith : ∀ᶠ N : ℕ in atTop, 2≤B N ∧ B N≤C N ∧ N+1≤(B N)^2 ∧
      (∀ p ∈ P N, p.Prime ∧ B N<p) ∧
      (∀ k ∈ Icc 1 (N/(C N+1)), k*F N k≤N))
    (hsize : ∀ᶠ N : ℕ in atTop, (P N).card≤(N : ℝ)^a ∧ (N : ℝ)^b≤C N) :
    Tendsto (fun N => (cutoffPrimeSkew (P N) (Icc 1 (N/(C N+1))) (C N) (F N)-
      vaughanProductTailKernel (vaughanPowerCutoff γ N) (vaughanPowerCutoff γ N)
        (vaughanPowerCutoff τ N) (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N)
      atTop (𝓝 0) := by
  have hp := cutoffPrimeSkew_polynomial_vaughan_remainder_tendsto a b γ ha hγ hgapγ
    B C P F harith hsize
  have hP : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P N, 0<p := by
    filter_upwards [harith] with N hn p hp
    exact (hn.2.2.2.1 p hp).1.pos
  have hh := vaughanLong_polynomial_product_head_zero a b τ ha hτ hgapτ
    (vaughanPowerCutoff γ) (vaughanPowerCutoff γ) C P F hP hsize
  have ht := hp.add hh
  simp only [add_zero] at ht
  convert ht using 1
  ext N
  ring

#print axioms cutoffPrimeSkew_polynomial_product_tail_remainder_tendsto
#print axioms vaughanLong_product_head_bound
#print axioms vaughanLong_polynomial_product_head_zero
end Erdos371
