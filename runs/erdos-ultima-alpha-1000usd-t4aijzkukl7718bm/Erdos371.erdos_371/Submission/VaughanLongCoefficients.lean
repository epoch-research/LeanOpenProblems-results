import Submission.VaughanPrimeKernel

/-! The long-divisor remainder has substantial ordinary-composite support.
In particular, it has no summable absolute reciprocal tail like the proper
prime powers in the earlier Mangoldt replacement. -/
namespace Erdos371
open Finset Filter

lemma truncated_convolution_apply_rough (U q : ℕ) (f g : ArithmeticFunction ℝ)
    (hU : 1 ≤ U) (hq : q≠0) (hrough : U < q.minFac) :
    (arithmeticTruncate U f*g) q = f 1*g q := by
  rw [truncated_convolution_apply U q f g hq]
  have he : (Icc 1 U).filter (fun u => u∣q) = {1} := by
    ext u
    simp only [mem_filter,mem_Icc,mem_singleton]
    constructor
    · rintro ⟨⟨hu1,huU⟩,hud⟩
      by_contra hne
      have := Nat.minFac_le_of_dvd (by omega : 2 ≤ u) hud
      omega
    · rintro rfl
      exact ⟨⟨le_rfl,hU⟩,one_dvd _⟩
  rw [he,sum_singleton,Nat.div_one]

/-- On numbers without small prime divisors, the long term is exactly
Lambda(q)-log(q), not a pointwise-small remainder. -/
theorem vaughanLongFunction_rough (U V q : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hq : 0 < q) (hrough : max U V < q.minFac) :
    vaughanLongFunction U V q = ArithmeticFunction.vonMangoldt q-Real.log q := by
  have hUr : U < q.minFac := (le_max_left _ _).trans_lt hrough
  have hVr : V < q.minFac := (le_max_right _ _).trans_lt hrough
  have hVq : ¬q≤V := by have := Nat.minFac_le hq; omega
  have ht := congrArg (fun f : ArithmeticFunction ℝ => f q) (vonMangoldt_truncated_identity U V)
  have hs : (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log) q =
      Real.log q := by
    rw [truncated_convolution_apply_rough U q _ _ hU hq.ne' hUr]
    simp
  have hc : (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) q = 0 := by
    rw [mul_assoc,truncated_convolution_apply_rough U q _ _ hU hq.ne' hUr,
      truncated_convolution_apply_rough V q _ _ hV hq.ne' hVr]
    simp
  change ArithmeticFunction.vonMangoldt q = arithmeticTruncate V ArithmeticFunction.vonMangoldt q+
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.log) q-
    (arithmeticTruncate U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
      arithmeticTruncate V ArithmeticFunction.vonMangoldt*ArithmeticFunction.zeta) q+
    vaughanLongFunction U V q at ht
  rw [hs,hc,arithmeticTruncate_apply,if_neg hVq] at ht
  linarith

lemma vonMangoldt_distinct_prime_mul (r s : ℕ) (hr : r.Prime) (hs : s.Prime) (hrs : r≠s) :
    ArithmeticFunction.vonMangoldt (r*s) = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro h
  obtain ⟨p,hp,hunique⟩ := isPrimePow_iff_unique_prime_dvd.mp h
  have hrp := hunique r ⟨hr,dvd_mul_right r s⟩
  have hsp := hunique s ⟨hs,dvd_mul_left s r⟩
  exact hrs (hrp.trans hsp.symm)

/-- Distinct products of two sufficiently large primes carry normalized
coefficient exactly -1, whatever the fixed truncation levels are. -/
theorem vaughanLongFunction_semiprime (U V r s : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hr : r.Prime) (hs : s.Prime) (hrs : r≠s) (hrUV : max U V < r) (hsUV : max U V < s) :
    vaughanLongFunction U V (r*s)/Real.log (r*s : ℕ) = -1 := by
  have hrough : max U V < (r*s).minFac := by
    rw [minFac_mul_of_one_lt r s hr.one_lt hs.one_lt,hr.minFac_eq,hs.minFac_eq]
    exact lt_min hrUV hsUV
  have hprod : 1 < r*s := by have := hr.one_lt; have := hs.one_lt; nlinarith
  rw [vaughanLongFunction_rough U V (r*s) hU hV (Nat.mul_pos hr.pos hs.pos) hrough,
    vonMangoldt_distinct_prime_mul r s hr hs hrs,zero_sub,neg_div,
    div_self (Real.log_pos (by exact_mod_cast hprod)).ne']

/-- Consequently, the absolute reciprocal coefficients of the long term
are not summable. The prime-power tail argument cannot be reused for it. -/
theorem vaughanLongFunction_not_abs_reciprocal_summable (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ¬Summable (fun q : ℕ => |vaughanLongFunction U V q/Real.log q|/q) := by
  intro hsum
  obtain ⟨r,hrUV,hr⟩ := Nat.exists_infinite_primes (max U V+1)
  have hrUV' : max U V < r := by omega
  have hinj : Function.Injective (fun n : ℕ => r*n) := fun a b h => Nat.eq_of_mul_eq_mul_left hr.pos h
  have hsub := (hsum.comp_injective hinj).mul_left (r : ℝ)
  have hind := hsub.indicator {n : ℕ | n.Prime}
  apply not_summable_one_div_on_primes
  apply (summable_congr_atTop ?_).mp hind
  filter_upwards [eventually_gt_atTop (max (max U V) r)] with s hslarge
  by_cases hs : s.Prime
  · have hsUV : max U V < s := (le_max_left _ _).trans_lt hslarge
    have hrs : r≠s := ne_of_lt ((le_max_right _ _).trans_lt hslarge)
    simp only [Set.indicator_apply,Set.mem_setOf_eq,hs,if_true,Function.comp_apply]
    rw [vaughanLongFunction_semiprime U V r s hU hV hr hs hrs hrUV' hsUV]
    norm_num only [abs_neg,abs_one,Nat.cast_mul]
    have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne_zero
    field_simp
  · simp [hs]

#print axioms vaughanLongFunction_rough
#print axioms vaughanLongFunction_semiprime
#print axioms vaughanLongFunction_not_abs_reciprocal_summable
end Erdos371
