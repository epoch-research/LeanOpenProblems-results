import Submission.OppositeProgressionWeights
import Submission.VaughanArithmetic
import Submission.SmallPrimeReflectionDensity

/-! A natural-scale cancellation bound for the short logarithmic-divisor
term of Vaughan's identity in the actual opposite-progression kernel. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def signedWeightedKernel (P S : Finset ℕ) (C : ℕ)
    (F : ℕ → ℕ) (w : ℕ → ℝ) : ℝ :=
  weightedOppositeKernel P S C F w true-weightedOppositeKernel P S C F w false

lemma signedWeightedKernel_eq (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) (w : ℕ → ℝ) :
    signedWeightedKernel P S C F w =
      ∑ p ∈ P, ∑ b ∈ S, ∑ q ∈ Ioc C (F b), w q*oppositeProgressionSign p b q := by
  simp only [signedWeightedKernel,weightedOppositeKernel,← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro q hq
  have hq0 : q≠0 := by have := (mem_Ioc.mp hq).1; omega
  simp only [oppositeProgressionSign,if_neg hq0,if_true,Bool.false_eq_true,if_false,mul_sub]

noncomputable def normalizedArithmeticKernel (P S : Finset ℕ) (C : ℕ)
    (F : ℕ → ℕ) (f : ArithmeticFunction ℝ) : ℝ :=
  signedWeightedKernel P S C F (fun q => f q/Real.log q)

lemma normalizedArithmeticKernel_add (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (f g : ArithmeticFunction ℝ) :
    normalizedArithmeticKernel P S C F (f+g) =
      normalizedArithmeticKernel P S C F f+normalizedArithmeticKernel P S C F g := by
  simp only [normalizedArithmeticKernel,signedWeightedKernel_eq,ArithmeticFunction.add_apply,
    add_div,add_mul,sum_add_distrib]

lemma normalizedArithmeticKernel_sub (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (f g : ArithmeticFunction ℝ) :
    normalizedArithmeticKernel P S C F (f-g) =
      normalizedArithmeticKernel P S C F f-normalizedArithmeticKernel P S C F g := by
  have he (q : ℕ) : (f-g) q = f q-g q := rfl
  simp only [normalizedArithmeticKernel,signedWeightedKernel_eq,he,sub_div,sub_mul,sum_sub_distrib]

lemma normalizedArithmeticKernel_vonMangoldt (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) :
    normalizedArithmeticKernel P S C F ArithmeticFunction.vonMangoldt =
      mangoldtCutoffSkew P S C F := rfl

lemma logFactorRatio_bounds (u C X v : ℕ) (hu : 0 < u) (hC : 1 ≤ C)
    (hv : v ∈ Ioc (C/u) (X/u)) :
    0 ≤ Real.log v/Real.log (u*v : ℕ) ∧ Real.log v/Real.log (u*v : ℕ) ≤ 1 := by
  have hv0 : 0 < v := (Nat.zero_lt_of_lt (mem_Ioc.mp hv).1)
  have hprod : 1 < u*v := by
    have := (Nat.div_lt_iff_lt_mul hu).mp (mem_Ioc.mp hv).1
    nlinarith
  have hl : 0 < Real.log (u*v : ℕ) := Real.log_pos (by exact_mod_cast hprod)
  constructor
  · exact div_nonneg (Real.log_natCast_nonneg v) hl.le
  · apply (div_le_one hl).mpr
    exact Real.log_le_log (by exact_mod_cast hv0) (by exact_mod_cast (show v≤u*v by nlinarith))

lemma logFactorRatio_monotone (u C X : ℕ) (hu : 0 < u) (hC : 1 ≤ C) :
    MonotoneOn (fun v : ℕ => Real.log v/Real.log (u*v : ℕ)) (Set.Ioc (C/u) (X/u)) := by
  intro v hv w hw hvw
  have hv0 : 0 < v := Nat.zero_lt_of_lt hv.1
  have hw0 : 0 < w := by omega
  have hvprod : 1 < u*v := by
    have := (Nat.div_lt_iff_lt_mul hu).mp hv.1
    nlinarith
  have hwprod : 1 < u*w := by
    have := (Nat.div_lt_iff_lt_mul hu).mp hw.1
    nlinarith
  have hvlog : 0 < Real.log (u*v : ℕ) := Real.log_pos (by exact_mod_cast hvprod)
  have hwlog : 0 < Real.log (u*w : ℕ) := Real.log_pos (by exact_mod_cast hwprod)
  have hlvw : Real.log v ≤ Real.log w := Real.log_le_log (by exact_mod_cast hv0) (by exact_mod_cast hvw)
  have hlu := Real.log_natCast_nonneg u
  apply (div_le_div_iff₀ hvlog hwlog).mpr
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hu.ne') (by exact_mod_cast hw0.ne'),
    Nat.cast_mul,Real.log_mul (by exact_mod_cast hu.ne') (by exact_mod_cast hv0.ne')]
  nlinarith

noncomputable def shortLogPrimeKernel (U : ℕ) (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  normalizedArithmeticKernel P S C F
    (arithmeticTruncate U ArithmeticFunction.moebius*ArithmeticFunction.log)

/-- The short divisor remains outside the opposite progression sum. -/
lemma normalizedArithmeticKernel_truncated_expansion (U : ℕ) (P S : Finset ℕ) (C : ℕ)
    (F : ℕ → ℕ) (f g : ArithmeticFunction ℝ) :
    normalizedArithmeticKernel P S C F (arithmeticTruncate U f*g) =
      ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, f u*
        ∑ v ∈ Ioc (C/u) (F b/u),
          (g v/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v := by
  unfold normalizedArithmeticKernel
  rw [signedWeightedKernel_eq]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro b hb
  have he := truncated_convolution_interval U C (F b) f g (fun q => oppositeProgressionSign p b q/Real.log q)
  convert he using 1
  · apply sum_congr rfl
    intro q hq
    ring
  · apply sum_congr rfl
    intro u hu
    congr 1
    apply sum_congr rfl
    intro v hv
    have hv0 : v≠0 := (Nat.zero_lt_of_lt (mem_Ioc.mp hv).1).ne'
    have huv0 : u*v≠0 := Nat.mul_ne_zero (by have := (mem_Icc.mp hu).1; omega) hv0
    simp only [oppositeProgressionSign,if_neg hv0,
      if_neg huv0,Nat.mul_assoc,Nat.cast_mul]
    ring

lemma shortLogPrimeKernel_expansion (U : ℕ) (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) :
    shortLogPrimeKernel U P S C F =
      ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, (ArithmeticFunction.moebius u : ℝ)*
        ∑ v ∈ Ioc (C/u) (F b/u),
          (Real.log v/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v := by
  exact normalizedArithmeticKernel_truncated_expansion U P S C F
    ArithmeticFunction.moebius ArithmeticFunction.log

/-- This is actual signed cancellation: each short-divisor progression has
a bound independent of its length, modulus, and hyperbolic endpoint. -/
theorem shortLogPrimeKernel_bound (U : ℕ) (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hS : ∀ b ∈ S, 0 < b) (hC : 1 ≤ C) :
    |shortLogPrimeKernel U P S C F| ≤ 6*(P.card : ℝ)*S.card*U := by
  rw [shortLogPrimeKernel_expansion]
  calc
    _ ≤ ∑ p ∈ P, |∑ b ∈ S, ∑ u ∈ Icc 1 U, (ArithmeticFunction.moebius u : ℝ)*
        ∑ v ∈ Ioc (C/u) (F b/u), (Real.log v/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, (6 : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro u hu
      rw [abs_mul]
      have hμ : |(ArithmeticFunction.moebius u : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := u))
      have h := oppositeProgressionSign_weighted_bound p (b*u) (C/u) (F b/u) (hP p hp)
        (Nat.mul_pos (hS b hb) (mem_Icc.mp hu).1)
        (fun v => Real.log v/Real.log (u*v : ℕ)) 1 (by norm_num)
        (fun v hv => logFactorRatio_bounds u C (F b) v (mem_Icc.mp hu).1 hC hv)
        (Or.inl (logFactorRatio_monotone u C (F b) (mem_Icc.mp hu).1 hC))
      nlinarith [abs_nonneg (ArithmeticFunction.moebius u : ℝ),
        abs_nonneg (∑ v ∈ Ioc (C/u) (F b/u), (Real.log v/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v)]
    _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; ring

/-- A reusable natural-density estimate for a fixed multiple of the number
of prime moduli and short cofactors. -/
theorem tendsto_zero_of_prime_cofactor_bound (K : ℕ → ℝ) (P : ℕ → Finset ℕ)
    (C : ℕ → ℕ) (A : ℝ) (hA : 0 ≤ A) (hC : Tendsto C atTop atTop)
    (hP : ∀ᶠ N in atTop, ∀ p ∈ P N, p.Prime ∧ p≤C N)
    (hbound : ∀ᶠ N in atTop, |K N| ≤ A*(P N).card*(N/(C N+1) : ℕ)) :
    Tendsto (fun N : ℕ => K N/N) atTop (𝓝 0) := by
  have ht := (primesBelow_card_div_tendsto_zero.comp hC).const_mul A
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hP,hbound,eventually_gt_atTop (0 : ℕ),hC.eventually (eventually_ge_atTop 1)]
    with N hp hb hN hc
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hC0 : (0 : ℝ)<C N := by exact_mod_cast hc
  have hcard : ((P N).card : ℝ) ≤ ((C N+1).primesBelow).card := by
    exact_mod_cast card_le_card (show P N ⊆ (C N+1).primesBelow from fun p hp' =>
      Nat.mem_primesBelow.mpr ⟨by have := (hp p hp').2; omega,(hp p hp').1⟩)
  have hd : ((N/(C N+1) : ℕ) : ℝ) ≤ (N : ℝ)/(C N) := by
    apply le_trans (Nat.cast_div_le (α := ℝ) (m := N) (n := C N+1))
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) hC0
    exact_mod_cast (Nat.le_succ (C N))
  rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
  calc
    |K N|/N ≤ (A*(P N).card*(N/(C N+1) : ℕ))/N := div_le_div_of_nonneg_right hb hN0.le
    _ ≤ (A*(((C N+1).primesBelow).card : ℝ)*((N : ℝ)/(C N)))/N := by
      apply div_le_div_of_nonneg_right _ hN0.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcard hA) hd (Nat.cast_nonneg _) (by positivity)
    _ = A*(((C N+1).primesBelow).card : ℝ)/(C N) := by field_simp
    _ = _ := by simp only [Function.comp_apply]; ring

/-- The short logarithmic-divisor term is negligible for every fixed U,
uniformly over all prime and cofactor endpoints. -/
theorem shortLogPrimeKernel_tendsto (U : ℕ) (P : ℕ → Finset ℕ) (C : ℕ → ℕ)
    (F : ℕ → ℕ → ℕ) (hC : Tendsto C atTop atTop)
    (hP : ∀ᶠ N in atTop, ∀ p ∈ P N, p.Prime ∧ p≤C N) :
    Tendsto (fun N : ℕ => shortLogPrimeKernel U (P N) (Icc 1 (N/(C N+1))) (C N) (F N)/N)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_prime_cofactor_bound _ P C (6*U) (by positivity) hC hP
  filter_upwards [hP,hC.eventually (eventually_ge_atTop 1)] with N hp hc
  have h := shortLogPrimeKernel_bound U (P N) (Icc 1 (N/(C N+1))) (C N) (F N)
    (fun p hp' => (hp p hp').1.pos) (fun b hb => (mem_Icc.mp hb).1) hc
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at h
  exact h.trans_eq (by ring)

#print axioms shortLogPrimeKernel_expansion
#print axioms shortLogPrimeKernel_bound
#print axioms shortLogPrimeKernel_tendsto
end Erdos371
