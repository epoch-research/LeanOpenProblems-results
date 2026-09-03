import Submission.ShortDivisorPrimeKernel

/-! The short terms of Vaughan's identity are negligible in the natural
upper-half prime kernel. The remaining long-divisor term is not estimated. -/
namespace Erdos371
open Finset Filter
open scoped Topology

lemma inverseLogFactor_bounds (u C X v : ℕ) (hu : 0 < u) (hC : 1 ≤ C)
    (hv : v ∈ Ioc (C/u) (X/u)) :
    0 ≤ 1/Real.log (u*v : ℕ) ∧ 1/Real.log (u*v : ℕ) ≤ 2 := by
  have hprod : 2 ≤ u*v := by
    have := (Nat.div_lt_iff_lt_mul hu).mp (mem_Ioc.mp hv).1
    nlinarith
  have hl : 1/2 < Real.log (u*v : ℕ) :=
    (by linarith [Real.log_two_gt_d9] : (1/2 : ℝ)<Real.log 2).trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hprod))
  constructor
  · positivity
  · apply (div_le_iff₀ (by linarith : 0 < Real.log (u*v : ℕ))).mpr
    linarith

lemma inverseLogFactor_antitone (u C X : ℕ) (hu : 0 < u) (hC : 1 ≤ C) :
    AntitoneOn (fun v : ℕ => 1/Real.log (u*v : ℕ)) (Set.Ioc (C/u) (X/u)) := by
  intro v hv w hw hvw
  have hprod : 1 < u*v := by
    have := (Nat.div_lt_iff_lt_mul hu).mp hv.1
    nlinarith
  apply one_div_le_one_div_of_le (Real.log_pos (by exact_mod_cast hprod))
  exact Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hprod))
    (by exact_mod_cast (Nat.mul_le_mul_left u hvw))

noncomputable def shortZetaPrimeKernel (U : ℕ) (f : ArithmeticFunction ℝ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  normalizedArithmeticKernel P S C F (arithmeticTruncate U f*ArithmeticFunction.zeta)

lemma shortZetaPrimeKernel_expansion (U : ℕ) (f : ArithmeticFunction ℝ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) :
    shortZetaPrimeKernel U f P S C F =
      ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, f u*
        ∑ v ∈ Ioc (C/u) (F b/u),
          (1/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v := by
  unfold shortZetaPrimeKernel
  rw [normalizedArithmeticKernel_truncated_expansion]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro b hb
  apply sum_congr rfl
  intro u hu
  congr 1
  apply sum_congr rfl
  intro v hv
  have hv0 : v≠0 := (Nat.zero_lt_of_lt (mem_Ioc.mp hv).1).ne'
  simp [ArithmeticFunction.zeta_apply,hv0]

/-- The second short term permits arbitrary fixed divisor coefficients. -/
theorem shortZetaPrimeKernel_bound (U : ℕ) (f : ArithmeticFunction ℝ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hS : ∀ b ∈ S, 0 < b) (hC : 1 ≤ C) :
    |shortZetaPrimeKernel U f P S C F| ≤
      12*(P.card : ℝ)*S.card*(∑ u ∈ Icc 1 U, |f u|) := by
  rw [shortZetaPrimeKernel_expansion]
  calc
    _ ≤ ∑ p ∈ P, |∑ b ∈ S, ∑ u ∈ Icc 1 U, f u*
        ∑ v ∈ Ioc (C/u) (F b/u), (1/Real.log (u*v : ℕ))*oppositeProgressionSign p (b*u) v| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ b ∈ S, ∑ u ∈ Icc 1 U, |f u| * 12 := by
      apply sum_le_sum
      intro p hp
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro u hu
      rw [abs_mul]
      have h := oppositeProgressionSign_weighted_bound p (b*u) (C/u) (F b/u) (hP p hp)
        (Nat.mul_pos (hS b hb) (mem_Icc.mp hu).1)
        (fun v => 1/Real.log (u*v : ℕ)) 2 (by norm_num)
        (fun v hv => inverseLogFactor_bounds u C (F b) v (mem_Icc.mp hu).1 hC hv)
        (Or.inr (inverseLogFactor_antitone u C (F b) (mem_Icc.mp hu).1 hC))
      exact mul_le_mul_of_nonneg_left (by norm_num at h ⊢; exact h) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; simp only [sum_const,nsmul_eq_mul]; ring

theorem shortZetaPrimeKernel_tendsto (U : ℕ) (f : ArithmeticFunction ℝ)
    (P : ℕ → Finset ℕ) (C : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (hC : Tendsto C atTop atTop)
    (hP : ∀ᶠ N in atTop, ∀ p ∈ P N, p.Prime ∧ p≤C N) :
    Tendsto (fun N : ℕ => shortZetaPrimeKernel U f (P N) (Icc 1 (N/(C N+1))) (C N) (F N)/N)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_prime_cofactor_bound _ P C (12*(∑ u ∈ Icc 1 U, |f u|)) (by positivity) hC hP
  filter_upwards [hP,hC.eventually (eventually_ge_atTop 1)] with N hp hc
  have h := shortZetaPrimeKernel_bound U f (P N) (Icc 1 (N/(C N+1))) (C N) (F N)
    (fun p hp' => (hp p hp').1.pos) (fun b hb => (mem_Icc.mp hb).1) hc
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at h
  exact h.trans_eq (by ring)

noncomputable def vaughanLongFunction (U V : ℕ) : ArithmeticFunction ℝ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)-arithmeticTruncate U ArithmeticFunction.moebius)*
    (ArithmeticFunction.vonMangoldt-arithmeticTruncate V ArithmeticFunction.vonMangoldt)*
      ArithmeticFunction.zeta

noncomputable def vaughanLongKernel (U V : ℕ) (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  normalizedArithmeticKernel P S C F (vaughanLongFunction U V)

lemma normalizedArithmeticKernel_truncate_zero (V : ℕ) (f : ArithmeticFunction ℝ)
    (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) (hVC : V≤C) :
    normalizedArithmeticKernel P S C F (arithmeticTruncate V f) = 0 := by
  rw [normalizedArithmeticKernel,signedWeightedKernel_eq]
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro b hb
  apply sum_eq_zero
  intro q hq
  have hqV : ¬q≤V := by have := (mem_Ioc.mp hq).1; omega
  simp [hqV]

/-- The identity is exact before taking any limits. Once C>=V, the direct
small-Mangoldt term is identically zero. -/
theorem mangoldtKernel_vaughan_decomposition (U V : ℕ) (P S : Finset ℕ)
    (C : ℕ) (F : ℕ → ℕ) (hVC : V≤C) :
    mangoldtCutoffSkew P S C F =
      shortLogPrimeKernel U P S C F -
      shortZetaPrimeKernel (U*V)
        (arithmeticTruncate U ArithmeticFunction.moebius*arithmeticTruncate V ArithmeticFunction.vonMangoldt)
        P S C F + vaughanLongKernel U V P S C F := by
  rw [← normalizedArithmeticKernel_vonMangoldt]
  conv_lhs => rw [vonMangoldt_truncated_identity U V]
  rw [normalizedArithmeticKernel_add,normalizedArithmeticKernel_sub,normalizedArithmeticKernel_add,
    normalizedArithmeticKernel_truncate_zero V ArithmeticFunction.vonMangoldt P S C F hVC,zero_add]
  unfold shortLogPrimeKernel shortZetaPrimeKernel vaughanLongKernel vaughanLongFunction
  rw [arithmeticTruncate_convolution_support]

/-- For fixed U,V the full Mangoldt kernel and its long-divisor term differ
by o(N). This theorem does not claim that either kernel itself is o(N). -/
theorem mangoldtKernel_vaughan_remainder_tendsto (U V : ℕ)
    (P : ℕ → Finset ℕ) (C : ℕ → ℕ) (F : ℕ → ℕ → ℕ) (hC : Tendsto C atTop atTop)
    (hP : ∀ᶠ N in atTop, ∀ p ∈ P N, p.Prime ∧ p≤C N) :
    Tendsto (fun N : ℕ => (mangoldtCutoffSkew (P N) (Icc 1 (N/(C N+1))) (C N) (F N) -
      vaughanLongKernel U V (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N) atTop (𝓝 0) := by
  have ht := (shortLogPrimeKernel_tendsto U P C F hC hP).sub
    (shortZetaPrimeKernel_tendsto (U*V)
      (arithmeticTruncate U ArithmeticFunction.moebius*arithmeticTruncate V ArithmeticFunction.vonMangoldt)
      P C F hC hP)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [hC.eventually (eventually_ge_atTop V)] with N hc
  rw [mangoldtKernel_vaughan_decomposition U V (P N) (Icc 1 (N/(C N+1))) (C N) (F N) hc,
    add_sub_cancel_right,sub_div]

noncomputable def dyadicVaughanLongKernel (U V B C N k : ℕ) : ℝ :=
  vaughanLongKernel U V ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
    (Icc 1 (N/(C+1))) C (fun b => N/dyadicCofactorRound k b)

lemma dyadicMangoldtSkew_vaughan_remainder_tendsto (U V : ℕ) (B C k : ℕ → ℕ)
    (hC : Tendsto C atTop atTop) :
    Tendsto (fun N : ℕ => (dyadicMangoldtSkew (B N) (C N) N (k N)-
      dyadicVaughanLongKernel U V (B N) (C N) N (k N))/N) atTop (𝓝 0) := by
  apply mangoldtKernel_vaughan_remainder_tendsto U V _ C _ hC
  exact Eventually.of_forall fun N p hp =>
    ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.2⟩

/-- In the actual upper-half skew, only the long-divisor kernel remains,
up to the chosen grid error and a term tending to zero. No estimate on the
long-divisor kernel is assumed or proved here. -/
theorem smoothCutoffSkew_vaughan_approximation (U V : ℕ) (B C k : ℕ → ℕ)
    (hC : Tendsto C atTop atTop)
    (hcut : ∀ᶠ N : ℕ in atTop, 2 ≤ B N ∧ B N ≤ C N ∧
      N+N/2^(k N)+2 ≤ (B N)^2) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |smoothCutoffSkew (B N) (C N) N-dyadicVaughanLongKernel U V (B N) (C N) N (k N)|/N ≤
        1/(2 : ℝ)^(k N)+ε := by
  have hr := (dyadicMangoldtSkew_vaughan_remainder_tendsto U V B C k hC).abs
  have ht := ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add
    ((primePowerKernelTail_tendsto.comp hC).const_mul 3)).add hr
  simp only [mul_zero,add_zero,abs_zero] at ht
  have he := Metric.tendsto_nhds.mp ht ε hε
  filter_upwards [hcut,he,eventually_gt_atTop (0 : ℕ)] with N hc he hN
  rw [Real.dist_eq,sub_zero] at he
  have herror : 2/(N : ℝ)+3*primePowerKernelTail (C N)+
      |(dyadicMangoldtSkew (B N) (C N) N (k N)-
        dyadicVaughanLongKernel U V (B N) (C N) N (k N))/N| < ε := by
    exact lt_of_le_of_lt (le_abs_self _) he
  have hround := smoothCutoffSkew_mangoldt_rectangles_ratio (B N) (C N) N (k N)
    hN hc.1 hc.2.1 hc.2.2
  have htri := abs_sub_le (smoothCutoffSkew (B N) (C N) N)
    (dyadicMangoldtSkew (B N) (C N) N (k N))
    (dyadicVaughanLongKernel U V (B N) (C N) N (k N))
  have hd := div_le_div_of_nonneg_right htri (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hd
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ)≤N)] at herror
  linarith

#print axioms shortZetaPrimeKernel_bound
#print axioms shortZetaPrimeKernel_tendsto
#print axioms mangoldtKernel_vaughan_decomposition
#print axioms mangoldtKernel_vaughan_remainder_tendsto
#print axioms smoothCutoffSkew_vaughan_approximation
end Erdos371
