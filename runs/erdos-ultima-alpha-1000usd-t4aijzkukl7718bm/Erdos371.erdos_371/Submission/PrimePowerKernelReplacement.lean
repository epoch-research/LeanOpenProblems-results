import Submission.DyadicPrimeSkewRectangles

/-! Higher prime powers can be removed from the full upper-half cofactor
kernel with a uniform natural-scale error. The remaining Mangoldt-weighted
prime-character sums are not estimated here. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def mangoldtPrimeWeight (q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q / Real.log q

noncomputable def properPrimePowerWeight (q : ℕ) : ℝ :=
  if q.Prime then 0 else mangoldtPrimeWeight q

lemma mangoldtPrimeWeight_nonneg (q : ℕ) : 0 ≤ mangoldtPrimeWeight q :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg q)

lemma properPrimePowerWeight_nonneg (q : ℕ) : 0 ≤ properPrimePowerWeight q := by
  unfold properPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact mangoldtPrimeWeight_nonneg q

lemma mangoldtPrimeWeight_split (q : ℕ) :
    mangoldtPrimeWeight q = (if q.Prime then 1 else 0) + properPrimePowerWeight q := by
  by_cases hq : q.Prime
  · have hl : Real.log q ≠ 0 := (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
    simp [mangoldtPrimeWeight,properPrimePowerWeight,hq,
      ArithmeticFunction.vonMangoldt_apply_prime hq,hl]
  · simp [properPrimePowerWeight,hq]

lemma mangoldtPrimeWeight_le_twice (q : ℕ) :
    mangoldtPrimeWeight q ≤ 2*ArithmeticFunction.vonMangoldt q := by
  by_cases hq : q ≤ 1
  · interval_cases q <;> simp [mangoldtPrimeWeight]
  · have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
    have hlog : 1/2 < Real.log q :=
      (by linarith [Real.log_two_gt_d9] : (1/2 : ℝ) < Real.log 2).trans_le
        (Real.log_le_log (by norm_num) hq2)
    unfold mangoldtPrimeWeight
    apply (div_le_iff₀ (by linarith : 0 < Real.log q)).mpr
    have hm := mul_le_mul_of_nonneg_left hlog.le
      (ArithmeticFunction.vonMangoldt_nonneg (n := q))
    nlinarith

lemma properPrimePowerWeight_reciprocal_summable :
    Summable (fun q : ℕ => properPrimePowerWeight q / q) := by
  have hs : Summable (fun q : ℕ =>
      (if q.Prime then 0 else ArithmeticFunction.vonMangoldt q)/q) := by
    have hs := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
    have he (q : ℕ) : ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) q =
        ArithmeticFunction.vonMangoldt q := by
      have hq : (q : ZMod 1)=0 := Subsingleton.elim _ _
      simp [ArithmeticFunction.vonMangoldt.residueClass,hq]
    simpa only [he] using hs
  apply (hs.mul_left 2).of_nonneg_of_le (fun q =>
    div_nonneg (properPrimePowerWeight_nonneg q) (Nat.cast_nonneg q))
  intro q
  by_cases hq : q.Prime
  · simp [properPrimePowerWeight,hq]
  · simp only [properPrimePowerWeight,if_neg hq]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
      (mangoldtPrimeWeight_le_twice q) (Nat.cast_nonneg (α := ℝ) q)

noncomputable def primePowerKernelTail (C : ℕ) : ℝ :=
  (∑' q : ℕ, properPrimePowerWeight q/q) -
    ∑ q ∈ range (C+1), properPrimePowerWeight q/q

lemma primePowerKernelTail_nonneg (C : ℕ) : 0 ≤ primePowerKernelTail C := by
  apply sub_nonneg.mpr
  exact properPrimePowerWeight_reciprocal_summable.sum_le_tsum _
    (fun q _ => div_nonneg (properPrimePowerWeight_nonneg q) (Nat.cast_nonneg q))

lemma primePowerKernelTail_tendsto : Tendsto primePowerKernelTail atTop (𝓝 0) := by
  have hs := properPrimePowerWeight_reciprocal_summable.tendsto_sum_tsum_nat.comp
    (tendsto_add_atTop_nat 1)
  have ht := (tendsto_const_nhds (x := ∑' q : ℕ, properPrimePowerWeight q/q)).sub hs
  simpa only [primePowerKernelTail,sub_self,Function.comp_apply] using ht

lemma primePowerKernelTail_interval_bound (C M : ℕ) :
    (∑ q ∈ Ioc C M, properPrimePowerWeight q/q) ≤ primePowerKernelTail C := by
  have hd : Disjoint (range (C+1)) (Ioc C M) := by
    apply disjoint_left.mpr
    intro q hq hq'
    have := mem_range.mp hq
    have := mem_Ioc.mp hq'
    omega
  have hs := properPrimePowerWeight_reciprocal_summable.sum_le_tsum
    (range (C+1) ∪ Ioc C M)
    (fun q _ => div_nonneg (properPrimePowerWeight_nonneg q) (Nat.cast_nonneg q))
  rw [sum_union hd] at hs
  unfold primePowerKernelTail
  linarith

noncomputable def weightedOppositeKernel (P S : Finset ℕ) (C : ℕ)
    (F : ℕ → ℕ) (w : ℕ → ℝ) (s : Bool) : ℝ :=
  ∑ p ∈ P, ∑ b ∈ S, ∑ q ∈ Ioc C (F b),
    w q * (if p ∣ (if s then b*q-1 else b*q+1) then 1 else 0)

lemma weightedOppositeKernel_add (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ)
    (w v : ℕ → ℝ) (s : Bool) :
    weightedOppositeKernel P S C F (fun q => w q+v q) s =
      weightedOppositeKernel P S C F w s + weightedOppositeKernel P S C F v s := by
  simp only [weightedOppositeKernel,add_mul,sum_add_distrib]

lemma weightedOppositeKernel_prime (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) (s : Bool) :
    weightedOppositeKernel P S C F (fun q => if q.Prime then 1 else 0) s =
      ∑ p ∈ P, ∑ b ∈ S, (oppositePrimeCount C (F b) p b s : ℝ) := by
  unfold weightedOppositeKernel oppositePrimeCount
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro b hb
  have he (q : ℕ) : (if q.Prime then (1 : ℝ) else 0) *
      (if p ∣ (if s then b*q-1 else b*q+1) then 1 else 0) =
      if q.Prime ∧ p ∣ (if s then b*q-1 else b*q+1) then 1 else 0 := by
    split_ifs <;> simp_all
  simp only [he,sum_boole]

private lemma large_prime_divisor_sum_le_one (P : Finset ℕ) (B n : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ B<p) (hn : 0 < n) (hsize : n ≤ B^2) :
    (∑ p ∈ P, if p ∣ n then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_boole]
  have hc : (P.filter fun p => p ∣ n).card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨hpP,hpd⟩ := mem_filter.mp hp
    obtain ⟨hqP,hqd⟩ := mem_filter.mp hq
    exact prime_dvd_unique_above_sqrt B n p q hn hsize
      (hP p hpP).1 (hP q hqP).1 (hP p hpP).2 (hP q hqP).2 hpd hqd
  exact_mod_cast hc

private lemma cofactor_weighted_mass_bound (S : Finset ℕ) (C M : ℕ)
    (F : ℕ → ℕ) (w : ℕ → ℝ) (hS : ∀ b ∈ S, 0 < b)
    (hF : ∀ b ∈ S, b*F b ≤ M) (hw : ∀ q, 0 ≤ w q) :
    (∑ b ∈ S, ∑ q ∈ Ioc C (F b), w q) ≤ M * ∑ q ∈ Ioc C M, w q/q := by
  have hFM (b : ℕ) (hb : b ∈ S) : F b ≤ M := by
    have := hS b hb
    have := hF b hb
    nlinarith
  have he (b : ℕ) (hb : b ∈ S) :
      (∑ q ∈ Ioc C (F b), w q) = ∑ q ∈ Ioc C M, if q ≤ F b then w q else 0 := by
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext q
    simp only [mem_Ioc,mem_filter]
    have := hFM b hb
    omega
  rw [sum_congr rfl he,sum_comm,mul_sum]
  apply sum_le_sum
  intro q hq
  have hq0 : 0 < q := by have := (mem_Ioc.mp hq).1; omega
  have hsub : S.filter (fun b => q ≤ F b) ⊆ Icc 1 (M/q) := by
    intro b hb
    obtain ⟨hb,hqF⟩ := mem_filter.mp hb
    apply mem_Icc.mpr
    refine ⟨hS b hb,(Nat.le_div_iff_mul_le hq0).mpr ?_⟩
    exact (Nat.mul_le_mul_left b hqF).trans (hF b hb)
  have hc := card_le_card hsub
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hc
  rw [← sum_filter,sum_const,nsmul_eq_mul]
  calc
    _ ≤ (M/q : ℕ) * w q := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hw q)
    _ ≤ ((M : ℝ)/q)*w q := mul_le_mul_of_nonneg_right (Nat.cast_div_le (α := ℝ)) (hw q)
    _ = _ := by ring

/-- A uniform total bound for any nonnegative cofactor weight. Only the
large prime in P needs uniqueness; q is not assumed prime here. -/
theorem weightedOppositeKernel_bounds (P S : Finset ℕ) (B C M : ℕ)
    (F : ℕ → ℕ) (w : ℕ → ℝ) (s : Bool) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B<p) (hS : ∀ b ∈ S, 0 < b)
    (hF : ∀ b ∈ S, b*F b ≤ M) (hw : ∀ q, 0 ≤ w q) (hsize : M+1 ≤ B^2) :
    0 ≤ weightedOppositeKernel P S C F w s ∧
      weightedOppositeKernel P S C F w s ≤ M * ∑ q ∈ Ioc C M, w q/q := by
  constructor
  · unfold weightedOppositeKernel
    exact sum_nonneg fun p _ => sum_nonneg fun b _ => sum_nonneg fun q _ =>
      mul_nonneg (hw q) (by split_ifs <;> norm_num)
  · apply le_trans _ (cofactor_weighted_mass_bound S C M F w hS hF hw)
    unfold weightedOppositeKernel
    rw [sum_comm]
    apply sum_le_sum
    intro b hb
    rw [sum_comm]
    apply sum_le_sum
    intro q hq
    rw [← mul_sum]
    have hqF := (mem_Ioc.mp hq).2
    have hqC := (mem_Ioc.mp hq).1
    have hb0 := hS b hb
    have hbM := (Nat.mul_le_mul_left b hqF).trans (hF b hb)
    have hbq : 1 < b*q := by nlinarith
    have hn0 : 0 < if s then b*q-1 else b*q+1 := by
      cases s <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
    have hnsize : (if s then b*q-1 else b*q+1) ≤ B^2 := by
      cases s <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
    exact mul_le_of_le_one_right (hw q)
      (large_prime_divisor_sum_le_one P B _ hP hn0 hnsize)

noncomputable def mangoldtCutoffSkew (P S : Finset ℕ) (C : ℕ) (F : ℕ → ℕ) : ℝ :=
  weightedOppositeKernel P S C F mangoldtPrimeWeight true -
    weightedOppositeKernel P S C F mangoldtPrimeWeight false

/-- Higher prime powers have a global summable-tail error, with no loss for
the number of moduli or cofactor blocks. -/
theorem mangoldtCutoffSkew_prime_error (P S : Finset ℕ) (B C M : ℕ)
    (F : ℕ → ℕ) (hB : 2 ≤ B) (hBC : B ≤ C)
    (hP : ∀ p ∈ P, p.Prime ∧ B<p) (hS : ∀ b ∈ S, 0 < b)
    (hF : ∀ b ∈ S, b*F b ≤ M) (hsize : M+1 ≤ B^2) :
    |mangoldtCutoffSkew P S C F - cutoffPrimeSkew P S C F| ≤ M*primePowerKernelTail C := by
  have hsplit : mangoldtPrimeWeight = fun q => (if q.Prime then 1 else 0)+properPrimePowerWeight q :=
    funext mangoldtPrimeWeight_split
  have he (s : Bool) := weightedOppositeKernel_bounds P S B C M F properPrimePowerWeight s
    hB hBC hP hS hF properPrimePowerWeight_nonneg hsize
  have htail := mul_le_mul_of_nonneg_left (primePowerKernelTail_interval_bound C M)
    (Nat.cast_nonneg (α := ℝ) M)
  simp only [mangoldtCutoffSkew,hsplit,weightedOppositeKernel_add,
    weightedOppositeKernel_prime,cutoffPrimeSkew,sum_sub_distrib]
  rw [abs_le]
  constructor <;> linarith [(he true).1,(he true).2,(he false).1,(he false).2]

noncomputable def dyadicMangoldtSkew (B C N k : ℕ) : ℝ :=
  mangoldtCutoffSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
    (Icc 1 (N/(C+1))) C (fun b => N/dyadicCofactorRound k b)

/-- The Mangoldt replacement error for the dyadic kernel is uniform even
in the grid precision k. -/
theorem dyadicMangoldtSkew_prime_ratio (B C N k : ℕ) (hN : 0 < N)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hsize : N+N/2^k+2 ≤ B^2) :
    |dyadicMangoldtSkew B C N k -
      roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
        (Icc 1 (N/(C+1))) C N (dyadicCofactorRound k)|/N ≤ 3*primePowerKernelTail C := by
  rw [roundedPrimeSkew_eq_cutoff]
  have h := mangoldtCutoffSkew_prime_error
    ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
    (Icc 1 (N/(C+1))) B C (N+N/2^k+1) (fun b => N/dyadicCofactorRound k b)
    hB hBC (fun p hp => ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.1⟩)
    (fun b hb => (mem_Icc.mp hb).1) (fun b hb => ?_) (by omega)
  · have hM : N+N/2^k+1 ≤ 3*N := by
      have hd := Nat.div_le_self N (2^k)
      omega
    have hM' : ((N+N/2^k+1 : ℕ) : ℝ) ≤ 3*(N : ℝ) := by exact_mod_cast hM
    have ht := mul_le_mul_of_nonneg_right hM' (primePowerKernelTail_nonneg C)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    apply (div_le_iff₀ hN0).mpr
    change |mangoldtCutoffSkew _ _ _ _ - cutoffPrimeSkew _ _ _ _| ≤ _
    exact (h.trans ht).trans_eq (by ring)
  · have hb' := dyadicCofactorRound_bounds k b (mem_Icc.mp hb).1
    exact (rounded_prime_endpoint_bounds N (N+N/2^k+1) b (dyadicCofactorRound k b)
      hb'.1 hb'.2 (dyadicCofactorRound_cross k N b)).2

/-- A natural-scale bound directly against the Mangoldt-weighted dyadic
kernel. No estimate on that kernel itself has been assumed. -/
theorem smoothCutoffSkew_mangoldt_rectangles_ratio (B C N k : ℕ) (hN : 0 < N)
    (hB : 2 ≤ B) (hBC : B ≤ C) (hsize : N+N/2^k+2 ≤ B^2) :
    |smoothCutoffSkew B C N-dyadicMangoldtSkew B C N k|/N ≤
      1/(2 : ℝ)^k+2/N+3*primePowerKernelTail C := by
  have hr := smoothCutoffSkew_dyadic_rounding_ratio B C N k hN hB hBC hsize
  have hm := dyadicMangoldtSkew_prime_ratio B C N k hN hB hBC hsize
  have ht := abs_sub_le (smoothCutoffSkew B C N)
    (roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B<p ∧ p≤C)
      (Icc 1 (N/(C+1))) C N (dyadicCofactorRound k))
    (dyadicMangoldtSkew B C N k)
  rw [abs_sub_comm (dyadicMangoldtSkew B C N k)] at hm
  have hh := div_le_div_of_nonneg_right ht (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hh
  exact hh.trans (add_le_add hr hm)

/-- Higher-prime-power replacement is negligible along any moving cutoffs
satisfying the upper-half condition. The grid precision may also vary. -/
theorem dyadicMangoldtSkew_replacement_tendsto (B C k : ℕ → ℕ)
    (hC : Tendsto C atTop atTop)
    (hcut : ∀ᶠ N : ℕ in atTop, 2 ≤ B N ∧ B N ≤ C N ∧
      N+N/2^(k N)+2 ≤ (B N)^2) :
    Tendsto (fun N : ℕ => (dyadicMangoldtSkew (B N) (C N) N (k N) -
      roundedPrimeSkew ((range (N+2)).filter fun p => p.Prime ∧ B N<p ∧ p≤C N)
        (Icc 1 (N/(C N+1))) (C N) N (dyadicCofactorRound (k N)))/N)
      atTop (𝓝 0) := by
  have ht := (primePowerKernelTail_tendsto.comp hC).const_mul 3
  simp only [mul_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hcut,eventually_gt_atTop (0 : ℕ)] with N hc hN
  rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
  exact dyadicMangoldtSkew_prime_ratio (B N) (C N) N (k N) hN hc.1 hc.2.1 hc.2.2

#print axioms properPrimePowerWeight_reciprocal_summable
#print axioms primePowerKernelTail_tendsto
#print axioms weightedOppositeKernel_bounds
#print axioms mangoldtCutoffSkew_prime_error
#print axioms smoothCutoffSkew_mangoldt_rectangles_ratio
#print axioms dyadicMangoldtSkew_replacement_tendsto
end Erdos371
