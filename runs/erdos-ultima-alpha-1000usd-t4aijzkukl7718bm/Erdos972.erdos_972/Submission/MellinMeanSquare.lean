import Submission.UniformDivisorCoefficient

/-!
Mean-square bounds on arbitrary finite frequency intervals for finite Mellin
sums. These are energy estimates, not signed prime-pair correlation estimates.
-/
namespace Erdos972MellinMeanSquare

open Finset MeasureTheory
open scoped ComplexConjugate
open Erdos972MellinDivisorCoefficient

set_option maxHeartbeats 1000000

noncomputable def osc (x t : ℝ) : ℂ := Complex.exp ((x : ℂ)*Complex.I*(t : ℂ))
noncomputable def kernel (A B x : ℝ) : ℂ := ∫ t in A..B, osc x t
noncomputable def frequencySum (s : Finset ℕ) (f : ℕ → ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, a n*osc (f n) t
noncomputable def energy (s : Finset ℕ) (a : ℕ → ℂ) : ℝ := ∑ n ∈ s, ‖a n‖^2

lemma norm_osc (x t : ℝ) : ‖osc x t‖ = 1 := by
  have he : (x : ℂ)*Complex.I*(t : ℂ) = Complex.I*((x*t : ℝ) : ℂ) := by push_cast; ring
  rw [osc, he, Complex.norm_exp_I_mul_ofReal]

lemma osc_mul_conj (x y t : ℝ) : osc x t*conj (osc y t) = osc (x-y) t := by
  simp only [osc, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_sub]
  congr 1
  ring

lemma kernel_zero (A B : ℝ) : kernel A B 0 = ((B-A : ℝ) : ℂ) := by
  simp [kernel, osc, intervalIntegral.integral_const, Complex.real_smul]

lemma norm_kernel_le (A B : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ‖kernel A B x‖ ≤ 2/|x| := by
  have hc : (x : ℂ)*Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hx) Complex.I_ne_zero
  unfold kernel osc
  rw [integral_exp_mul_complex hc, norm_div]
  have hh := norm_sub_le (osc x B) (osc x A)
  rw [norm_osc, norm_osc] at hh
  have hd : ‖(x : ℂ)*Complex.I‖ = |x| := by simp [Real.norm_eq_abs]
  rw [hd]
  simpa only [osc, one_add_one_eq_two] using div_le_div_of_nonneg_right hh (abs_nonneg x)

lemma frequencySum_square (s : Finset ℕ) (f : ℕ → ℝ) (a : ℕ → ℂ) (t : ℝ) :
    ((‖frequencySum s f a t‖^2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m*conj (a n))*osc (f m-f n) t := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [frequencySum, map_sum, map_mul, sum_mul_sum]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro n hn
  rw [show (a m*osc (f m) t)*(conj (a n)*conj (osc (f n) t)) =
    (a m*conj (a n))*(osc (f m) t*conj (osc (f n) t)) by ring, osc_mul_conj]

lemma frequencySum_integral_square (s : Finset ℕ) (f : ℕ → ℝ) (a : ℕ → ℂ) (A B : ℝ) :
    ((∫ t in A..B, ‖frequencySum s f a t‖^2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (a m*conj (a n))*kernel A B (f m-f n) := by
  have hi (m n : ℕ) : IntervalIntegrable
      (fun t => (a m*conj (a n))*osc (f m-f n) t) volume A B := by
    apply Continuous.intervalIntegrable
    unfold osc
    fun_prop
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [frequencySum_square]
  rw [intervalIntegral.integral_finset_sum (fun m hm => by
    apply Continuous.intervalIntegrable
    apply continuous_finset_sum s
    intro n hn
    unfold osc
    fun_prop)]
  apply sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_finset_sum (fun n hn => hi m n)]
  simp only [intervalIntegral.integral_const_mul, kernel]

noncomputable def offKernel (f : ℕ → ℝ) (m n : ℕ) : ℝ :=
  if m = n then 0 else 2/|f m-f n|

lemma offKernel_nonneg (f : ℕ → ℝ) (m n : ℕ) : 0 ≤ offKernel f m n := by
  unfold offKernel
  split_ifs <;> positivity

lemma offKernel_symm (f : ℕ → ℝ) (m n : ℕ) : offKernel f m n = offKernel f n m := by
  by_cases h : m = n
  · subst n; rfl
  · simp only [offKernel, if_neg h, if_neg (Ne.symm h), abs_sub_comm]

lemma symmetric_row_bound (s : Finset ℕ) (K : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (C : ℝ)
    (hK : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n)
    (hKs : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
    (hrow : ∀ m ∈ s, (∑ n ∈ s, K m n) ≤ C) :
    (∑ m ∈ s, ∑ n ∈ s, a m*a n*K m n) ≤ C*(∑ m ∈ s, (a m)^2) := by
  have hterm : 2*(∑ m ∈ s, ∑ n ∈ s, a m*a n*K m n) ≤
      ∑ m ∈ s, ∑ n ∈ s, ((a m)^2+(a n)^2)*K m n := by
    simp only [mul_sum]
    apply sum_le_sum
    intro m hm
    apply sum_le_sum
    intro n hn
    have hh := mul_nonneg (sq_nonneg (a m-a n)) (hK m hm n hn)
    nlinarith only [hh]
  have he : (∑ m ∈ s, ∑ n ∈ s, ((a m)^2+(a n)^2)*K m n) =
      2*(∑ m ∈ s, (a m)^2*(∑ n ∈ s, K m n)) := by
    simp only [add_mul, sum_add_distrib]
    have hh : (∑ m ∈ s, ∑ n ∈ s, (a n)^2*K m n) =
        ∑ m ∈ s, ∑ n ∈ s, (a m)^2*K m n := by
      rw [sum_comm]
      apply sum_congr rfl
      intro m hm
      apply sum_congr rfl
      intro n hn
      rw [hKs n hn m hm]
    rw [hh, ← two_mul]
    congr 1
    apply sum_congr rfl
    intro m hm
    rw [mul_sum]
  have hb : (∑ m ∈ s, (a m)^2*(∑ n ∈ s, K m n)) ≤ C*(∑ m ∈ s, (a m)^2) := by
    rw [mul_sum]
    exact sum_le_sum (fun m hm =>
      (mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg (a m))).trans_eq (by ring))
  rw [he] at hterm
  linarith only [hterm, hb]

/-- A two-sided energy discrepancy estimate from bounds on the off-diagonal
Gram-matrix rows. The interval endpoints may grow without restriction. -/
theorem frequencySum_mean_square (s : Finset ℕ) (f : ℕ → ℝ) (a : ℕ → ℂ) (A B C : ℝ)
    (hf : Set.InjOn f (s : Set ℕ))
    (hrow : ∀ m ∈ s, (∑ n ∈ s, offKernel f m n) ≤ C) :
    |(∫ t in A..B, ‖frequencySum s f a t‖^2) - (B-A)*energy s a| ≤ C*energy s a := by
  let H : ℕ → ℕ → ℂ := fun m n => (a m*conj (a n))*kernel A B (f m-f n)
  have hd (m : ℕ) : H m m = (((B-A)*‖a m‖^2 : ℝ) : ℂ) := by
    dsimp [H]
    rw [sub_self, kernel_zero, Complex.mul_conj']
    push_cast
    ring
  have he : ((∫ t in A..B, ‖frequencySum s f a t‖^2 : ℝ) : ℂ) -
      (((B-A)*energy s a : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, (if m = n then 0 else H m n) := by
    rw [frequencySum_integral_square]
    change (∑ m ∈ s, ∑ n ∈ s, H m n) - _ = _
    have hs : (((B-A)*energy s a : ℝ) : ℂ) = ∑ m ∈ s, H m m := by
      simp only [hd, energy, mul_sum, Complex.ofReal_sum]
    rw [hs, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    have hh : (∑ n ∈ s, H m n) = H m m + ∑ n ∈ s, (if m = n then 0 else H m n) := by
      have ht := sum_add_distrib (s := s) (f := fun n => if m = n then H m n else 0)
        (g := fun n => if m = n then 0 else H m n)
      simp only [sum_ite_eq, if_pos hm] at ht
      rw [← ht]
      apply sum_congr rfl
      intro n hn
      split_ifs <;> simp
    rw [hh]
    abel
  have hb : ‖∑ m ∈ s, ∑ n ∈ s, (if m = n then 0 else H m n)‖ ≤
      ∑ m ∈ s, ∑ n ∈ s, ‖a m‖*‖a n‖*offKernel f m n := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro m hm
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro n hn
    by_cases hmn : m = n
    · simp [hmn, offKernel]
    · simp only [if_neg hmn, H, norm_mul, Complex.norm_conj, offKernel]
      apply mul_le_mul_of_nonneg_left
        (norm_kernel_le A B (sub_ne_zero.mpr (fun h => hmn (hf hm hn h))))
        (by positivity)
  have hs := symmetric_row_bound s (offKernel f) (fun m => ‖a m‖) C
    (fun m hm n hn => offKernel_nonneg f m n)
    (fun m hm n hn => offKernel_symm f m n) hrow
  have hh := hb.trans hs
  rw [← he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh

lemma sum_reciprocal_Icc (N : ℕ) :
    (∑ d ∈ Icc 0 N, 1/(d : ℝ)) = (harmonic N : ℝ) := by
  rw [← sum_Ioc_add_eq_sum_Icc (f := fun d : ℕ => 1/(d : ℝ)) (Nat.zero_le N)]
  simp only [Nat.cast_zero, div_zero, add_zero]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rfl

lemma nat_dist_le (m n N : ℕ) (hm : m ≤ N) (hn : n ≤ N) : m.dist n ≤ N := by
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    omega

lemma distance_sum_of_injective (s : Finset ℕ) {m N : ℕ} (hm : m ≤ N)
    (hs : s ⊆ Icc 0 N) (hi : Set.InjOn (Nat.dist m) (s : Set ℕ)) :
    (∑ n ∈ s, 1/(m.dist n : ℝ)) ≤ (harmonic N : ℝ) := by
  rw [← sum_image (f := fun d : ℕ => 1/(d : ℝ)) hi, ← sum_reciprocal_Icc]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨Nat.zero_le _, nat_dist_le m n N hm (mem_Icc.mp (hs hn)).2⟩
  · intro d hd hnot
    positivity

lemma reciprocal_distance_row (m N : ℕ) (hm : m ≤ N) :
    (∑ n ∈ Ioc 0 N, 1/(m.dist n : ℝ)) ≤ 2*(harmonic N : ℝ) := by
  have hlo := distance_sum_of_injective ((Ioc 0 N).filter (fun n => n ≤ m)) hm
    (by intro n hn; exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp (mem_filter.mp hn).1).2⟩)
    (by
      intro i hi j hj he
      simp only [Finset.mem_coe, mem_filter] at hi hj
      have hi' := hi.2
      have hj' := hj.2
      rw [Nat.dist_eq_sub_of_le_right hi', Nat.dist_eq_sub_of_le_right hj'] at he
      omega)
  have hhi := distance_sum_of_injective ((Ioc 0 N).filter (fun n => ¬ n ≤ m)) hm
    (by intro n hn; exact mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp (mem_filter.mp hn).1).2⟩)
    (by
      intro i hi j hj he
      simp only [Finset.mem_coe, mem_filter] at hi hj
      have hi' : m ≤ i := by have := hi.2; omega
      have hj' : m ≤ j := by have := hj.2; omega
      rw [Nat.dist_eq_sub_of_le hi', Nat.dist_eq_sub_of_le hj'] at he
      omega)
  have he := sum_filter_add_sum_filter_not (Ioc 0 N) (fun n => n ≤ m)
    (fun n => 1/(m.dist n : ℝ))
  linarith only [hlo, hhi, he]

lemma log_gap_lower_of_le {x y C : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyC : y ≤ C) :
    y-x ≤ C*(Real.log y-Real.log x) := by
  have hy : 0 < y := hx.trans_le hxy
  have hh := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hh
  have hm := mul_le_mul_of_nonneg_right hh hy.le
  have he : (x/y-1)*y = x-y := by field_simp
  rw [he] at hm
  have hl : 0 ≤ Real.log y-Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy)
  have hc := mul_le_mul_of_nonneg_right hyC hl
  nlinarith only [hm, hc]

lemma nat_log_gap {N m n : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    (m.dist n : ℝ) ≤ (N : ℝ)*|Real.log m-Real.log n| := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (mem_Ioc.mp hm).1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Ioc.mp hn).1
  rcases le_total m n with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hm0 (Nat.cast_le.mpr h)))]
    exact log_gap_lower_of_le hm0 (Nat.cast_le.mpr h) (Nat.cast_le.mpr (mem_Ioc.mp hn).2)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 (Nat.cast_le.mpr h)))]
    exact log_gap_lower_of_le hn0 (Nat.cast_le.mpr h) (Nat.cast_le.mpr (mem_Ioc.mp hm).2)

lemma log_nat_injective (N : ℕ) : Set.InjOn (fun n : ℕ => Real.log n) (Ioc 0 N : Set ℕ) := by
  intro m hm n hn he
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (mem_Ioc.mp hm).1
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Ioc.mp hn).1
  exact Nat.cast_injective (Real.log_injOn_pos hm0 hn0 he)

lemma log_offKernel_bound {N m n : ℕ} (hm : m ∈ Ioc 0 N) (hn : n ∈ Ioc 0 N) :
    offKernel (fun k : ℕ => Real.log k) m n ≤ 2*(N : ℝ)/(m.dist n : ℝ) := by
  by_cases hmn : m = n
  · simp [hmn, offKernel]
  have hd : 0 < m.dist n := by
    rcases le_total m n with h | h
    · rw [Nat.dist_eq_sub_of_le h]; omega
    · rw [Nat.dist_eq_sub_of_le_right h]; omega
  have hlog : Real.log (m : ℝ) ≠ Real.log n := fun he => hmn (log_nat_injective N hm hn he)
  have hlog0 : 0 < |Real.log (m : ℝ)-Real.log n| := abs_pos.mpr (sub_ne_zero.mpr hlog)
  simp only [offKernel, if_neg hmn]
  apply (div_le_div_iff₀ hlog0 (Nat.cast_pos.mpr hd)).mpr
  have hh := nat_log_gap hm hn
  nlinarith only [hh]

lemma log_offKernel_row {N m : ℕ} (hm : m ∈ Ioc 0 N) :
    (∑ n ∈ Ioc 0 N, offKernel (fun k : ℕ => Real.log k) m n) ≤
      4*(N : ℝ)*(1+Real.log N) := by
  have hd := reciprocal_distance_row m N (mem_Ioc.mp hm).2
  have hH := harmonic_le_one_add_log N
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, 2*(N : ℝ)/(m.dist n : ℝ) :=
      sum_le_sum (fun n hn => log_offKernel_bound hm hn)
    _ = 2*(N : ℝ)*(∑ n ∈ Ioc 0 N, 1/(m.dist n : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ 2*(N : ℝ)*(2*(harmonic N : ℝ)) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ 4*(N : ℝ)*(1+Real.log N) := by
      have hh := mul_le_mul_of_nonneg_left hH (show 0 ≤ 4*(N : ℝ) by positivity)
      nlinarith only [hh]

lemma osc_log_eq_mellinPhase (n : ℕ) (t : ℝ) : osc (Real.log n) t = mellinPhase t n := by
  unfold osc mellinPhase
  congr 1
  push_cast
  ring

/-- A finite Mellin mean-square estimate with an explicit logarithmic
spacing error, uniform in both endpoints of the frequency interval. -/
theorem mellin_mean_square {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N)
    (a : ℕ → ℂ) (A B : ℝ) :
    |(∫ t in A..B, ‖∑ n ∈ s, a n*mellinPhase t n‖^2) - (B-A)*energy s a| ≤
      4*(N : ℝ)*(1+Real.log N)*energy s a := by
  have hh := frequencySum_mean_square s (fun n : ℕ => Real.log n) a A B
    (4*(N : ℝ)*(1+Real.log N))
    (fun m hm n hn he => log_nat_injective N (hs hm) (hs hn) he)
    (fun m hm => (sum_le_sum_of_subset_of_nonneg hs
      (fun n hn hnot => offKernel_nonneg (fun k : ℕ => Real.log k) m n)).trans (log_offKernel_row (hs hm)))
  simpa only [frequencySum, osc_log_eq_mellinPhase] using hh

lemma energy_nonneg (s : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ energy s a :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma actual_divisorCoeff_energy {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N) (U : ℕ) :
    energy s (fun n => (divisorCoeff U n : ℂ)) ≤ (N : ℝ)*(1+Real.log N)^3 := by
  have hp (n : ℕ) : ‖(divisorCoeff U n : ℂ)‖^2 ≤ (n.divisors.card : ℝ)^2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Erdos972Vaughan.abs_typeII_coefficient_le_card_divisors U n) 2
  apply (sum_le_sum (fun n hn => hp n)).trans
  apply (sum_le_sum_of_subset_of_nonneg hs (fun n hn hnot => sq_nonneg _)).trans
  exact Erdos972DivisorEnergy.sum_card_divisors_square_le_log N

/-- The logarithmic mean-square estimate applies to the genuine coefficient
on every frequency interval, without a bounded-frequency restriction. -/
theorem actual_divisorCoeff_mean_square {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N)
    (U : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t in A..B, ‖∑ n ∈ s, (divisorCoeff U n : ℂ)*mellinPhase t n‖^2) ≤
      (B-A+4*(N : ℝ)*(1+Real.log N))*((N : ℝ)*(1+Real.log N)^3) := by
  have hh := mellin_mean_square s hs (fun n => (divisorCoeff U n : ℂ)) A B
  have he := actual_divisorCoeff_energy s hs U
  have hC : 0 ≤ B-A+4*(N : ℝ)*(1+Real.log N) := by
    have hlog := Real.log_natCast_nonneg N
    have hBA : 0 ≤ B-A := sub_nonneg.mpr hAB
    positivity
  have hb := mul_le_mul_of_nonneg_left he hC
  have hi := (abs_le.mp hh).2
  nlinarith only [hi, hb]

/-- The same estimate on a dyadic block, with all parameter dependence shown. -/
theorem dyadic_divisorCoeff_mean_square (U M : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t in A..B, ‖∑ n ∈ Ioc M (2*M), (divisorCoeff U n : ℂ)*mellinPhase t n‖^2) ≤
      (B-A+8*(M : ℝ)*(1+Real.log (2*M : ℕ)))*
        (2*(M : ℝ)*(1+Real.log (2*M : ℕ))^3) := by
  have hh := actual_divisorCoeff_mean_square (Ioc M (2*M))
    (Ioc_subset_Ioc (Nat.zero_le M) le_rfl) U hAB
  convert hh using 1
  push_cast
  ring

lemma vonMangoldt_energy {N : ℕ} (s : Finset ℕ) (hs : s ⊆ Ioc 0 N) :
    energy s (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤
      Real.log N * Chebyshev.psi N := by
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hp (n : ℕ) (hn : n ∈ Ioc 0 N) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖^2 ≤
        Real.log N * ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hh := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hn).1)
      (Nat.cast_le.mpr (mem_Ioc.mp hn).2)
    have hm := mul_le_mul_of_nonneg_right (hh.trans hlog) (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    nlinarith only [hm]
  apply (sum_le_sum (fun n hn => hp n (hs hn))).trans
  apply (sum_le_sum_of_subset_of_nonneg hs
    (fun n hn hnot => mul_nonneg hlogN ArithmeticFunction.vonMangoldt_nonneg)).trans_eq
  simp only [Chebyshev.psi, Nat.floor_natCast, mul_sum]

#print axioms frequencySum_mean_square
#print axioms mellin_mean_square
#print axioms actual_divisorCoeff_mean_square
#print axioms dyadic_divisorCoeff_mean_square
#print axioms vonMangoldt_energy

end Erdos972MellinMeanSquare
