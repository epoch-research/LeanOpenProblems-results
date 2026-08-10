import Mathlib
open Finset BigOperators
open scoped ArithmeticFunction.vonMangoldt

noncomputable def T (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 N, Real.log k

/-- Log-factorial identity: T(N) = ∑_{d≤N} Λ(d) * ⌊N/d⌋. -/
theorem T_eq (N : ℕ) :
    T N = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  unfold T
  -- log k = ∑_{d ∈ k.divisors} Λ d
  have h1 : ∀ k ∈ Finset.Icc 1 N, Real.log k
      = ∑ d ∈ Finset.Icc 1 N, (if d ∣ k then ArithmeticFunction.vonMangoldt d else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← ArithmeticFunction.vonMangoldt_sum (n := k)]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hkne⟩
      have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hd; omega)
      have hdk : d ≤ k := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨hd1, by omega⟩, hd⟩
    · rintro ⟨⟨hd1, hdN⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- #{k ∈ Icc 1 N | d ∣ k} = N / d
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    apply Finset.ext; intro x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  norm_cast
  exact Nat.Ioc_filter_dvd_card_eq_div N d

theorem T_eq_range (N : ℕ) : T N = ∑ i ∈ Finset.range N, Real.log (1 + (i : ℝ)) := by
  unfold T
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N+1) by
    apply Finset.ext; intro x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_add, Nat.cast_one, add_comm]

theorem log_monotoneOn (a b : ℝ) (ha : 1 ≤ a) : MonotoneOn Real.log (Set.Icc a b) := by
  intro x hx y hy hxy
  exact Real.log_le_log (by linarith [hx.1]) hxy

/-- Upper bound on log(N!). -/
theorem T_upper (N : ℕ) : T N ≤ ((N:ℝ) + 1) * Real.log (N + 1) - N := by
  rw [T_eq_range]
  have h := MonotoneOn.sum_le_integral (f := Real.log) (x₀ := 1) (a := N)
    (log_monotoneOn 1 (1 + (N:ℝ)) le_rfl)
  rw [integral_log] at h
  simp only [Real.log_one, mul_zero, sub_zero] at h
  calc ∑ i ∈ Finset.range N, Real.log (1 + (i : ℝ))
      ≤ (1 + (N:ℝ)) * Real.log (1 + N) - (1 + N) + 1 := h
    _ = ((N:ℝ) + 1) * Real.log (N + 1) - N := by ring_nf

/-- Lower bound on log(N!). -/
theorem T_lower (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) * Real.log N - N + 1 ≤ T N := by
  rw [T_eq_range]
  have h := MonotoneOn.integral_le_sum (f := Real.log) (x₀ := 1) (a := N - 1)
    (log_monotoneOn 1 (1 + ((N-1 : ℕ) : ℝ)) le_rfl)
  rw [integral_log] at h
  simp only [Real.log_one, mul_zero, sub_zero] at h
  -- h : ∫ = (1+(N-1))*log(1+(N-1)) - (1+(N-1)) + 1 ≤ ∑ i in range (N-1), log(1+(i+1))
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN, Nat.cast_one]
  rw [hN1] at h
  have hsum : ∑ i ∈ Finset.range N, Real.log (1 + (i:ℝ))
      = ∑ i ∈ Finset.range (N-1), Real.log (1 + ((i+1:ℕ):ℝ)) := by
    conv_lhs => rw [show N = (N-1) + 1 by omega, Finset.sum_range_succ']
    simp [Real.log_one]
  have hNe : (1 : ℝ) + ((N:ℝ) - 1) = (N:ℝ) := by ring
  rw [hNe] at h
  rw [hsum]
  linarith [h]

/-- Chebyshev combination coefficient. -/
def Ccoef (t : ℕ) : ℕ := (t + t / 30) - (t / 2 + t / 3 + t / 5)

theorem Ccoef_periodic (t : ℕ) : Ccoef (t + 30) = Ccoef t := by
  unfold Ccoef
  have h2 : (t + 30) / 2 = t / 2 + 15 := by omega
  have h3 : (t + 30) / 3 = t / 3 + 10 := by omega
  have h5 : (t + 30) / 5 = t / 5 + 6 := by omega
  have h30 : (t + 30) / 30 = t / 30 + 1 := by omega
  rw [h2, h3, h5, h30]; omega

theorem Ccoef_le_one (t : ℕ) : Ccoef t ≤ 1 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases lt_or_ge t 30 with h | h
    · interval_cases t <;> decide
    · have key := Ccoef_periodic (t - 30)
      rw [show t - 30 + 30 = t by omega] at key
      rw [key]; exact ih (t - 30) (by omega)

theorem Ccoef_eq_one_small (t : ℕ) (h1 : 1 ≤ t) (h5 : t ≤ 5) : Ccoef t = 1 := by
  interval_cases t <;> decide

theorem Ccoef_ge (t : ℕ) : t / 2 + t / 3 + t / 5 ≤ t + t / 30 := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases lt_or_ge t 30 with h | h
    · interval_cases t <;> decide
    · have h2 : t / 2 = (t - 30) / 2 + 15 := by omega
      have h3 : t / 3 = (t - 30) / 3 + 10 := by omega
      have h5 : t / 5 = (t - 30) / 5 + 6 := by omega
      have h30 : t / 30 = (t - 30) / 30 + 1 := by omega
      have := ih (t - 30) (by omega)
      omega

/-- Real cast of the coefficient equals the floor combination. -/
theorem Ccoef_cast (t : ℕ) :
    ((Ccoef t : ℕ) : ℝ) = (t : ℝ) - (t / 2 : ℕ) - (t / 3 : ℕ) - (t / 5 : ℕ) + (t / 30 : ℕ) := by
  unfold Ccoef
  rw [Nat.cast_sub (Ccoef_ge t)]
  push_cast
  ring

noncomputable def psiN (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d

/-- The set of prime powers of `p` up to `N`, characterised as an image. -/
theorem fiber_eq_image (N p : ℕ) (hp : p.Prime) :
    (Finset.Icc 1 N).filter (fun d => d.minFac = p ∧ IsPrimePow d)
      = (Finset.Icc 1 (Nat.log p N)).image (fun k => p ^ k) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hd1, hdN⟩, hmf, hpp⟩
    obtain ⟨q, k, hq, hk, rfl⟩ := hpp
    have hqn : q.Prime := hq.nat_prime
    have hmfq : (q ^ k).minFac = q := Nat.Prime.pow_minFac hqn (by omega)
    have hqp : q = p := by rw [← hmfq]; exact hmf
    subst hqp
    refine ⟨k, ⟨by omega, ?_⟩, rfl⟩
    exact (Nat.le_log_iff_pow_le hqn.one_lt (by omega)).mpr hdN
  · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
    have hN0 : N ≠ 0 := by rintro rfl; rw [Nat.log_zero_right] at hkN; omega
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.pos.ne'), ?_⟩,
      Nat.Prime.pow_minFac hp (by omega), ⟨p, k, hp.prime, by omega, rfl⟩⟩
    calc p ^ k ≤ p ^ Nat.log p N := Nat.pow_le_pow_right hp.pos hkN
      _ ≤ N := Nat.pow_log_le_self p hN0

/-- Chebyshev-type: ψ(N) ≤ π(N)·log N (self-contained via grouping prime powers by prime). -/
theorem psi_le_pc_logN (N : ℕ) (hN : 2 ≤ N) :
    psiN N ≤ (((Finset.Icc 1 N).filter Nat.Prime).card : ℝ) * Real.log N := by
  have hNR : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  set F := (Finset.Icc 1 N).filter Nat.Prime with hF
  -- fiberwise decomposition by minFac
  have hmaps : ∀ d ∈ Finset.Icc 1 N, d.minFac ∈ insert 1 F := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rcases eq_or_lt_of_le hd.1 with h | h
    · simp [← h]
    · refine Finset.mem_insert_of_mem ?_
      rw [hF, Finset.mem_filter, Finset.mem_Icc]
      have hd2 : 2 ≤ d := h
      have hpr : d.minFac.Prime := Nat.minFac_prime (by omega)
      exact ⟨⟨hpr.one_le, le_trans (Nat.minFac_le (by omega)) hd.2⟩, hpr⟩
  have hfw := Finset.sum_fiberwise_of_maps_to hmaps ArithmeticFunction.vonMangoldt
  -- psiN N = ∑_{y ∈ insert 1 F} fiber(y)
  have h1notF : (1:ℕ) ∉ F := by rw [hF]; simp [Nat.not_prime_one]
  rw [Finset.sum_insert h1notF] at hfw
  -- the y=1 fiber is 0
  have hfiber1 : (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d.minFac = 1),
      ArithmeticFunction.vonMangoldt d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    have : d = 1 := by
      by_contra hne
      have : 2 ≤ d := by omega
      have := Nat.minFac_prime (show d ≠ 1 by omega)
      rw [hd.2] at this; exact Nat.not_prime_one this
    rw [this]; simp
  rw [hfiber1, zero_add] at hfw
  -- now psiN N = ∑_{y∈F} fiber(y), and each fiber ≤ log N
  rw [psiN, ← hfw]
  rw [show (((F.card : ℕ)) : ℝ) * Real.log N = ∑ _y ∈ F, Real.log N by
    rw [Finset.sum_const, nsmul_eq_mul]]
  apply Finset.sum_le_sum
  intro y hy
  rw [hF, Finset.mem_filter] at hy
  have hyp : y.Prime := hy.2
  -- fiber(y) = ∑ over prime-powers of y = card * log y ≤ log N
  have hfibereq : (Finset.Icc 1 N).filter (fun d => d.minFac = y)
      = ((Finset.Icc 1 N).filter (fun d => d.minFac = y ∧ IsPrimePow d))
        ∪ ((Finset.Icc 1 N).filter (fun d => d.minFac = y ∧ ¬ IsPrimePow d)) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro d _; tauto
  rw [hfibereq, Finset.sum_union (by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rw [Finset.mem_filter] at ha hb; exact hb.2.2 ha.2.2)]
  have hnp : (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d.minFac = y ∧ ¬ IsPrimePow d),
      ArithmeticFunction.vonMangoldt d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [ArithmeticFunction.vonMangoldt_apply, if_neg hd.2.2]
  rw [hnp, add_zero]
  -- prime-power fiber sum
  have hval : ∀ d ∈ (Finset.Icc 1 N).filter (fun d => d.minFac = y ∧ IsPrimePow d),
      ArithmeticFunction.vonMangoldt d = Real.log y := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hd.2.2, hd.2.1]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  rw [fiber_eq_image N y hyp, Finset.card_image_of_injective _
    (fun a b h => by exact Nat.pow_right_injective hyp.two_le h)]
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  -- (Nat.log y N) * log y ≤ log N
  have : ((Nat.log y N : ℕ) : ℝ) * Real.log y = Real.log ((y : ℝ) ^ (Nat.log y N)) := by
    rw [Real.log_pow]
  rw [this]
  apply Real.log_le_log (pow_pos (by exact_mod_cast hyp.pos) _)
  have : (y : ℝ) ^ (Nat.log y N) = ((y ^ Nat.log y N : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  exact_mod_cast Nat.pow_log_le_self y (by omega)

/-- Extended log-factorial identity over range Icc 1 N. -/
theorem T_ext (M N : ℕ) (hMN : M ≤ N) :
    T M = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((M / d : ℕ) : ℝ) := by
  rw [T_eq M]
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hxni
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Icc, not_and] at hxni
    have : M < x := by by_contra hc; exact absurd (hxni hx.1) (by push_neg; omega)
    rw [Nat.div_eq_of_lt this, Nat.cast_zero, mul_zero]

noncomputable def Dcomb (N : ℕ) : ℝ := T N - T (N/2) - T (N/3) - T (N/5) + T (N/30)

/-- D combination equals the weighted sum with coefficient Ccoef. -/
theorem Dcomb_eq (N : ℕ) :
    Dcomb N = ∑ d ∈ Finset.Icc 1 N,
      ArithmeticFunction.vonMangoldt d * ((Ccoef (N / d) : ℕ) : ℝ) := by
  unfold Dcomb
  rw [T_ext N N le_rfl, T_ext (N/2) N (Nat.div_le_self _ _),
      T_ext (N/3) N (Nat.div_le_self _ _), T_ext (N/5) N (Nat.div_le_self _ _),
      T_ext (N/30) N (Nat.div_le_self _ _)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Ccoef_cast]
  have e2 : N / 2 / d = N / d / 2 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e3 : N / 3 / d = N / d / 3 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e5 : N / 5 / d = N / d / 5 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have e30 : N / 30 / d = N / d / 30 := by rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [e2, e3, e5, e30]
  ring

theorem vonMangoldt_nonneg (d : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt d :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- ψ(N) ≥ D(N). -/
theorem psiN_ge_Dcomb (N : ℕ) : Dcomb N ≤ psiN N := by
  rw [Dcomb_eq, psiN]
  apply Finset.sum_le_sum
  intro d hd
  have hC : ((Ccoef (N/d) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Ccoef_le_one (N/d)
  calc ArithmeticFunction.vonMangoldt d * ((Ccoef (N/d) : ℕ) : ℝ)
      ≤ ArithmeticFunction.vonMangoldt d * 1 := by
        apply mul_le_mul_of_nonneg_left hC (vonMangoldt_nonneg d)
    _ = ArithmeticFunction.vonMangoldt d := by ring

theorem filter_gt_eq_Icc (N m : ℕ) (hm : m ≤ N) :
    (Finset.Icc 1 N).filter (fun d => m < d) = Finset.Icc (m+1) N := by
  apply Finset.ext; intro x
  simp only [Finset.mem_filter, Finset.mem_Icc]; omega

/-- ψ(N) - ψ(⌊N/6⌋) ≤ D(N). -/
theorem Dcomb_ge_psi_sub (N : ℕ) : psiN N - psiN (N/6) ≤ Dcomb N := by
  rw [Dcomb_eq]
  have hsub : psiN N - psiN (N/6)
      = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * (if N/6 < d then (1:ℝ) else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    rw [filter_gt_eq_Icc N (N/6) (Nat.div_le_self _ _)]
    rw [psiN, psiN]
    rw [show Finset.Icc 1 N = Finset.Icc 1 (N/6) ∪ Finset.Icc (N/6+1) N by
      apply Finset.ext; intro x
      simp only [Finset.mem_Icc, Finset.mem_union]
      have : N/6 ≤ N := Nat.div_le_self _ _
      omega]
    rw [Finset.sum_union (by
      apply Finset.disjoint_left.mpr; intro a ha hb
      rw [Finset.mem_Icc] at ha hb; omega)]
    ring
  rw [hsub]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mem_Icc] at hd
  by_cases h : N/6 < d
  · rw [if_pos h]
    have : Ccoef (N/d) = 1 := by
      apply Ccoef_eq_one_small
      · exact Nat.one_le_div_iff (by omega) |>.mpr hd.2
      · have hlt : N / d < 6 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
        omega
    rw [this]; simp
  · rw [if_neg h, mul_zero]
    apply mul_nonneg (vonMangoldt_nonneg d)
    exact_mod_cast Nat.zero_le _

open Real

/-- (a+1) log(a+1) ≤ a log a + log a + 2 for a ≥ 1. -/
theorem xlogx_succ_le (a : ℝ) (ha : 1 ≤ a) :
    (a + 1) * Real.log (a + 1) ≤ a * Real.log a + Real.log a + 2 := by
  have ha0 : 0 < a := by linarith
  have hlog : Real.log (a + 1) = Real.log a + Real.log (1 + 1/a) := by
    rw [← Real.log_mul (by linarith) (by positivity)]
    congr 1; field_simp
  have hle : Real.log (1 + 1/a) ≤ 1/a := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/a by positivity)
    linarith
  have h2 : (a + 1) * (1/a) ≤ 2 := by
    rw [add_mul, mul_one_div, div_self (by linarith)]
    have : 1/a ≤ 1 := by rw [div_le_one ha0]; linarith
    linarith
  calc (a + 1) * Real.log (a + 1)
      = (a + 1) * (Real.log a + Real.log (1 + 1/a)) := by rw [hlog]
    _ = a * Real.log a + Real.log a + (a+1) * Real.log (1 + 1/a) := by ring
    _ ≤ a * Real.log a + Real.log a + (a+1) * (1/a) := by
        gcongr
    _ ≤ a * Real.log a + Real.log a + 2 := by linarith

theorem xlogx_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x * Real.log x ≤ y * Real.log y := by
  have hy : 1 ≤ y := le_trans hx hxy
  exact mul_le_mul hxy (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx) (by linarith)

theorem cast_div_ge (N k : ℕ) (hk : 0 < k) :
    (N:ℝ)/(k:ℝ) - 1 ≤ ((N / k : ℕ) : ℝ) := by
  have e := Nat.div_add_mod N k
  have hm := Nat.mod_lt N hk
  have h1 : N < k * (N / k) + k := by omega
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have h2 : (N:ℝ) < (k:ℝ) * ((N/k:ℕ):ℝ) + (k:ℝ) := by exact_mod_cast h1
  rw [sub_le_iff_le_add, div_le_iff₀ hkR]
  nlinarith [h2]

noncomputable def c30 : ℝ := Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

/-- Main-term identity: the combination of x·log x equals c30 · n. -/
theorem main_identity (n : ℝ) (hn : 0 < n) :
    n * Real.log n - (n/2) * Real.log (n/2) - (n/3) * Real.log (n/3)
      - (n/5) * Real.log (n/5) + (n/30) * Real.log (n/30) = c30 * n := by
  rw [Real.log_div (by linarith) (by norm_num),
      Real.log_div (by linarith) (by norm_num),
      Real.log_div (by linarith) (by norm_num),
      Real.log_div (by linarith) (by norm_num)]
  unfold c30
  ring

/-- Top-slice: the primes in `((p-1)/2, p]` each contribute `log q` (with coefficient 1) to
`Dcomb p`, giving `H · log((p-1)/2 + 1) ≤ Dcomb p`. -/
theorem top_slice (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 p).filter (fun q => q.Prime ∧ (p-1)/2 < q)).card : ℝ)
        * Real.log (((p-1)/2 : ℕ) + 1) ≤ Dcomb p := by
  set B := (p - 1) / 2 with hB
  have hp2 : 2 ≤ p := hp.two_le
  have hBp : 2 * B = p - 1 := by
    obtain ⟨m, hm⟩ := hodd; omega
  set S := (Finset.Icc 1 p).filter (fun q => q.Prime ∧ B < q) with hS
  have hSsub : S ⊆ Finset.Icc 1 p := Finset.filter_subset _ _
  rw [Dcomb_eq]
  -- lower bound the full sum by the sum over S (nonneg terms)
  have hstep : ∑ d ∈ S, ArithmeticFunction.vonMangoldt d * ((Ccoef (p / d) : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 p, ArithmeticFunction.vonMangoldt d * ((Ccoef (p / d) : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
    intro d _ _
    exact mul_nonneg (vonMangoldt_nonneg d) (by positivity)
  refine le_trans ?_ hstep
  -- on S, the summand is log d ≥ log(B+1)
  have hval : ∀ d ∈ S, ArithmeticFunction.vonMangoldt d * ((Ccoef (p / d) : ℕ) : ℝ)
      = Real.log d := by
    intro d hd
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdp⟩, hdpr, hdB⟩ := hd
    have hdpos : 0 < d := by omega
    have hd1' : 1 ≤ p / d := (Nat.one_le_div_iff hdpos).mpr hdp
    have hd2' : p / d < 2 := (Nat.div_lt_iff_lt_mul hdpos).mpr (by omega)
    have hpd1 : p / d = 1 := by omega
    rw [hpd1]
    have : Ccoef 1 = 1 := by decide
    rw [this, Nat.cast_one, mul_one, ArithmeticFunction.vonMangoldt_apply_prime hdpr]
  rw [Finset.sum_congr rfl hval]
  -- ∑_{d∈S} log d ≥ card * log(B+1)
  rw [show (((S.card : ℕ)) : ℝ) * Real.log ((B:ℕ) + 1) = ∑ _d ∈ S, Real.log ((B:ℕ)+1) by
    rw [Finset.sum_const, nsmul_eq_mul]]
  apply Finset.sum_le_sum
  intro d hd
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hd
  apply Real.log_le_log (by positivity)
  have : (B:ℕ) + 1 ≤ d := by omega
  exact_mod_cast this

/-- Lower bound: ψ(N) ≥ Dcomb(N) ≥ c30·N − 4logN − 9 for N ≥ 60. -/
theorem Dcomb_lower (N : ℕ) (hN : 60 ≤ N) :
    c30 * (N:ℝ) - 4 * Real.log N - 9 ≤ Dcomb N := by
  have hNR : (60:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have cn : ∀ m : ℕ, (0:ℝ) ≤ (m:ℝ) := fun m => Nat.cast_nonneg m
  -- floor bounds
  have h2le : ((N/2:ℕ):ℝ) ≤ (N:ℝ)/2 := Nat.cast_div_le
  have h3le : ((N/3:ℕ):ℝ) ≤ (N:ℝ)/3 := Nat.cast_div_le
  have h5le : ((N/5:ℕ):ℝ) ≤ (N:ℝ)/5 := Nat.cast_div_le
  have h30le : ((N/30:ℕ):ℝ) ≤ (N:ℝ)/30 := Nat.cast_div_le
  have h2ge : (N:ℝ)/2 - 1 ≤ ((N/2:ℕ):ℝ) := cast_div_ge N 2 (by norm_num)
  have h3ge : (N:ℝ)/3 - 1 ≤ ((N/3:ℕ):ℝ) := cast_div_ge N 3 (by norm_num)
  have h5ge : (N:ℝ)/5 - 1 ≤ ((N/5:ℕ):ℝ) := cast_div_ge N 5 (by norm_num)
  have h30ge : (N:ℝ)/30 - 1 ≤ ((N/30:ℕ):ℝ) := cast_div_ge N 30 (by norm_num)
  -- positivity of divisions
  have p2 : (1:ℝ) ≤ (N:ℝ)/2 := by linarith
  have p3 : (1:ℝ) ≤ (N:ℝ)/3 := by linarith
  have p5 : (1:ℝ) ≤ (N:ℝ)/5 := by linarith
  have p30 : (2:ℝ) ≤ (N:ℝ)/30 := by linarith
  -- T bounds
  have tN := T_lower N (by omega)
  have tm2 := T_upper (N/2)
  have tm3 := T_upper (N/3)
  have tm5 := T_upper (N/5)
  have tm30 := T_lower (N/30) (by omega)
  -- xlogx upper bounds for the subtracted terms
  have hb2 : (((N/2:ℕ):ℝ)+1) * Real.log (((N/2:ℕ):ℝ)+1)
      ≤ ((N:ℝ)/2) * Real.log ((N:ℝ)/2) + Real.log ((N:ℝ)/2) + 2 := by
    have hmono := xlogx_mono (x := ((N/2:ℕ):ℝ)+1) (y := (N:ℝ)/2 + 1)
      (by linarith [cn (N/2)]) (by linarith)
    have hsucc := xlogx_succ_le ((N:ℝ)/2) p2
    linarith
  have hb3 : (((N/3:ℕ):ℝ)+1) * Real.log (((N/3:ℕ):ℝ)+1)
      ≤ ((N:ℝ)/3) * Real.log ((N:ℝ)/3) + Real.log ((N:ℝ)/3) + 2 := by
    have hmono := xlogx_mono (x := ((N/3:ℕ):ℝ)+1) (y := (N:ℝ)/3 + 1)
      (by linarith [cn (N/3)]) (by linarith)
    have hsucc := xlogx_succ_le ((N:ℝ)/3) p3
    linarith
  have hb5 : (((N/5:ℕ):ℝ)+1) * Real.log (((N/5:ℕ):ℝ)+1)
      ≤ ((N:ℝ)/5) * Real.log ((N:ℝ)/5) + Real.log ((N:ℝ)/5) + 2 := by
    have hmono := xlogx_mono (x := ((N/5:ℕ):ℝ)+1) (y := (N:ℝ)/5 + 1)
      (by linarith [cn (N/5)]) (by linarith)
    have hsucc := xlogx_succ_le ((N:ℝ)/5) p5
    linarith
  -- xlogx lower bound for the +T(N/30) term
  have hb30 : ((N:ℝ)/30) * Real.log ((N:ℝ)/30) - Real.log ((N:ℝ)/30) - 2
      ≤ ((N/30:ℕ):ℝ) * Real.log ((N/30:ℕ):ℝ) := by
    have hmono := xlogx_mono (x := (N:ℝ)/30 - 1) (y := ((N/30:ℕ):ℝ))
      (by linarith) h30ge
    have hsucc := xlogx_succ_le ((N:ℝ)/30 - 1) (by linarith)
    have heq : (N:ℝ)/30 - 1 + 1 = (N:ℝ)/30 := by ring
    rw [heq] at hsucc
    have hloglt : Real.log ((N:ℝ)/30 - 1) ≤ Real.log ((N:ℝ)/30) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  -- log(N/k) ≤ log N
  have hl2 : Real.log ((N:ℝ)/2) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl3 : Real.log ((N:ℝ)/3) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl5 : Real.log ((N:ℝ)/5) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl30 : Real.log ((N:ℝ)/30) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hmain := main_identity (N:ℝ) hN0
  unfold Dcomb
  linarith [tN, tm2, tm3, tm5, tm30, hb2, hb3, hb5, hb30, hmain,
    hl2, hl3, hl5, hl30, h2ge, h3ge, h5ge, h30le]

/-- Upper bound: Dcomb(N) ≤ c30·N + 5logN + 10 for N ≥ 60. -/
theorem Dcomb_upper (N : ℕ) (hN : 60 ≤ N) :
    Dcomb N ≤ c30 * (N:ℝ) + 5 * Real.log N + 10 := by
  have hNR : (60:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) < (N:ℝ) := by linarith
  have cn : ∀ m : ℕ, (0:ℝ) ≤ (m:ℝ) := fun m => Nat.cast_nonneg m
  have h2le : ((N/2:ℕ):ℝ) ≤ (N:ℝ)/2 := Nat.cast_div_le
  have h3le : ((N/3:ℕ):ℝ) ≤ (N:ℝ)/3 := Nat.cast_div_le
  have h5le : ((N/5:ℕ):ℝ) ≤ (N:ℝ)/5 := Nat.cast_div_le
  have h30le : ((N/30:ℕ):ℝ) ≤ (N:ℝ)/30 := Nat.cast_div_le
  have h2ge : (N:ℝ)/2 - 1 ≤ ((N/2:ℕ):ℝ) := cast_div_ge N 2 (by norm_num)
  have h3ge : (N:ℝ)/3 - 1 ≤ ((N/3:ℕ):ℝ) := cast_div_ge N 3 (by norm_num)
  have h5ge : (N:ℝ)/5 - 1 ≤ ((N/5:ℕ):ℝ) := cast_div_ge N 5 (by norm_num)
  have h30ge : (N:ℝ)/30 - 1 ≤ ((N/30:ℕ):ℝ) := cast_div_ge N 30 (by norm_num)
  have p30 : (1:ℝ) ≤ (N:ℝ)/30 := by linarith
  have tN := T_upper N
  have tm2 := T_lower (N/2) (by omega)
  have tm3 := T_lower (N/3) (by omega)
  have tm5 := T_lower (N/5) (by omega)
  have tm30 := T_upper (N/30)
  -- upper bound on (N+1)log(N+1)
  have hbN := xlogx_succ_le (N:ℝ) (by linarith)
  -- reverse bounds for subtracted terms m2,m3,m5:  (N/k)log(N/k) - log(N/k) - 2 ≤ m_k log m_k
  have hbu2 : ((N:ℝ)/2) * Real.log ((N:ℝ)/2) - Real.log ((N:ℝ)/2) - 2
      ≤ ((N/2:ℕ):ℝ) * Real.log ((N/2:ℕ):ℝ) := by
    have hmono := xlogx_mono (x := (N:ℝ)/2 - 1) (y := ((N/2:ℕ):ℝ)) (by linarith) h2ge
    have hsucc := xlogx_succ_le ((N:ℝ)/2 - 1) (by linarith)
    have heq : (N:ℝ)/2 - 1 + 1 = (N:ℝ)/2 := by ring
    rw [heq] at hsucc
    have hloglt : Real.log ((N:ℝ)/2 - 1) ≤ Real.log ((N:ℝ)/2) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hbu3 : ((N:ℝ)/3) * Real.log ((N:ℝ)/3) - Real.log ((N:ℝ)/3) - 2
      ≤ ((N/3:ℕ):ℝ) * Real.log ((N/3:ℕ):ℝ) := by
    have hmono := xlogx_mono (x := (N:ℝ)/3 - 1) (y := ((N/3:ℕ):ℝ)) (by linarith) h3ge
    have hsucc := xlogx_succ_le ((N:ℝ)/3 - 1) (by linarith)
    have heq : (N:ℝ)/3 - 1 + 1 = (N:ℝ)/3 := by ring
    rw [heq] at hsucc
    have hloglt : Real.log ((N:ℝ)/3 - 1) ≤ Real.log ((N:ℝ)/3) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hbu5 : ((N:ℝ)/5) * Real.log ((N:ℝ)/5) - Real.log ((N:ℝ)/5) - 2
      ≤ ((N/5:ℕ):ℝ) * Real.log ((N/5:ℕ):ℝ) := by
    have hmono := xlogx_mono (x := (N:ℝ)/5 - 1) (y := ((N/5:ℕ):ℝ)) (by linarith) h5ge
    have hsucc := xlogx_succ_le ((N:ℝ)/5 - 1) (by linarith)
    have heq : (N:ℝ)/5 - 1 + 1 = (N:ℝ)/5 := by ring
    rw [heq] at hsucc
    have hloglt : Real.log ((N:ℝ)/5 - 1) ≤ Real.log ((N:ℝ)/5) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  -- upper bound for the +T(N/30) term
  have hbu30 : (((N/30:ℕ):ℝ)+1) * Real.log (((N/30:ℕ):ℝ)+1)
      ≤ ((N:ℝ)/30) * Real.log ((N:ℝ)/30) + Real.log ((N:ℝ)/30) + 2 := by
    have hmono := xlogx_mono (x := ((N/30:ℕ):ℝ)+1) (y := (N:ℝ)/30 + 1)
      (by linarith [cn (N/30)]) (by linarith)
    have hsucc := xlogx_succ_le ((N:ℝ)/30) p30
    linarith
  have hl2 : Real.log ((N:ℝ)/2) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl3 : Real.log ((N:ℝ)/3) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl5 : Real.log ((N:ℝ)/5) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hl30 : Real.log ((N:ℝ)/30) ≤ Real.log N := Real.log_le_log (by linarith) (by linarith)
  have hmain := main_identity (N:ℝ) hN0
  unfold Dcomb
  linarith [tN, tm2, tm3, tm5, tm30, hbN, hbu2, hbu3, hbu5, hbu30, hmain,
    hl2, hl3, hl5, hl30, h2le, h3le, h5le, h30ge]
