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

open Finset

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def g4 (x : ℕ) : ℕ := ((Finset.Ico 1 x).filter (fun k => tau k = 4)).card

/-- τ of a product of two distinct primes is 4. -/
theorem tau_two_primes {r q : ℕ} (hr : r.Prime) (hq : q.Prime) (hrq : r ≠ q) :
    tau (r * q) = 4 := by
  unfold tau
  rw [Nat.Coprime.card_divisors_mul (Nat.coprime_primes hr hq |>.mpr hrq),
      Nat.Prime.divisors hr, Nat.Prime.divisors hq]
  rw [Finset.card_pair (fun h => hr.ne_one h.symm), Finset.card_pair (fun h => hq.ne_one h.symm)]

/-- The family injection lower bound for g4. -/
theorem g4_ge_fam (p : ℕ) (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    ∑ r ∈ S, ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card ≤ g4 p := by
  set f : ℕ → Finset ℕ := fun r =>
    ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).image (fun q => r*q) with hf
  have hcard : ∀ r ∈ S, (f r).card
      = ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card := by
    intro r hr
    rw [hf]
    apply Finset.card_image_of_injOn
    intro a _ b _ hab
    have hrpos : 0 < r := (hS r hr).pos
    exact Nat.eq_of_mul_eq_mul_left hrpos hab
  -- disjointness
  have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (f x) (f y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro n hnx hny
    rw [hf] at hnx hny
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hnx hny
    obtain ⟨qx, ⟨⟨hqx1, _⟩, hqxp, _⟩, rfl⟩ := hnx
    obtain ⟨qy, ⟨⟨hqy1, _⟩, hqyp, _⟩, hqe⟩ := hny
    -- hqe : y * qy = x * qx ; x<qx, y<qy, all prime; derive x = y
    have hxp := hS x hx; have hyp := hS y hy
    have hxlt : x < qx := hqx1
    have hylt : y < qy := hqy1
    have hdvd : x ∣ y * qy := ⟨qx, hqe⟩
    rcases (hxp.dvd_mul.mp hdvd) with h | h
    · exact hxy ((Nat.prime_dvd_prime_iff_eq hxp hyp).mp h)
    · have hxqy : x = qy := (Nat.prime_dvd_prime_iff_eq hxp hqyp).mp h
      rw [← hxqy] at hqe
      -- hqe : y * x = x * qx
      have hxpos : 0 < x := hxp.pos
      have hyqx : y = qx := by
        have h2 : x * y = x * qx := by rw [mul_comm x y]; exact hqe
        exact Nat.eq_of_mul_eq_mul_left hxpos h2
      omega
  have hbu : (S.biUnion f).card = ∑ r ∈ S, (f r).card := Finset.card_biUnion hdisj
  have hsub : S.biUnion f ⊆ (Finset.Ico 1 p).filter (fun k => tau k = 4) := by
    intro n hn
    rw [Finset.mem_biUnion] at hn
    obtain ⟨r, hrS, hnr⟩ := hn
    rw [hf] at hnr
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico] at hnr
    obtain ⟨q, ⟨⟨hq1, _⟩, hqp, hqpr⟩, rfl⟩ := hnr
    have hrp := hS r hrS
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, hqpr⟩, ?_⟩
    · have := hrp.pos; nlinarith [hqp.pos]
    · exact tau_two_primes hrp hqp (by omega)
  calc ∑ r ∈ S, ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card
      = ∑ r ∈ S, (f r).card := by rw [Finset.sum_congr rfl hcard]
    _ = (S.biUnion f).card := hbu.symm
    _ ≤ ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card := Finset.card_le_card hsub
    _ = g4 p := rfl

theorem c30_eq : c30 = 7/15 * Real.log 2 + 3/10 * Real.log 3 + 1/6 * Real.log 5 := by
  unfold c30
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30:ℝ) = 2*3*5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  rw [h30]; ring

/-- exp(x) ≤ 1/(1-x) for x < 1 (from `1-x ≤ exp(-x)`). -/
theorem exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ 1 / (1 - x) := by
  have h1 : (1 - x) ≤ Real.exp (-x) := by have := Real.add_one_le_exp (-x); linarith
  rw [Real.exp_neg] at h1
  have hp : (0:ℝ) < Real.exp x := Real.exp_pos _
  rw [le_div_iff₀ (by linarith)]
  have hcancel : (Real.exp x)⁻¹ * Real.exp x = 1 := inv_mul_cancel₀ hp.ne'
  nlinarith [h1, hp, hcancel]

theorem log3_ge : (1.09:ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hsum : Real.exp (1.09:ℝ) = Real.exp 1 * Real.exp 0.09 := by
    rw [← Real.exp_add]; norm_num
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he09 : Real.exp (0.09:ℝ) ≤ 1/(1-0.09) := exp_le_inv_one_sub (by norm_num)
  have hp09 : (0:ℝ) < Real.exp (0.09:ℝ) := Real.exp_pos _
  have hp1 : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  rw [hsum]; nlinarith [he1, he09, hp09, hp1]

theorem log5_ge : (1.5:ℝ) ≤ Real.log 5 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hsum : Real.exp (1.5:ℝ) = Real.exp 1 * (Real.exp 0.25 * Real.exp 0.25) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he25 : Real.exp (0.25:ℝ) ≤ 1/(1-0.25) := exp_le_inv_one_sub (by norm_num)
  have hp25 : (0:ℝ) < Real.exp (0.25:ℝ) := Real.exp_pos _
  have hp1 : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  rw [hsum]; nlinarith [he1, he25, hp25, hp1]

theorem log3_le : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos (1:ℝ), Real.exp_add 1 1, Real.exp_pos (2:ℝ),
    show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]

theorem log5_le : Real.log 5 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  nlinarith [Real.exp_one_gt_d9, Real.exp_pos (1:ℝ),
    show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]

theorem c30_ge : (0.9 : ℝ) ≤ c30 := by
  rw [c30_eq]
  have h2 := Real.log_two_gt_d9
  nlinarith [h2, log3_ge, log5_ge]

theorem c30_le : c30 ≤ (1.4 : ℝ) := by
  rw [c30_eq]
  have h2 := Real.log_two_lt_d9
  nlinarith [h2, log3_le, log5_le]

noncomputable def pc (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter Nat.Prime).card

theorem pc_lower (N : ℕ) (hN : 60 ≤ N) :
    c30 * N - 4 * Real.log N - 9 ≤ (pc N : ℝ) * Real.log N := by
  have h1 := Dcomb_lower N hN
  have h2 := psiN_ge_Dcomb N
  have h3 := psi_le_pc_logN N (by omega)
  unfold pc
  linarith

theorem fam_card_eq (p r : ℕ) (hr : 0 < r) (hrB : r ≤ (p-1)/r) :
    ((Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)).card
      = pc ((p-1)/r) - pc r := by
  set B := (p-1)/r with hB
  have hBp : B < p := by
    have : B ≤ p - 1 := Nat.div_le_self _ _
    omega
  -- rewrite the filter set as (Ioc r B).filter Prime
  have e1 : (Finset.Ico (r+1) p).filter (fun q => q.Prime ∧ r*q < p)
      = (Finset.Ioc r B).filter Nat.Prime := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hq1, _⟩, hqp, hrq⟩
      have : q ≤ B := by
        rw [hB, Nat.le_div_iff_mul_le hr, Nat.mul_comm]; omega
      exact ⟨⟨by omega, this⟩, hqp⟩
    · rintro ⟨⟨hrq, hqB⟩, hqp⟩
      refine ⟨⟨by omega, by omega⟩, hqp, ?_⟩
      have : r * q ≤ p - 1 := by
        rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le hr]; exact hqB
      omega
  -- split Icc 1 B
  have esplit : Finset.Icc 1 B = Finset.Icc 1 r ∪ Finset.Ioc r B := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 r).filter Nat.Prime)
      ((Finset.Ioc r B).filter Nat.Prime) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1; simp only [Finset.mem_Ioc] at hx2; omega
  have hpcB : pc B = pc r + ((Finset.Ioc r B).filter Nat.Prime).card := by
    unfold pc
    rw [esplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  rw [e1]; omega

theorem pc_mono {a b : ℕ} (h : a ≤ b) : pc a ≤ pc b := by
  unfold pc
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h))

theorem top_card_eq (p B : ℕ) (h1B : 1 ≤ B) (hBp : B ≤ p) :
    ((Finset.Icc 1 p).filter (fun q => q.Prime ∧ B < q)).card = pc p - pc B := by
  have e1 : (Finset.Icc 1 p).filter (fun q => q.Prime ∧ B < q)
      = (Finset.Ioc B p).filter Nat.Prime := by
    ext q; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hqp⟩, hpr, hBq⟩; exact ⟨⟨hBq, hqp⟩, hpr⟩
    · rintro ⟨⟨hBq, hqp⟩, hpr⟩; exact ⟨⟨by omega, hqp⟩, hpr, hBq⟩
  have esplit : Finset.Icc 1 p = Finset.Icc 1 B ∪ Finset.Ioc B p := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint ((Finset.Icc 1 B).filter Nat.Prime)
      ((Finset.Ioc B p).filter Nat.Prime) := by
    apply Finset.disjoint_filter_filter; rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1; simp only [Finset.mem_Ioc] at hx2; omega
  have hpcp : pc p = pc B + ((Finset.Ioc B p).filter Nat.Prime).card := by
    unfold pc; rw [esplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  rw [e1]; omega

theorem family_pc_lower (p r : ℕ) (hr3 : 3 ≤ r) (hr47 : r ≤ 47) (hp : 13000 ≤ p) :
    c30 * ((p:ℝ)/r) - 2*c30 - 4 * Real.log ((p:ℝ)/2) - 9
      ≤ (pc ((p-1)/r) : ℝ) * Real.log ((p:ℝ)/2) := by
  set Br := (p-1)/r with hBr
  have hrpos : 0 < r := by omega
  have hB60 : 60 ≤ Br := by rw [hBr, Nat.le_div_iff_mul_le hrpos]; omega
  have hpc := pc_lower Br hB60
  have hcast_pm1 : ((p-1:ℕ):ℝ) = (p:ℝ) - 1 := by rw [Nat.cast_sub (show 1≤p by omega)]; norm_num
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hrpos
  have hr3R : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr3
  have hBrpos : (0:ℝ) < (Br:ℝ) := by exact_mod_cast (show 0 < Br by omega)
  have c1 : (Br:ℝ) * r ≤ (p:ℝ) - 1 := by
    have h := Nat.div_mul_le_self (p-1) r
    rw [← hBr] at h
    calc (Br:ℝ)*r = ((Br*r:ℕ):ℝ) := by push_cast; ring
      _ ≤ ((p-1:ℕ):ℝ) := by exact_mod_cast h
      _ = (p:ℝ)-1 := hcast_pm1
  have hBrle : (Br:ℝ) ≤ (p:ℝ)/2 := by
    nlinarith [c1, hr3R, hBrpos, mul_nonneg hBrpos.le (show (0:ℝ)≤(r:ℝ)-3 by linarith)]
  have hlogle : Real.log Br ≤ Real.log ((p:ℝ)/2) := Real.log_le_log hBrpos hBrle
  have hcd := cast_div_ge (p-1) r hrpos
  rw [hcast_pm1, ← hBr] at hcd
  have hBrge : (p:ℝ)/r - 2 ≤ (Br:ℝ) := by
    have h1r : (1:ℝ)/r ≤ 1 := by rw [div_le_one hrR]; linarith
    have e : ((p:ℝ)-1)/(r:ℝ) = (p:ℝ)/r - 1/r := by ring
    rw [e] at hcd; linarith
  have hc30 : (0:ℝ) ≤ c30 := by have := c30_ge; linarith
  have hpcpos : (0:ℝ) ≤ (pc Br : ℝ) := by positivity
  have step1 : (pc Br : ℝ) * Real.log Br ≤ (pc Br : ℝ) * Real.log ((p:ℝ)/2) :=
    mul_le_mul_of_nonneg_left hlogle hpcpos
  have h1 : c30*(Br:ℝ) - 4*Real.log Br - 9 ≤ (pc Br:ℝ)*Real.log ((p:ℝ)/2) := by linarith
  have h2 : c30*((p:ℝ)/r - 2) ≤ c30*(Br:ℝ) := mul_le_mul_of_nonneg_left hBrge hc30
  have e : c30*((p:ℝ)/r - 2) = c30*((p:ℝ)/r) - 2*c30 := by ring
  linarith

theorem closing_mono (p : ℝ) (hp : 13000 ≤ p) (α : ℝ) (hα : 181 ≤ α * 13000) :
    α * 13000 - 181 * Real.log (13000/2) ≤ α * p - 181 * Real.log (p/2) := by
  have hlogdiff : Real.log (p/2) - Real.log (13000/2) = Real.log (p/13000) := by
    rw [← Real.log_div (by positivity) (by norm_num)]; congr 1; ring
  have hle : Real.log (p/13000) ≤ p/13000 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have key : 181*(p/13000 - 1) ≤ α*p - 13000*α := by
    nlinarith [mul_nonneg (show (0:ℝ)≤α - 181/13000 by linarith) (show (0:ℝ)≤p-13000 by linarith)]
  linarith

set_option maxHeartbeats 2000000 in
theorem key_large (p : ℕ) (hp : p.Prime) (hpge : 13000 ≤ p) : pc p ≤ g4 p := by
  have hpge60 : 60 ≤ p := by omega
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have hR2prime : ∀ r ∈ ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47} : Finset ℕ), r.Prime := by decide
  have hg4 := g4_ge_fam p {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47} hR2prime
  rw [show ({2,3,5,7,11,13,17,19,23,29,31,37,41,43,47} : Finset ℕ)
      = insert 2 (insert 3 (insert 5 (insert 7 (insert 11 (insert 13 (insert 17 (insert 19
        (insert 23 (insert 29 (insert 31 (insert 37 (insert 41 (insert 43 {47}))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at hg4
  -- rewrite each fam card
  rw [fam_card_eq p 2 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 3 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 5 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 7 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 11 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 13 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 17 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 19 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 23 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 29 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 31 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 37 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 41 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 43 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega),
      fam_card_eq p 47 (by norm_num) (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)] at hg4
  -- pc values
  have hpv : pc 2 = 1 ∧ pc 3 = 2 ∧ pc 5 = 3 ∧ pc 7 = 4 ∧ pc 11 = 5 ∧ pc 13 = 6 ∧ pc 17 = 7 ∧
      pc 19 = 8 ∧ pc 23 = 9 ∧ pc 29 = 10 ∧ pc 31 = 11 ∧ pc 37 = 12 ∧ pc 41 = 13 ∧ pc 43 = 14 ∧
      pc 47 = 15 := by decide
  obtain ⟨v2,v3,v5,v7,v11,v13,v17,v19,v23,v29,v31,v37,v41,v43,v47⟩ := hpv
  -- analytic real inequality
  have hnat : pc p + 120 ≤ pc ((p-1)/2) + pc ((p-1)/3) + pc ((p-1)/5) + pc ((p-1)/7)
      + pc ((p-1)/11) + pc ((p-1)/13) + pc ((p-1)/17) + pc ((p-1)/19) + pc ((p-1)/23)
      + pc ((p-1)/29) + pc ((p-1)/31) + pc ((p-1)/37) + pc ((p-1)/41) + pc ((p-1)/43)
      + pc ((p-1)/47) := by
    have hpR : (13000:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpge
    -- family bounds
    have hb3 := family_pc_lower p 3 (by norm_num) (by norm_num) hpge
    have hb5 := family_pc_lower p 5 (by norm_num) (by norm_num) hpge
    have hb7 := family_pc_lower p 7 (by norm_num) (by norm_num) hpge
    have hb11 := family_pc_lower p 11 (by norm_num) (by norm_num) hpge
    have hb13 := family_pc_lower p 13 (by norm_num) (by norm_num) hpge
    have hb17 := family_pc_lower p 17 (by norm_num) (by norm_num) hpge
    have hb19 := family_pc_lower p 19 (by norm_num) (by norm_num) hpge
    have hb23 := family_pc_lower p 23 (by norm_num) (by norm_num) hpge
    have hb29 := family_pc_lower p 29 (by norm_num) (by norm_num) hpge
    have hb31 := family_pc_lower p 31 (by norm_num) (by norm_num) hpge
    have hb37 := family_pc_lower p 37 (by norm_num) (by norm_num) hpge
    have hb41 := family_pc_lower p 41 (by norm_num) (by norm_num) hpge
    have hb43 := family_pc_lower p 43 (by norm_num) (by norm_num) hpge
    have hb47 := family_pc_lower p 47 (by norm_num) (by norm_num) hpge
    push_cast at hb3 hb5 hb7 hb11 hb13 hb17 hb19 hb23 hb29 hb31 hb37 hb41 hb43 hb47
    -- top slice
    have hmono2 : pc ((p-1)/2) ≤ pc p := pc_mono (by omega)
    have harg : Real.log ((p:ℝ)/2) ≤ Real.log ((((p-1)/2 : ℕ):ℝ) + 1) := by
      have hpm : (p-1)/2 = m := by omega
      rw [hpm]
      apply Real.log_le_log (by positivity)
      have hpc2 : (p:ℝ) = 2*(m:ℝ)+1 := by exact_mod_cast hm
      rw [hpc2]; push_cast; linarith
    have hcard := top_card_eq p ((p-1)/2) (by omega) (by omega)
    have hslice := top_slice p hp ⟨m, hm⟩
    have hdu := Dcomb_upper p hpge60
    set Ftop := ((Finset.Icc 1 p).filter (fun q => q.Prime ∧ (p-1)/2 < q)).card with hFtop
    have hcardnn : (0:ℝ) ≤ (Ftop:ℝ) := by positivity
    have hI0 : (Ftop:ℝ)*Real.log ((p:ℝ)/2) ≤ c30*p + 5*Real.log p + 10 :=
      le_trans (le_trans (mul_le_mul_of_nonneg_left harg hcardnn) hslice) hdu
    rw [hcard, Nat.cast_sub hmono2, sub_mul] at hI0
    -- log p decomposition
    have hlogp : Real.log 2 + Real.log ((p:ℝ)/2) = Real.log (p:ℝ) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
    -- closing
    set α := c30 * ((1/3+1/5+1/7+1/11+1/13+1/17+1/19+1/23+1/29+1/31+1/37+1/41+1/43+1/47 : ℝ) - 1)
      with hαdef
    have hαpos : (0.144:ℝ) ≤ α := by rw [hαdef]; nlinarith [c30_ge]
    have hα13000 : (1872:ℝ) ≤ α*13000 := by linarith
    have hlog6500 : Real.log (13000/2 : ℝ) ≤ 13*Real.log 2 := by
      have h1 : Real.log (13000/2 : ℝ) ≤ Real.log ((2:ℝ)^13) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h1; push_cast at h1; linarith
    have hnum : 5*Real.log 2 + 28*c30 + 136 ≤ α*13000 - 181*Real.log (13000/2 : ℝ) := by
      linarith [hα13000, hlog6500, Real.log_two_lt_d9, c30_le]
    have hmono := closing_mono (p:ℝ) hpR α (by linarith)
    have hfrac : c30*((p:ℝ)/3) + c30*((p:ℝ)/5) + c30*((p:ℝ)/7) + c30*((p:ℝ)/11)
        + c30*((p:ℝ)/13) + c30*((p:ℝ)/17) + c30*((p:ℝ)/19) + c30*((p:ℝ)/23) + c30*((p:ℝ)/29)
        + c30*((p:ℝ)/31) + c30*((p:ℝ)/37) + c30*((p:ℝ)/41) + c30*((p:ℝ)/43) + c30*((p:ℝ)/47)
        = α*(p:ℝ) + c30*(p:ℝ) := by rw [hαdef]; ring
    have hfamsum : α*(p:ℝ) + c30*(p:ℝ) - 28*c30 - 56*Real.log ((p:ℝ)/2) - 126
        ≤ (pc ((p-1)/3):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/5):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/7):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/11):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/13):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/17):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/19):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/23):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/29):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/31):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/37):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/41):ℝ)*Real.log ((p:ℝ)/2)
        + (pc ((p-1)/43):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/47):ℝ)*Real.log ((p:ℝ)/2) := by
      linarith [hb3, hb5, hb7, hb11, hb13, hb17, hb19, hb23, hb29, hb31, hb37, hb41, hb43, hb47, hfrac]
    have hu : (0:ℝ) < Real.log ((p:ℝ)/2) := by
      apply Real.log_pos; rw [lt_div_iff₀ (by norm_num)]; linarith
    -- combine to the *u inequality then divide
    have hbig : ((pc p:ℝ) + 120) * Real.log ((p:ℝ)/2)
        ≤ ((pc ((p-1)/2):ℝ) + (pc ((p-1)/3):ℝ) + (pc ((p-1)/5):ℝ) + (pc ((p-1)/7):ℝ)
          + (pc ((p-1)/11):ℝ) + (pc ((p-1)/13):ℝ) + (pc ((p-1)/17):ℝ) + (pc ((p-1)/19):ℝ)
          + (pc ((p-1)/23):ℝ) + (pc ((p-1)/29):ℝ) + (pc ((p-1)/31):ℝ) + (pc ((p-1)/37):ℝ)
          + (pc ((p-1)/41):ℝ) + (pc ((p-1)/43):ℝ) + (pc ((p-1)/47):ℝ)) * Real.log ((p:ℝ)/2) := by
      have el : ((pc p:ℝ) + 120) * Real.log ((p:ℝ)/2)
          = (pc p:ℝ)*Real.log ((p:ℝ)/2) + 120*Real.log ((p:ℝ)/2) := by ring
      have er : ((pc ((p-1)/2):ℝ) + (pc ((p-1)/3):ℝ) + (pc ((p-1)/5):ℝ) + (pc ((p-1)/7):ℝ)
          + (pc ((p-1)/11):ℝ) + (pc ((p-1)/13):ℝ) + (pc ((p-1)/17):ℝ) + (pc ((p-1)/19):ℝ)
          + (pc ((p-1)/23):ℝ) + (pc ((p-1)/29):ℝ) + (pc ((p-1)/31):ℝ) + (pc ((p-1)/37):ℝ)
          + (pc ((p-1)/41):ℝ) + (pc ((p-1)/43):ℝ) + (pc ((p-1)/47):ℝ)) * Real.log ((p:ℝ)/2)
          = (pc ((p-1)/2):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/3):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/5):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/7):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/11):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/13):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/17):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/19):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/23):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/29):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/31):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/37):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/41):ℝ)*Real.log ((p:ℝ)/2) + (pc ((p-1)/43):ℝ)*Real.log ((p:ℝ)/2)
          + (pc ((p-1)/47):ℝ)*Real.log ((p:ℝ)/2) := by ring
      rw [el, er]
      linarith [hI0, hfamsum, hlogp, hmono, hnum]
    have hfinal := le_of_mul_le_mul_right hbig hu
    exact_mod_cast hfinal
  -- monotonicity facts so omega can handle the Nat subtractions linearly
  have m2 : pc 2 ≤ pc ((p-1)/2) := pc_mono (by omega)
  have m3 : pc 3 ≤ pc ((p-1)/3) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m5 : pc 5 ≤ pc ((p-1)/5) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m7 : pc 7 ≤ pc ((p-1)/7) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m11 : pc 11 ≤ pc ((p-1)/11) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m13 : pc 13 ≤ pc ((p-1)/13) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m17 : pc 17 ≤ pc ((p-1)/17) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m19 : pc 19 ≤ pc ((p-1)/19) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m23 : pc 23 ≤ pc ((p-1)/23) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m29 : pc 29 ≤ pc ((p-1)/29) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m31 : pc 31 ≤ pc ((p-1)/31) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m37 : pc 37 ≤ pc ((p-1)/37) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m41 : pc 41 ≤ pc ((p-1)/41) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m43 : pc 43 ≤ pc ((p-1)/43) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  have m47 : pc 47 ≤ pc ((p-1)/47) := pc_mono (by rw [Nat.le_div_iff_mul_le (by norm_num)]; omega)
  omega
