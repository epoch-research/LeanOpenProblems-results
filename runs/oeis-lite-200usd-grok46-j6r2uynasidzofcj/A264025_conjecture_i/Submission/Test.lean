import FormalConjectures.Util.ProblemImports

set_option linter.style.moduleDocstring false

open Nat Real
open Finset
open ArithmeticFunction hiding log

lemma y_term_add_Tp {p : ℕ} (hp : Odd p) :
    ((p - 1) / 2) * (2 * ((p - 1) / 2) + 1) + p * (p + 1) / 2 = p ^ 2 := by
  have hp1 : 1 ≤ p := by
    rcases hp with ⟨k, hk⟩
    omega
  have hdiv : 2 * ((p - 1) / 2) = p - 1 := by
    have : p % 2 = 1 := Nat.odd_iff.mp hp
    exact Nat.mul_div_cancel' (by omega)
  have hpT : 2 * (p * (p + 1) / 2) = p * (p + 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self p))
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * (((p - 1) / 2) * (2 * ((p - 1) / 2) + 1) + p * (p + 1) / 2)
        = 2 * (((p - 1) / 2) * (2 * ((p - 1) / 2) + 1)) + 2 * (p * (p + 1) / 2) := by ring
    _ = (2 * ((p - 1) / 2)) * (2 * ((p - 1) / 2) + 1) + p * (p + 1) := by
        rw [hpT]; ring
    _ = (p - 1) * ((p - 1) + 1) + p * (p + 1) := by rw [hdiv]
    _ = (p - 1) * p + p * (p + 1) := by
        congr 2; exact Nat.sub_add_cancel hp1
    _ = p * (p - 1 + (p + 1)) := by ring
    _ = p * (2 * p) := by
        congr 1; omega
    _ = 2 * p ^ 2 := by ring

lemma two_mul_div_le (n d : ℕ) (hd : 0 < d) :
    2 * (n / (2 * d)) ≤ n / d := by
  have hle : (2 * d) * (n / (2 * d)) ≤ n := Nat.mul_div_le n (2 * d)
  have : (2 * (n / (2 * d))) * d ≤ n := by
    convert hle using 1; ring
  exact (Nat.le_div_iff_mul_le hd).mpr this

lemma div_sub_two_div_le_one (n d : ℕ) (hd : 0 < d) :
    n / d - 2 * (n / (2 * d)) ≤ 1 := by
  have h2d : 0 < 2 * d := Nat.mul_pos (by decide) hd
  have hlt : n < (2 * d) * (n / (2 * d) + 1) := Nat.lt_mul_div_succ n h2d
  have hlt' : n < (2 * (n / (2 * d) + 1)) * d := by
    convert hlt using 1; ring
  have hlt'' : n / d < 2 * (n / (2 * d) + 1) := (Nat.div_lt_iff_lt_mul hd).mpr hlt'
  have : 2 * (n / (2 * d) + 1) = 2 * (n / (2 * d)) + 2 := by ring
  rw [this] at hlt''
  omega

lemma Icc_eq_Ioc_zero (n : ℕ) : Icc 1 n = Ioc 0 n := by
  ext x
  simp only [mem_Icc, mem_Ioc]
  omega

lemma Icc_filter_dvd_card' (n d : ℕ) :
    #{x ∈ Icc 1 n | d ∣ x} = n / d := by
  rw [Icc_eq_Ioc_zero]
  exact Ioc_filter_dvd_card_eq_div n d

lemma sum_log_eq_sum_Lambda_mul_div (n : ℕ) :
    ∑ m ∈ Icc 1 n, log (m : ℝ) = ∑ d ∈ Icc 1 n, Λ d * ((n / d : ℕ) : ℝ) := by
  have lhs : ∑ m ∈ Icc 1 n, log (m : ℝ) =
      ∑ m ∈ Icc 1 n, ∑ d ∈ divisors m, Λ d := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_Icc] at hm
    simpa using (vonMangoldt_sum (n := m)).symm
  rw [lhs]
  have : ∑ m ∈ Icc 1 n, ∑ d ∈ divisors m, Λ d =
      ∑ m ∈ Icc 1 n, ∑ d ∈ Icc 1 n, if d ∣ m then Λ d else 0 := by
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_Icc] at hm
    have hdiv : divisors m = (Icc 1 n).filter (fun d => d ∣ m) := by
      ext d
      simp only [mem_divisors, mem_filter, mem_Icc]
      constructor
      · intro ⟨hdvd, hm0⟩
        have dpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have d_le_m : d ≤ m := Nat.le_of_dvd (by omega) hdvd
        exact ⟨⟨by omega, d_le_m.trans hm.2⟩, hdvd⟩
      · intro ⟨⟨_, _⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hdiv, sum_filter]
  rw [this, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have : ∑ m ∈ Icc 1 n, (if d ∣ m then Λ d else 0) =
      ((Icc 1 n).filter (d ∣ ·)).card • Λ d := by
    rw [← sum_filter, sum_const]
  rw [this, nsmul_eq_mul, Icc_filter_dvd_card', mul_comm]

open Chebyshev
open scoped Chebyshev

lemma prod_Icc_id_eq_factorial (n : ℕ) : ∏ m ∈ Icc 1 n, m = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Nat.factorial_succ, prod_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), ih]
      ring

lemma log_factorial_eq_sum_log (n : ℕ) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, log (m : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
    have hpos : ∀ m ∈ Icc 1 (n + 1), (m : ℝ) ≠ 0 := by
      intro m hm; simp only [mem_Icc] at hm; exact_mod_cast (show m ≠ 0 by omega)
    have hprod : ((n + 1)! : ℝ) = ∏ m ∈ Icc 1 (n + 1), (m : ℝ) := by
      rw [← prod_Icc_id_eq_factorial, Nat.cast_prod]
    rw [hprod, log_prod hpos]

lemma sum_log_ge_stirling {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 + Real.log (2 * π) / 2 ≤
      ∑ m ∈ Icc 1 n, Real.log (m : ℝ) := by
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  simpa [log_factorial_eq_sum_log] using Stirling.le_log_factorial_stirling hn0

lemma nat_sub_cast {a b : ℕ} (h : b ≤ a) : ((a - b : ℕ) : ℝ) = (a : ℝ) - (b : ℝ) :=
  Nat.cast_sub h

lemma weight_cast (n d : ℕ) (hd : 0 < d) :
    ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ)
      = (n / d : ℕ) - (2 * (n / (2 * d)) : ℕ) := by
  exact nat_sub_cast (two_mul_div_le n d hd)

/-- `ψ n ≥ ∑_{d≤n} Λ(d) (⌊n/d⌋ - 2⌊n/(2d)⌋)`. -/
lemma psi_ge_weighted_sum (n : ℕ) :
    ∑ d ∈ Icc 1 n, Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) ≤ ψ (n : ℝ) := by
  have hpsi : ψ (n : ℝ) = ∑ d ∈ Icc 1 n, Λ d := by
    rw [psi_eq_sum_Icc, Nat.floor_natCast]
    have : Icc 0 n = insert 0 (Icc 1 n) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [this, sum_insert (by simp)]
    simp [vonMangoldt_apply]
  rw [hpsi]
  have hle : ∑ d ∈ Icc 1 n, Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ)
      ≤ ∑ d ∈ Icc 1 n, Λ d * (1 : ℝ) := by
    refine sum_le_sum fun d hd => ?_
    have hdpos : 0 < d := by simp [mem_Icc] at hd; omega
    have h1 : n / d - 2 * (n / (2 * d)) ≤ 1 := div_sub_two_div_le_one n d hdpos
    have hnn : 0 ≤ Λ d := vonMangoldt_nonneg
    have : ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith
  simpa using hle

lemma T_sub_twoT_le_psi (n : ℕ) :
    ∑ m ∈ Icc 1 n, log (m : ℝ) - 2 * ∑ m ∈ Icc 1 (n / 2), log (m : ℝ) ≤ ψ (n : ℝ) := by
  rw [sum_log_eq_sum_Lambda_mul_div n, sum_log_eq_sum_Lambda_mul_div (n / 2)]
  -- Replace `(n/2)/d` by `n/(2d)`.
  have hre : ∑ d ∈ Icc 1 (n / 2), Λ d * (((n / 2) / d : ℕ) : ℝ)
      = ∑ d ∈ Icc 1 (n / 2), Λ d * ((n / (2 * d) : ℕ) : ℝ) := by
    refine sum_congr rfl fun d _ => ?_
    rw [Nat.div_div_eq_div_mul]
  rw [hre]
  refine (le_of_eq ?_).trans (psi_ge_weighted_sum n)
  have hsub : Icc 1 (n / 2) ⊆ Icc 1 n := fun x hx => by
    simp only [mem_Icc] at hx ⊢; omega
  -- Split `∑_{d=1}^n` into `d ≤ n/2` and the rest.
  rw [← sum_sdiff hsub]
  -- Left-hand side becomes (sum on small d) + (sum on large d) - 2 * (sum on small d).
  have hsmall : ∀ d ∈ Icc 1 (n / 2),
      Λ d * ((n / d : ℕ) : ℝ) - 2 * Λ d * ((n / (2 * d) : ℕ) : ℝ)
        = Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) := by
    intro d hd
    have hdpos : 0 < d := by simp [mem_Icc] at hd; omega
    rw [weight_cast n d hdpos, Nat.cast_mul]
    ring
  have hlarge : ∀ d ∈ Icc 1 n \ Icc 1 (n / 2),
      Λ d * ((n / d : ℕ) : ℝ) = Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) := by
    intro d hd
    have hz : n / (2 * d) = 0 := by
      simp only [mem_sdiff, mem_Icc] at hd
      have hlt : n / 2 < d := by omega
      have : n < d * 2 := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hlt
      rw [mul_comm] at this
      exact Nat.div_eq_of_lt this
    rw [hz, Nat.sub_zero]
  have hmul :
      2 * ∑ d ∈ Icc 1 (n / 2), Λ d * ((n / (2 * d) : ℕ) : ℝ)
        = ∑ d ∈ Icc 1 (n / 2), (2 * Λ d * ((n / (2 * d) : ℕ) : ℝ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun d _ => by ring
  calc
    ∑ d ∈ Icc 1 n \ Icc 1 (n / 2), Λ d * ((n / d : ℕ) : ℝ)
        + ∑ d ∈ Icc 1 (n / 2), Λ d * ((n / d : ℕ) : ℝ)
        - 2 * ∑ d ∈ Icc 1 (n / 2), Λ d * ((n / (2 * d) : ℕ) : ℝ)
      = ∑ d ∈ Icc 1 n \ Icc 1 (n / 2), Λ d * ((n / d : ℕ) : ℝ)
        + (∑ d ∈ Icc 1 (n / 2), Λ d * ((n / d : ℕ) : ℝ)
            - ∑ d ∈ Icc 1 (n / 2), (2 * Λ d * ((n / (2 * d) : ℕ) : ℝ))) := by
        rw [hmul]; ring
    _ = ∑ d ∈ Icc 1 n \ Icc 1 (n / 2), Λ d * ((n / d : ℕ) : ℝ)
        + ∑ d ∈ Icc 1 (n / 2),
            (Λ d * ((n / d : ℕ) : ℝ) - 2 * Λ d * ((n / (2 * d) : ℕ) : ℝ)) := by
        rw [← sum_sub_distrib]
    _ = ∑ d ∈ Icc 1 n \ Icc 1 (n / 2), Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ)
        + ∑ d ∈ Icc 1 (n / 2), Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) := by
        congr 1
        · exact sum_congr rfl hlarge
        · exact sum_congr rfl hsmall
    _ = ∑ d ∈ Icc 1 n, Λ d * ((n / d - 2 * (n / (2 * d)) : ℕ) : ℝ) := by
        rw [← sum_sdiff hsub]



lemma sum_log_le_integral {n : ℕ} (hn : 2 ≤ n) :
    ∑ m ∈ Icc 1 n, Real.log (m : ℝ)
      ≤ ((n + 1 : ℝ) * Real.log (n + 1) - (n + 1) - 2 * Real.log 2 + 2) := by
  have hab : (2 : ℕ) ≤ n + 1 := by omega
  have hmono : MonotoneOn (fun x : ℝ => Real.log x) (Set.Icc (2 : ℕ) (n + 1 : ℕ)) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x :=
      lt_of_lt_of_le (by exact_mod_cast (by decide : (0 : ℕ) < 2)) hx.1
    exact Real.log_le_log hx0 hxy
  have hsum : ∑ m ∈ Ico (2 : ℕ) (n + 1), Real.log (m : ℝ)
      ≤ ∫ x in (2 : ℕ)..(n + 1 : ℕ), Real.log x :=
    MonotoneOn.sum_le_integral_Ico hab hmono
  have hIcc : ∑ m ∈ Icc 1 n, Real.log (m : ℝ)
      = ∑ m ∈ Ico (2 : ℕ) (n + 1), Real.log (m : ℝ) := by
    have : Icc 1 n = insert 1 (Ico 2 (n + 1)) := by
      ext x; simp only [mem_Icc, mem_insert, mem_Ico]; omega
    rw [this, sum_insert (by simp)]
    simp
  rw [hIcc]
  have hint : ∫ x in (2 : ℝ)..((n + 1 : ℕ) : ℝ), Real.log x
      = (n + 1 : ℝ) * Real.log (n + 1) - 2 * Real.log 2 - (n + 1) + 2 := by
    have := integral_log (a := (2 : ℝ)) (b := ((n + 1 : ℕ) : ℝ))
    simpa [Nat.cast_succ] using this
  have hinter : (∫ x in (2 : ℕ)..(n + 1 : ℕ), Real.log x)
      = ∫ x in (2 : ℝ)..((n + 1 : ℕ) : ℝ), Real.log x := rfl
  linarith [hsum, hint, hinter]

lemma two_mul_div_add_one_le (n : ℕ) : 2 * (n / 2 + 1) ≤ n + 2 := by omega

lemma n_sub_one_le_two_mul_div (n : ℕ) (hn : 1 ≤ n) : n - 1 ≤ 2 * (n / 2) := by omega

lemma T_sub_twoT_ge {n : ℕ} (hn : 8 ≤ n) :
    Real.log 2 * n - 2 * Real.log n - 12 ≤
      ∑ k ∈ Icc 1 n, Real.log (k : ℝ)
        - 2 * ∑ k ∈ Icc 1 (n / 2), Real.log (k : ℝ) := by
  have hlo := sum_log_ge_stirling (show 0 < n by omega)
  have hnd : 2 ≤ n / 2 := by omega
  have hup := sum_log_le_integral hnd
  have hpos_n : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set m : ℝ := ((n / 2 : ℕ) : ℝ) + 1
  have hm_nat : m = ((n / 2 + 1 : ℕ) : ℝ) := by
    push_cast; rfl
  have hpos_m : (0 : ℝ) < m := by positivity
  have hm_le_half : m ≤ (n + 2 : ℝ) / 2 := by
    have : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
    have : m ≤ (n : ℝ) / 2 + 1 := by
      dsimp [m]; linarith
    have : (n : ℝ) / 2 + 1 = (n + 2 : ℝ) / 2 := by ring
    linarith
  have hlog_m : Real.log m ≤ Real.log (n + 2) - Real.log 2 := by
    have := Real.log_le_log hpos_m hm_le_half
    have hid : Real.log ((n + 2 : ℝ) / 2) = Real.log (n + 2) - Real.log 2 :=
      Real.log_div (by positivity) (by positivity)
    linarith
  have hlog_n2 : Real.log (n + 2) ≤ Real.log n + (2 : ℝ) / n := by
    have hdiff : Real.log (n + 2) - Real.log n = Real.log ((n + 2) / n) := by
      rw [Real.log_div (by positivity) (ne_of_gt hpos_n)]
    have hid : Real.log ((n + 2) / n) = Real.log (1 + 2 / (n : ℝ)) := by
      congr 1; field_simp
    have hle : Real.log (1 + 2 / (n : ℝ)) ≤ 2 / (n : ℝ) := by
      have := Real.log_le_sub_one_of_pos (x := (1 : ℝ) + 2 / (n : ℝ)) (by positivity)
      have : (1 : ℝ) + 2 / (n : ℝ) - 1 = 2 / (n : ℝ) := by ring
      linarith
    linarith
  have hprod : (2 : ℝ) * m * Real.log m
      ≤ ((n : ℝ) + 2) * (Real.log n + 2 / (n : ℝ) - Real.log 2) := by
    have h1 : (2 : ℝ) * m ≤ (n : ℝ) + 2 := by
      have : 2 * (n / 2 + 1) ≤ n + 2 := two_mul_div_add_one_le n
      have hcast : (2 : ℝ) * ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast this
      rw [hm_nat]; exact hcast
    have h2 : Real.log m ≤ Real.log n + 2 / (n : ℝ) - Real.log 2 :=
      le_trans hlog_m (by linarith [hlog_n2])
    have h2n : (0 : ℝ) ≤ Real.log n + 2 / (n : ℝ) - Real.log 2 := by
      have : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by positivity)
          (by exact_mod_cast (show (2 : ℕ) ≤ n by omega))
      have : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
      linarith
    nlinarith
  have hc : (0 : ℝ) ≤ Real.log (2 * π) / 2 := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_d2]
    exact div_nonneg (Real.log_nonneg this) (by norm_num)
  have hup' : ∑ k ∈ Icc 1 (n / 2), Real.log (k : ℝ)
      ≤ m * Real.log m - m - 2 * Real.log 2 + 2 := by
    simpa [m] using hup
  have hcomb :
      (n : ℝ) * Real.log n - n + Real.log n / 2
        - 2 * (m * Real.log m - m - 2 * Real.log 2 + 2)
      ≤ ∑ k ∈ Icc 1 n, Real.log (k : ℝ)
          - 2 * ∑ k ∈ Icc 1 (n / 2), Real.log (k : ℝ) := by
    linarith [hlo, hup', hc]
  have h2m : (n : ℝ) + 1 ≤ 2 * m := by
    have : n + 1 ≤ 2 * (n / 2 + 1) := by omega
    have : ((n + 1 : ℕ) : ℝ) ≤ (2 * (n / 2 + 1) : ℕ) := by exact_mod_cast this
    push_cast at this
    rw [hm_nat]; linarith
  have hlogn_nonneg : (0 : ℝ) ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by omega))
  have hmid :
      (n : ℝ) * Real.log n - n
        - ((n : ℝ) + 2) * (Real.log n + 2 / (n : ℝ) - Real.log 2)
        + ((n : ℝ) + 1) + 4 * Real.log 2 - 4
      ≤ (n : ℝ) * Real.log n - n + Real.log n / 2
          - 2 * (m * Real.log m - m - 2 * Real.log 2 + 2) := by
    have hexpand : (n : ℝ) * Real.log n - n + Real.log n / 2
        - 2 * (m * Real.log m - m - 2 * Real.log 2 + 2)
        = (n : ℝ) * Real.log n - n + Real.log n / 2
            - 2 * m * Real.log m + 2 * m + 4 * Real.log 2 - 4 := by
      ring
    rw [hexpand]
    linarith [hprod, h2m, hlogn_nonneg]
  have hL :
      Real.log 2 * n - 2 * Real.log n - 12
        ≤ (n : ℝ) * Real.log n - n
          - ((n : ℝ) + 2) * (Real.log n + 2 / (n : ℝ) - Real.log 2)
          + ((n : ℝ) + 1) + 4 * Real.log 2 - 4 := by
    have hexp :
        (n : ℝ) * Real.log n - n
          - ((n : ℝ) + 2) * (Real.log n + 2 / (n : ℝ) - Real.log 2)
          + ((n : ℝ) + 1) + 4 * Real.log 2 - 4
        = Real.log 2 * (n : ℝ) - 2 * Real.log n + 6 * Real.log 2
            - ((n : ℝ) + 2) * (2 / (n : ℝ)) - 3 := by
      ring
    rw [hexp]
    have hfrac : ((n : ℝ) + 2) * (2 / (n : ℝ)) ≤ 3 := by
      have h1 : ((n : ℝ) + 2) * (2 / (n : ℝ)) = 2 + 4 / (n : ℝ) := by
        field_simp; ring
      have h2 : (4 : ℝ) / n ≤ 1 := by
        have : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
        exact (div_le_one hpos_n).mpr this
      linarith [h1, h2]
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 :=
      le_of_lt (lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9)
    linarith [hfrac, hlog2]
  linarith [hcomb, hmid, hL]

lemma psi_ge_T_sub_twoT (n : ℕ) :
    ∑ k ∈ Icc 1 n, Real.log (k : ℝ)
      - 2 * ∑ k ∈ Icc 1 (n / 2), Real.log (k : ℝ) ≤ ψ (n : ℝ) :=
  T_sub_twoT_le_psi n

lemma psi_ge_log_two_mul {n : ℕ} (hn : 8 ≤ n) :
    Real.log 2 * n - 2 * Real.log n - 12 ≤ ψ (n : ℝ) :=
  le_trans (T_sub_twoT_ge hn) (psi_ge_T_sub_twoT n)

lemma psi_ge_half_log_two_mul {n : ℕ} (hn : 256 ≤ n) :
    (Real.log 2 / 2) * n ≤ ψ (n : ℝ) := by
  have hn8 : 8 ≤ n := by omega
  have h := psi_ge_log_two_mul hn8
  have hpos_n : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 :=
    lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hlog2_lt : Real.log 2 < (7 : ℝ) / 10 :=
    lt_trans Real.log_two_lt_d9 (by norm_num)
  have hlogn : Real.log n ≤ 8 * Real.log 2 + (n : ℝ) / 256 - 1 := by
    have h256 : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
    have hsplit : Real.log n = Real.log 256 + Real.log (n / 256) := by
      have : Real.log n = Real.log (256 * (n / 256)) := by
        congr 1; field_simp
      rw [this, Real.log_mul (by norm_num) (by positivity)]
    have hlog256 : Real.log 256 = 8 * Real.log 2 := by
      rw [h256, Real.log_pow (2 : ℝ) 8]
      norm_cast
    have hrest : Real.log (n / 256) ≤ (n : ℝ) / 256 - 1 :=
      Real.log_le_sub_one_of_pos (x := (n : ℝ) / 256) (by positivity)
    linarith
  -- Enough to show 4 log n + 24 ≤ log 2 * n, using log 2 > 1/2.
  have hgoal : (Real.log 2 / 2) * n ≤ Real.log 2 * n - 2 * Real.log n - 12 := by
    have hineq : 4 * Real.log n + 24 ≤ Real.log 2 * n := by
      have h4 : 4 * Real.log n + 24 ≤ 4 * (8 * Real.log 2 + (n : ℝ) / 256 - 1) + 24 := by
        linarith [hlogn]
      have : 4 * (8 * Real.log 2 + (n : ℝ) / 256 - 1) + 24
          = 32 * Real.log 2 + (n : ℝ) / 64 + 20 := by ring
      have h32 : 32 * Real.log 2 ≤ 32 * ((7 : ℝ) / 10) := by nlinarith
      have : 32 * ((7 : ℝ) / 10) + (n : ℝ) / 64 + 20 ≤ (1 / 2) * n := by
        have hn256 : (256 : ℝ) ≤ n := by exact_mod_cast hn
        -- 22.4 + 20 + n/64 ≤ n/2
        -- 42.4 ≤ n/2 - n/64 = 32n/64 - n/64 = 31n/64
        -- 42.4 * 64 ≤ 31 n
        -- 2713.6 ≤ 31 n
        -- n ≥ 87.5, true
        nlinarith
      nlinarith [h4, h32]
    nlinarith [hineq]
  linarith [h, hgoal]



/-! ### Euclidean domain structure on ℤ[√-2] -/

open Zsqrtd

abbrev ZsqrtNegTwo : Type := Zsqrtd (-2)

local notation "ℤ√-2" => ZsqrtNegTwo

namespace ZsqrtNegTwo

instance : CommRing ℤ√-2 := Zsqrtd.commRing

theorem norm_eq (x : ℤ√-2) : x.norm = x.re * x.re + 2 * (x.im * x.im) := by
  simp [Zsqrtd.norm]
  ring

theorem norm_nonneg' (x : ℤ√-2) : 0 ≤ x.norm :=
  Zsqrtd.norm_nonneg (by simp) x

theorem norm_eq_zero_iff' {x : ℤ√-2} : x.norm = 0 ↔ x = 0 :=
  Zsqrtd.norm_eq_zero_iff (by simp) x

instance : Div ℤ√-2 :=
  ⟨fun x y =>
    let n := (norm y : ℚ)
    let c := star y
    ⟨round ((x * c).re / n : ℚ), round ((x * c).im / n : ℚ)⟩⟩

theorem div_def (x y : ℤ√-2) :
    x / y = ⟨round ((x * star y).re / norm y : ℚ),
              round ((x * star y).im / norm y : ℚ)⟩ :=
  rfl

instance : Mod ℤ√-2 := ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ℤ√-2) : x % y = x - y * (x / y) := rfl

private lemma sq_le_half_sq {a : ℚ} (h : |a| ≤ 1 / 2) : a ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
  have : |a| ^ 2 ≤ (1 / 2 : ℚ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs] using this

/-- The remainder has strictly smaller (positive) norm. -/
theorem norm_mod_lt (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have hy0 : (y.norm : ℚ) ≠ 0 := by
    exact_mod_cast (norm_eq_zero_iff'.not.mpr hy)
  have Npos : 0 < y.norm :=
    lt_of_le_of_ne (norm_nonneg' y) (Ne.symm (norm_eq_zero_iff'.not.mpr hy))
  have NposQ : (0 : ℚ) < y.norm := by exact_mod_cast Npos
  set q := x / y
  have hre_rd : q.re = round ((x * star y).re / y.norm : ℚ) := by
    simp [q, div_def]
  have him_rd : q.im = round ((x * star y).im / y.norm : ℚ) := by
    simp [q, div_def]
  have habs_re : |((x * star y).re : ℚ) / y.norm - q.re| ≤ 1 / 2 := by
    rw [hre_rd]; exact abs_sub_round _
  have habs_im : |((x * star y).im : ℚ) / y.norm - q.im| ≤ 1 / 2 := by
    rw [him_rd]; exact abs_sub_round _
  have hmul : ((x - y * q) * star y).norm = (x - y * q).norm * y.norm := by
    rw [norm_mul, norm_conj]
  have hident : (x - y * q) * star y = x * star y - q * (y.norm : ℤ√-2) := by
    have hyy : (y * star y : ℤ√-2) = y.norm := by
      simpa using (norm_eq_mul_conj y).symm
    calc
      (x - y * q) * star y = x * star y - (y * q) * star y := by simp [sub_mul]
      _ = x * star y - q * (y * star y) := by
        congr 1
        simp [mul_assoc, mul_left_comm]
      _ = x * star y - q * (y.norm : ℤ√-2) := by rw [hyy]
  have hcoord :
      ((x * star y) - q * (y.norm : ℤ√-2)).norm
        = ((x * star y).re - q.re * y.norm)
            * ((x * star y).re - q.re * y.norm)
          + 2 * (((x * star y).im - q.im * y.norm)
            * ((x * star y).im - q.im * y.norm)) := by
    rw [norm_eq]
    simp
  have hfrac :
      ((((x * star y).re - q.re * y.norm : ℤ) : ℚ) ^ 2
        + 2 * (((x * star y).im - q.im * y.norm : ℤ) : ℚ) ^ 2)
      ≤ (3 / 4 : ℚ) * (y.norm : ℚ) ^ 2 := by
    have h1 : (((x * star y).re - q.re * y.norm : ℤ) : ℚ)
        = (y.norm : ℚ) * (((x * star y).re : ℚ) / y.norm - q.re) := by
      have : ((x * star y).re : ℚ) - (q.re : ℚ) * y.norm
          = y.norm * (((x * star y).re : ℚ) / y.norm - q.re) := by
        field_simp [hy0]
      simpa using this
    have h2 : (((x * star y).im - q.im * y.norm : ℤ) : ℚ)
        = (y.norm : ℚ) * (((x * star y).im : ℚ) / y.norm - q.im) := by
      have : ((x * star y).im : ℚ) - (q.im : ℚ) * y.norm
          = y.norm * (((x * star y).im : ℚ) / y.norm - q.im) := by
        field_simp [hy0]
      simpa using this
    rw [h1, h2]
    have hexp :
        ((y.norm : ℚ) * (((x * star y).re : ℚ) / y.norm - q.re)) ^ 2
          + 2 * ((y.norm : ℚ) * (((x * star y).im : ℚ) / y.norm - q.im)) ^ 2
        = (y.norm : ℚ) ^ 2 *
            ((((x * star y).re : ℚ) / y.norm - q.re) ^ 2
              + 2 * (((x * star y).im : ℚ) / y.norm - q.im) ^ 2) := by ring
    rw [hexp]
    have hsq1 := sq_le_half_sq habs_re
    have hsq2 := sq_le_half_sq habs_im
    have hsum :
        ((((x * star y).re : ℚ) / y.norm - q.re) ^ 2
          + 2 * (((x * star y).im : ℚ) / y.norm - q.im) ^ 2)
        ≤ (3 / 4 : ℚ) := by
      nlinarith [hsq1, hsq2]
    nlinarith [sq_nonneg (y.norm : ℚ), hsum]
  have hleft :
      ((x - y * q).norm : ℚ) * y.norm
        = (((x * star y) - q * (y.norm : ℤ√-2)).norm : ℚ) := by
    have := hmul
    rw [hident] at this
    exact_mod_cast this.symm
  have hprod :
      ((x - y * q).norm : ℚ) * y.norm
        ≤ (3 / 4 : ℚ) * (y.norm : ℚ) ^ 2 := by
    rw [hleft, hcoord]
    simpa [pow_two] using hfrac
  have hle : ((x - y * q).norm : ℚ) ≤ (3 / 4 : ℚ) * y.norm := by
    have h' : ((x - y * q).norm : ℚ) * y.norm
        ≤ ((3 / 4 : ℚ) * y.norm) * y.norm := by
      convert hprod using 1
      ring
    exact le_of_mul_le_mul_right h' NposQ
  have hlt : ((x - y * q).norm : ℚ) < y.norm :=
    lt_of_le_of_lt hle (by nlinarith [NposQ])
  simpa [mod_def] using (show (x - y * q).norm < y.norm from by exact_mod_cast hlt)

theorem natAbs_norm_mod_lt (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := norm_mod_lt x hy
  have h1 := norm_nonneg' (x % y)
  have h2 := norm_nonneg' y
  omega

theorem norm_le_norm_mul_left (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  refine le_mul_of_one_le_right (Nat.zero_le _) ?_
  have : 0 < y.norm := lt_of_le_of_ne (norm_nonneg' y) (Ne.symm (norm_eq_zero_iff'.not.mpr hy))
  have : 1 ≤ y.norm.natAbs := by
    have : 0 < y.norm.natAbs := Int.natAbs_pos.mpr (ne_of_gt this)
    omega
  exact this

instance : Nontrivial ℤ√-2 := ⟨0, 1, by decide⟩

instance : EuclideanDomain ℤ√-2 :=
  { (inferInstance : CommRing ℤ√-2),
    (inferInstance : Nontrivial ℤ√-2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing

theorem natAbs_norm_eq (x : ℤ√-2) :
    ((norm x).natAbs : ℤ) = x.re * x.re + 2 * (x.im * x.im) := by
  have hn := norm_nonneg' x
  have : ((norm x).natAbs : ℤ) = norm x := Int.natAbs_of_nonneg hn
  simpa [norm_eq] using this

theorem sq_add_two_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ℤ√-2)) : ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = p := by
  have hpu : ¬IsUnit (p : ℤ√-2) :=
    mt Zsqrtd.norm_eq_one_iff.2 <| by
      rw [Zsqrtd.norm_natCast, Int.natAbs_mul, mul_eq_one]
      exact fun h => (_root_.ne_of_lt hp.1.one_lt).symm h.1
  have hab : ∃ a b, (p : ℤ√-2) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.1 hau)
        (mt Zsqrtd.norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.natCast_inj, Int.natCast_pow, sq, ← @Zsqrtd.norm_natCast (-2), hpab]
        simp).1
  refine ⟨a.re.natAbs, a.im.natAbs, ?_⟩
  have := natAbs_norm_eq a
  have h' : a.re.natAbs * a.re.natAbs + 2 * (a.im.natAbs * a.im.natAbs) = p := by
    have : ((a.re.natAbs : ℤ) * a.re.natAbs + 2 * (a.im.natAbs * a.im.natAbs) : ℤ) = p := by
      simpa [Int.natAbs_mul, pow_two] using this.symm.trans (by exact_mod_cast hnap)
    exact_mod_cast this
  simpa [pow_two, Nat.mul_assoc] using h'

theorem mod_eight_mem_of_nat_prime_of_prime (p : ℕ) [hp : Fact p.Prime]
    (hpi : Prime (p : ℤ√-2)) : p = 2 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  have h2orodd := hp.1.eq_two_or_odd
  rcases h2orodd with hp2 | hodd
  · exact Or.inl hp2
  refine Or.inr ?_
  by_contra hp57
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 := by
    have hodd' : p % 2 = 1 := hodd
    omega
  have hpne2 : p ≠ 2 := by omega
  have hsq : IsSquare (-2 : ZMod p) :=
    (ZMod.exists_sq_eq_neg_two_iff (p := p) hpne2).2 (by tauto)
  obtain ⟨k, hk⟩ := hsq
  obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = k :=
    ⟨k.val, k.val_lt, ZMod.natCast_zmod_val k⟩
  have hpk : p ∣ k ^ 2 + 2 := by
    rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul,
      Nat.cast_two, ← hk, neg_add_cancel]
  have hkmul : (k ^ 2 + 2 : ℤ√-2) = ⟨k, 1⟩ * ⟨k, -1⟩ := by
    ext <;> simp [sq]
  have hkltp : k * k + 2 < p * p := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hp2 : 2 < p := lt_of_le_of_ne hp.1.two_le (Ne.symm hpne2)
      nlinarith
    · nlinarith
  have hnorm_k1 : (Zsqrtd.norm (⟨k, 1⟩ : ℤ√-2)).natAbs = k * k + 2 := by
    simp [Zsqrtd.norm, Int.natAbs_add_of_nonneg, Int.natAbs_mul]
    omega
  have hnorm_km1 : (Zsqrtd.norm (⟨k, -1⟩ : ℤ√-2)).natAbs = k * k + 2 := by
    simp [Zsqrtd.norm, Int.natAbs_add_of_nonneg, Int.natAbs_mul]
    omega
  have hnorm_p : (norm (p : ℤ√-2)).natAbs = p * p := by
    have hn : norm (p : ℤ√-2) = (p : ℤ) * (p : ℤ) := Zsqrtd.norm_natCast p
    rw [hn, ← Int.natCast_mul, Int.natAbs_natCast]
  have hpk₁ : ¬(p : ℤ√-2) ∣ ⟨k, -1⟩ := fun ⟨x, hx⟩ =>
    lt_irrefl (norm ((p : ℤ√-2) * x)).natAbs <|
      calc
        (norm ((p : ℤ√-2) * x)).natAbs = (Zsqrtd.norm ⟨k, -1⟩).natAbs := by rw [hx]
        _ < (norm (p : ℤ√-2)).natAbs := by
          rw [hnorm_km1, hnorm_p]; exact hkltp
        _ ≤ (norm ((p : ℤ√-2) * x)).natAbs :=
          norm_le_norm_mul_left _ fun hx0 => by
            have him : Zsqrtd.im (⟨k, -1⟩ : ℤ√-2) = 0 := by
              simpa [hx0] using congr_arg Zsqrtd.im hx
            simp at him
  have hpk₂ : ¬(p : ℤ√-2) ∣ ⟨k, 1⟩ := fun ⟨x, hx⟩ =>
    lt_irrefl (norm ((p : ℤ√-2) * x)).natAbs <|
      calc
        (norm ((p : ℤ√-2) * x)).natAbs = (Zsqrtd.norm ⟨k, 1⟩).natAbs := by rw [hx]
        _ < (norm (p : ℤ√-2)).natAbs := by
          rw [hnorm_k1, hnorm_p]; exact hkltp
        _ ≤ (norm ((p : ℤ√-2) * x)).natAbs :=
          norm_le_norm_mul_left _ fun hx0 => by
            have him : Zsqrtd.im (⟨k, 1⟩ : ℤ√-2) = 0 := by
              simpa [hx0] using congr_arg Zsqrtd.im hx
            simp at him
  obtain ⟨y, hy⟩ := hpk
  have := hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ ⟨y, by rw [← hkmul, ← Nat.cast_mul p, ← hy]; simp⟩
  tauto

lemma sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  set r := a % 8
  have hr : r < 8 := Nat.mod_lt a (by decide)
  interval_cases r <;> decide

lemma two_mul_sq_mod_eight (b : ℕ) :
    (2 * b ^ 2) % 8 = 0 ∨ (2 * b ^ 2) % 8 = 2 := by
  have hb := sq_mod_eight b
  rw [Nat.mul_mod]
  rcases hb with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

lemma not_sq_add_two_sq_of_mod_eight {a b p : ℕ} (hp : p % 8 = 5 ∨ p % 8 = 7) :
    a ^ 2 + 2 * b ^ 2 ≠ p := by
  intro h
  have hmod : (a ^ 2 + 2 * b ^ 2) % 8 = p % 8 := by rw [h]
  rw [Nat.add_mod] at hmod
  have ha := sq_mod_eight a
  have hb := two_mul_sq_mod_eight b
  rcases hp with hp | hp <;> rcases ha with ha | ha | ha <;> rcases hb with hb | hb <;>
    simp [ha, hb, hp] at hmod

theorem prime_of_nat_prime_of_mod_eight (p : ℕ) [hp : Fact p.Prime]
    (h57 : p % 8 = 5 ∨ p % 8 = 7) : Prime (p : ℤ√-2) :=
  irreducible_iff_prime.1 <| by_contra fun hpi => by
    obtain ⟨a, b, hab⟩ := sq_add_two_sq_of_nat_prime_of_not_irreducible p hpi
    exact not_sq_add_two_sq_of_mod_eight h57 hab

theorem prime_iff_mod_eight_of_nat_prime (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    Prime (p : ℤ√-2) ↔ p % 8 = 5 ∨ p % 8 = 7 := by
  constructor
  · intro hpi
    have := mod_eight_mem_of_nat_prime_of_prime p hpi
    tauto
  · exact prime_of_nat_prime_of_mod_eight p

theorem exists_sq_add_two_sq_of_prime_mod_eight {p : ℕ} [hp : Fact p.Prime]
    (h13 : p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3) :
    ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = p := by
  rcases h13 with hp2 | h13
  · exact ⟨0, 1, by simp [hp2]⟩
  refine sq_add_two_sq_of_nat_prime_of_not_irreducible p ?_
  intro hirr
  have hpr : Prime (p : ℤ√-2) := irreducible_iff_prime.1 hirr
  have := mod_eight_mem_of_nat_prime_of_prime p hpr
  rcases this with hp2 | h57
  · have : p % 8 = 2 := by omega
    omega
  · omega

end ZsqrtNegTwo

/-! ### Characterization of sums of a square and twice a square -/

lemma sq_add_two_sq_mul {R} [CommRing R] {a b x y u v : R}
    (ha : a = x ^ 2 + 2 * y ^ 2) (hb : b = u ^ 2 + 2 * v ^ 2) :
    ∃ r s : R, a * b = r ^ 2 + 2 * s ^ 2 :=
  ⟨x * u - 2 * y * v, x * v + y * u, by rw [ha, hb]; ring⟩

lemma Nat.sq_add_two_sq_mul {a b x y u v : ℕ}
    (ha : a = x ^ 2 + 2 * y ^ 2) (hb : b = u ^ 2 + 2 * v ^ 2) :
    ∃ r s : ℕ, a * b = r ^ 2 + 2 * s ^ 2 := by
  zify at ha hb ⊢
  obtain ⟨r, s, h⟩ := _root_.sq_add_two_sq_mul ha hb
  refine ⟨r.natAbs, s.natAbs, ?_⟩
  simpa [sq, Int.natCast_natAbs] using h

lemma ZMod.isSquare_neg_two_of_dvd {m n : ℕ} (hd : m ∣ n) (hs : IsSquare (-2 : ZMod n)) :
    IsSquare (-2 : ZMod m) := by
  let f : ZMod n →+* ZMod m := ZMod.castHom hd _
  have hf : f (-2) = (-2 : ZMod m) := by
    rw [map_neg, map_ofNat]
  rw [← hf]
  exact hs.map f

lemma Nat.eq_sq_add_two_sq_of_isSquare_mod_neg_two {n : ℕ}
    (h : IsSquare (-2 : ZMod n)) : ∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2 := by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, rfl⟩
  | one => exact ⟨1, 0, by simp⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hp : IsSquare (-2 : ZMod p) := ZMod.isSquare_neg_two_of_dvd ⟨n, rfl⟩ h
    have hp_rep : ∃ u v : ℕ, u ^ 2 + 2 * v ^ 2 = p := by
      by_cases hp2 : p = 2
      · exact ⟨0, 1, by simp [hp2]⟩
      · have hne2 : p ≠ 2 := hp2
        have h13 : p % 8 = 1 ∨ p % 8 = 3 :=
          (ZMod.exists_sq_eq_neg_two_iff (p := p) hne2).mp hp
        exact ZsqrtNegTwo.exists_sq_add_two_sq_of_prime_mod_eight (Or.inr h13)
    obtain ⟨u, v, huv⟩ := hp_rep
    obtain ⟨x, y, hxy⟩ := ih (ZMod.isSquare_neg_two_of_dvd ⟨p, mul_comm _ _⟩ h)
    exact Nat.sq_add_two_sq_mul huv.symm hxy

lemma ZMod.isSquare_neg_two_of_eq_sq_add_two_sq_of_isCoprime {n x y : ℤ}
    (h : n = x ^ 2 + 2 * y ^ 2) (hc : IsCoprime x y) :
    IsSquare (-2 : ZMod n.natAbs) := by
  -- `y` is invertible mod `n` because `gcd(y, n) = gcd(y, x²) = 1`.
  have hy_n : IsCoprime y n := by
    have hxy2 : IsCoprime y (x ^ 2) := hc.symm.pow_right
    have hn' : n = x ^ 2 + y * (2 * y) := by rw [h]; ring
    simpa [hn'] using hxy2.add_mul_left_right (2 * y)
  obtain ⟨u, v, huv⟩ := hy_n
  refine ⟨x * u, ?_⟩
  have : (x * u) ^ 2 + 2 = n * (u ^ 2 + 2 * v * (1 + u * y)) := by
    have h1 : 1 - u * y = v * n := by linarith [huv]
    calc
      (x * u) ^ 2 + 2 = x ^ 2 * u ^ 2 + 2 := by ring
      _ = (n - 2 * y ^ 2) * u ^ 2 + 2 := by rw [h]; ring
      _ = n * u ^ 2 + 2 * (1 - y ^ 2 * u ^ 2) := by ring
      _ = n * u ^ 2 + 2 * (1 - u * y) * (1 + u * y) := by ring
      _ = n * u ^ 2 + 2 * (v * n) * (1 + u * y) := by rw [h1]
      _ = n * (u ^ 2 + 2 * v * (1 + u * y)) := by ring
  conv_rhs => tactic => norm_cast
  rw [(by norm_cast : (-2 : ZMod n.natAbs) = (-2 : ℤ))]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ?_
  refine Int.natAbs_dvd.mpr ⟨u ^ 2 + 2 * v * (1 + u * y), ?_⟩
  linarith [this]

lemma ZMod.isSquare_neg_two_of_eq_sq_add_two_sq_of_coprime {n x y : ℕ}
    (h : n = x ^ 2 + 2 * y ^ 2) (hc : x.Coprime y) :
    IsSquare (-2 : ZMod n) := by
  zify at h
  exact ZMod.isSquare_neg_two_of_eq_sq_add_two_sq_of_isCoprime h hc.isCoprime

lemma Nat.eq_sq_add_two_sq_iff_eq_sq_mul {n : ℕ} :
    (∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2) ↔
      ∃ a b : ℕ, n = a ^ 2 * b ∧ IsSquare (-2 : ZMod b) := by
  constructor
  · rintro ⟨x, y, h⟩
    by_cases hxy : x = 0 ∧ y = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · rw [h, hxy.1, hxy.2]; simp
      · exact ⟨0, Subsingleton.elim _ _⟩
    · have hg : 0 < Nat.gcd x y := Nat.pos_of_ne_zero (mt Nat.gcd_eq_zero_iff.mp hxy)
      obtain ⟨g, x₁, y₁, _, h₂, h₃, h₄⟩ := Nat.exists_coprime' hg
      refine ⟨g, x₁ ^ 2 + 2 * y₁ ^ 2, ?_, ?_⟩
      · rw [h, h₃, h₄]; ring
      · exact ZMod.isSquare_neg_two_of_eq_sq_add_two_sq_of_coprime rfl h₂
  · rintro ⟨a, b, h₁, h₂⟩
    obtain ⟨x', y', h⟩ := Nat.eq_sq_add_two_sq_of_isSquare_mod_neg_two h₂
    exact ⟨a * x', a * y', by rw [h₁, h]; ring⟩





/-! ### Davenport–Cassels for the sum of three squares -/

/-- The bilinear polar form of `x² + y² + z²`. -/
def sqB (u v : ℚ × ℚ × ℚ) : ℚ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def sqQ (u : ℚ × ℚ × ℚ) : ℚ := sqB u u

lemma sqQ_eq (u : ℚ × ℚ × ℚ) :
    sqQ u = u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2 := by
  simp [sqQ, sqB]; ring

lemma sqB_comm (u v : ℚ × ℚ × ℚ) : sqB u v = sqB v u := by
  simp [sqB]; ring

lemma sqQ_sub (y δ : ℚ × ℚ × ℚ) :
    sqQ (y.1 - δ.1, y.2.1 - δ.2.1, y.2.2 - δ.2.2) =
      sqQ y - 2 * sqB y δ + sqQ δ := by
  simp [sqQ, sqB]; ring

lemma sqQ_add (y δ : ℚ × ℚ × ℚ) :
    sqQ (y.1 + δ.1, y.2.1 + δ.2.1, y.2.2 + δ.2.2) =
      sqQ y + 2 * sqB y δ + sqQ δ := by
  simp [sqQ, sqB]; ring

/-- Rounding each coordinate to the nearest integer. -/
def round3 (ξ : ℚ × ℚ × ℚ) : ℤ × ℤ × ℤ :=
  (round ξ.1, round ξ.2.1, round ξ.2.2)

lemma abs_sub_round3 (ξ : ℚ × ℚ × ℚ) :
    |ξ.1 - round ξ.1| ≤ 1 / 2 ∧
    |ξ.2.1 - round ξ.2.1| ≤ 1 / 2 ∧
    |ξ.2.2 - round ξ.2.2| ≤ 1 / 2 :=
  ⟨abs_sub_round _, abs_sub_round _, abs_sub_round _⟩

lemma sqQ_err_lt_one (ξ : ℚ × ℚ × ℚ) :
    sqQ (ξ.1 - round ξ.1, ξ.2.1 - round ξ.2.1, ξ.2.2 - round ξ.2.2) ≤ 3 / 4 := by
  obtain ⟨h1, h2, h3⟩ := abs_sub_round3 ξ
  have s1 : (ξ.1 - round ξ.1) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (ξ.1 - round ξ.1)) h1 2
    simpa [sq_abs] using this
  have s2 : (ξ.2.1 - round ξ.2.1) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (ξ.2.1 - round ξ.2.1)) h2 2
    simpa [sq_abs] using this
  have s3 : (ξ.2.2 - round ξ.2.2) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (ξ.2.2 - round ξ.2.2)) h3 2
    simpa [sq_abs] using this
  have : sqQ (ξ.1 - round ξ.1, ξ.2.1 - round ξ.2.1, ξ.2.2 - round ξ.2.2) =
      (ξ.1 - round ξ.1) ^ 2 + (ξ.2.1 - round ξ.2.1) ^ 2 + (ξ.2.2 - round ξ.2.2) ^ 2 :=
    sqQ_eq _
  nlinarith

/-- The Davenport–Cassels inversion: if `Q(ξ) = m` and `y` is an integer vector,
the reflected vector also has quadratic value `m`. -/
def dcReflect (ξ : ℚ × ℚ × ℚ) (y : ℚ × ℚ × ℚ) (m : ℚ) : ℚ × ℚ × ℚ :=
  let δ : ℚ × ℚ × ℚ := (ξ.1 - y.1, ξ.2.1 - y.2.1, ξ.2.2 - y.2.2)
  let t := (m - sqQ y) / sqQ δ
  (y.1 - t * δ.1, y.2.1 - t * δ.2.1, y.2.2 - t * δ.2.2)

lemma dcReflect_sqQ (ξ y : ℚ × ℚ × ℚ) (m : ℚ)
    (hξ : sqQ ξ = m) (hδ : sqQ (ξ.1 - y.1, ξ.2.1 - y.2.1, ξ.2.2 - y.2.2) ≠ 0) :
    sqQ (dcReflect ξ y m) = m := by
  set δ : ℚ × ℚ × ℚ := (ξ.1 - y.1, ξ.2.1 - y.2.1, ξ.2.2 - y.2.2)
  set t := (m - sqQ y) / sqQ δ
  have hsum : sqQ ξ = sqQ (y.1 + δ.1, y.2.1 + δ.2.1, y.2.2 + δ.2.2) := by
    have : (y.1 + δ.1, y.2.1 + δ.2.1, y.2.2 + δ.2.2) = ξ := by
      simp [δ]
    simpa [this]
  have hab : sqQ ξ = sqQ y + 2 * sqB y δ + sqQ δ := by
    rw [hsum, sqQ_add]
  have h2B : 2 * sqB y δ = m - sqQ y - sqQ δ := by
    linarith [hξ, hab]
  -- Q(y - tδ) = Q(y) - 2t B(y,δ) + t² Q(δ)
  have hcalc :
      sqQ (y.1 - t * δ.1, y.2.1 - t * δ.2.1, y.2.2 - t * δ.2.2) =
        sqQ y - 2 * t * sqB y δ + t ^ 2 * sqQ δ := by
    simp [sqQ, sqB]; ring
  have ht : t * sqQ δ = m - sqQ y := by
    dsimp [t]
    exact div_mul_cancel₀ (m - sqQ y) hδ
  have hgoal : sqQ y - 2 * t * sqB y δ + t ^ 2 * sqQ δ = m := by
    have h1 : sqQ y - t * (m - sqQ y - sqQ δ) + t ^ 2 * sqQ δ =
        sqQ y - t * (m - sqQ y) + t * sqQ δ + t ^ 2 * sqQ δ := by ring
    have h2 : t * sqQ δ + t ^ 2 * sqQ δ = (m - sqQ y) + t * (m - sqQ y) := by
      calc
        t * sqQ δ + t ^ 2 * sqQ δ = t * sqQ δ + t * (t * sqQ δ) := by ring
        _ = t * sqQ δ + t * (m - sqQ y) := by rw [ht]
        _ = (m - sqQ y) + t * (m - sqQ y) := by rw [ht]
    have h3 : sqQ y - 2 * t * sqB y δ + t ^ 2 * sqQ δ =
        sqQ y - t * (m - sqQ y - sqQ δ) + t ^ 2 * sqQ δ := by
      have : 2 * t * sqB y δ = t * (2 * sqB y δ) := by ring
      rw [this, h2B]
    linarith [h1, h2, h3, ht]
  simpa [dcReflect, δ, t] using (hcalc.trans hgoal)

lemma sqQ_nonneg (u : ℚ × ℚ × ℚ) : 0 ≤ sqQ u := by
  rw [sqQ_eq]; nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, sq_nonneg u.2.2]

lemma sqQ_eq_zero_iff (u : ℚ × ℚ × ℚ) : sqQ u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [sqQ_eq] at h
    have h1 : u.1 = 0 := sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg u.2.1, sq_nonneg u.2.2, h]) (sq_nonneg _))
    have h2 : u.2.1 = 0 := sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg u.1, sq_nonneg u.2.2, h]) (sq_nonneg _))
    have h3 : u.2.2 = 0 := sq_eq_zero_iff.mp (le_antisymm (by nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, h]) (sq_nonneg _))
    ext <;> simp [h1, h2, h3]
  · intro h; simp [h, sqQ, sqB]

/-- Integer vectors, viewed in `ℚ³`. -/
def toQ3 (y : ℤ × ℤ × ℤ) : ℚ × ℚ × ℚ := (y.1, y.2.1, y.2.2)

lemma sqQ_toQ3 (y : ℤ × ℤ × ℤ) :
    sqQ (toQ3 y) = y.1 * y.1 + y.2.1 * y.2.1 + y.2.2 * y.2.2 := by
  simp [sqQ, sqB, toQ3]

/-- A rational vector written with a common positive denominator. -/
structure RatVec3 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℕ
  d_pos : 0 < d

def RatVec3.toQ (v : RatVec3) : ℚ × ℚ × ℚ :=
  (v.a / v.d, v.b / v.d, v.c / v.d)

def RatVec3.den (v : RatVec3) : ℕ := v.d

lemma exists_RatVec3 (ξ : ℚ × ℚ × ℚ) :
    ∃ v : RatVec3, v.toQ = ξ := by
  let d1 := ξ.1.den
  let d2 := ξ.2.1.den
  let d3 := ξ.2.2.den
  let d := d1 * d2 * d3
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos ξ.1.den_pos ξ.2.1.den_pos) ξ.2.2.den_pos
  have hd1 : (d1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ξ.1.den_pos)
  have hd2 : (d2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ξ.2.1.den_pos)
  have hd3 : (d3 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp ξ.2.2.den_pos)
  let a : ℤ := ξ.1.num * d2 * d3
  let b : ℤ := ξ.2.1.num * d1 * d3
  let c : ℤ := ξ.2.2.num * d1 * d2
  refine ⟨⟨a, b, c, d, hd⟩, ?_⟩
  have ha : (a : ℚ) / d = ξ.1 := by
    have hξ := Rat.num_div_den ξ.1
    have hcancel : (ξ.1.num * d2 * d3 : ℚ) / (d1 * d2 * d3) = ξ.1.num / d1 := by
      field_simp [hd1, hd2, hd3]
    calc
      (a : ℚ) / d = (ξ.1.num * d2 * d3 : ℚ) / (d1 * d2 * d3) := by
        simp [a, d, d1, d2, d3]
      _ = ξ.1.num / d1 := hcancel
      _ = ξ.1 := hξ
  have hb : (b : ℚ) / d = ξ.2.1 := by
    have hξ := Rat.num_div_den ξ.2.1
    have hcancel : (ξ.2.1.num * d1 * d3 : ℚ) / (d1 * d2 * d3) = ξ.2.1.num / d2 := by
      field_simp [hd1, hd2, hd3]
    calc
      (b : ℚ) / d = (ξ.2.1.num * d1 * d3 : ℚ) / (d1 * d2 * d3) := by
        simp [b, d, d1, d2, d3]
      _ = ξ.2.1.num / d2 := hcancel
      _ = ξ.2.1 := hξ
  have hc : (c : ℚ) / d = ξ.2.2 := by
    have hξ := Rat.num_div_den ξ.2.2
    have hcancel : (ξ.2.2.num * d1 * d2 : ℚ) / (d1 * d2 * d3) = ξ.2.2.num / d3 := by
      field_simp [hd1, hd2, hd3]
    calc
      (c : ℚ) / d = (ξ.2.2.num * d1 * d2 : ℚ) / (d1 * d2 * d3) := by
        simp [c, d, d1, d2, d3]
      _ = ξ.2.2.num / d3 := hcancel
      _ = ξ.2.2 := hξ
  simp [RatVec3.toQ, ha, hb, hc]

lemma RatVec3.sqQ_toQ (v : RatVec3) :
    sqQ v.toQ = (v.a * v.a + v.b * v.b + v.c * v.c : ℚ) / (v.d * v.d) := by
  have hd : (v.d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp v.d_pos)
  simp [RatVec3.toQ, sqQ, sqB]
  field_simp [hd]


/-- Auxiliary integers for the Davenport–Cassels height drop. -/
def dcB (v : RatVec3) (y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (v.a - v.d * y.1, v.b - v.d * y.2.1, v.c - v.d * y.2.2)

def dcQy (y : ℤ × ℤ × ℤ) : ℤ :=
  y.1 * y.1 + y.2.1 * y.2.1 + y.2.2 * y.2.2

def dcYdot (v : RatVec3) (y : ℤ × ℤ × ℤ) : ℤ :=
  y.1 * v.a + y.2.1 * v.b + y.2.2 * v.c

def dcK (m : ℕ) (v : RatVec3) (y : ℤ × ℤ × ℤ) : ℤ :=
  (m : ℤ) * v.d - 2 * dcYdot v y + v.d * dcQy y

def dcQb (v : RatVec3) (y : ℤ × ℤ × ℤ) : ℤ :=
  let b := dcB v y
  b.1 * b.1 + b.2.1 * b.2.1 + b.2.2 * b.2.2

lemma dcQb_eq_d_mul_K {m : ℕ} (v : RatVec3) (y : ℤ × ℤ × ℤ)
    (hvQ : sqQ v.toQ = m) :
    dcQb v y = v.d * dcK m v y := by
  have hdQ : (v.d : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp v.d_pos)
  have hsum : (v.a * v.a + v.b * v.b + v.c * v.c : ℤ) = (m : ℤ) * v.d * v.d := by
    have hQ : (v.a * v.a + v.b * v.b + v.c * v.c : ℚ) = (m : ℚ) * v.d * v.d := by
      have hform := v.sqQ_toQ
      have : (v.a * v.a + v.b * v.b + v.c * v.c : ℚ) =
          sqQ v.toQ * (v.d : ℚ) * v.d := by
        rw [hform]; field_simp [hdQ]
      rw [this, hvQ]
    exact_mod_cast hQ
  unfold dcQb dcB dcK dcYdot dcQy
  have hexp :
      (v.a - v.d * y.1) * (v.a - v.d * y.1)
        + (v.b - v.d * y.2.1) * (v.b - v.d * y.2.1)
        + (v.c - v.d * y.2.2) * (v.c - v.d * y.2.2)
      = v.a * v.a + v.b * v.b + v.c * v.c
          - 2 * v.d * (y.1 * v.a + y.2.1 * v.b + y.2.2 * v.c)
          + v.d * v.d * (y.1 * y.1 + y.2.1 * y.2.1 + y.2.2 * y.2.2) := by
    ring
  rw [hexp, hsum]
  ring

lemma dcK_eq_d_mul_sqQ_δ {m : ℕ} (v : RatVec3) (y : ℤ × ℤ × ℤ)
    (hvQ : sqQ v.toQ = m) :
    (dcK m v y : ℚ) = (v.d : ℚ) *
      sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) := by
  have hdQ : (v.d : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp v.d_pos)
  have hQb : (dcQb v y : ℚ) = (v.d : ℚ) * (dcK m v y : ℚ) := by
    exact_mod_cast dcQb_eq_d_mul_K v y hvQ
  have hQb' : (dcQb v y : ℚ) =
      ((v.a : ℚ) - v.d * y.1) ^ 2 + ((v.b : ℚ) - v.d * y.2.1) ^ 2 +
        ((v.c : ℚ) - v.d * y.2.2) ^ 2 := by
    simp [dcQb, dcB, pow_two]
  have ha : v.toQ.1 - (y.1 : ℚ) = ((v.a : ℚ) - v.d * y.1) / v.d := by
    simp [RatVec3.toQ]; field_simp [hdQ]
  have hb' : v.toQ.2.1 - (y.2.1 : ℚ) = ((v.b : ℚ) - v.d * y.2.1) / v.d := by
    simp [RatVec3.toQ]; field_simp [hdQ]
  have hc : v.toQ.2.2 - (y.2.2 : ℚ) = ((v.c : ℚ) - v.d * y.2.2) / v.d := by
    simp [RatVec3.toQ]; field_simp [hdQ]
  have hδ :
      sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) =
        (dcQb v y : ℚ) / (v.d : ℚ) ^ 2 := by
    rw [sqQ_eq, ha, hb', hc, hQb']
    field_simp [hdQ]
  have hk : (dcK m v y : ℚ) = (dcQb v y : ℚ) / v.d := by
    field_simp [hdQ]
    linarith [hQb]
  rw [hk, hδ]
  field_simp [hdQ]

lemma dcK_pos_of_δ {m : ℕ} (v : RatVec3) (y : ℤ × ℤ × ℤ)
    (hvQ : sqQ v.toQ = m)
    (hδ0 : sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) ≠ 0) :
    0 < dcK m v y := by
  have h := dcK_eq_d_mul_sqQ_δ v y hvQ
  have hdpos : (0 : ℚ) < v.d := by exact_mod_cast v.d_pos
  have hδpos : 0 < sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) :=
    lt_of_le_of_ne (sqQ_nonneg _) (Ne.symm hδ0)
  have : (0 : ℚ) < dcK m v y := by
    rw [h]; exact mul_pos hdpos hδpos
  exact_mod_cast this

lemma dcK_lt_d {m : ℕ} (v : RatVec3) (y : ℤ × ℤ × ℤ)
    (hvQ : sqQ v.toQ = m)
    (hδle : sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) ≤ 3 / 4) :
    dcK m v y < v.d := by
  have h := dcK_eq_d_mul_sqQ_δ v y hvQ
  have hdpos : (0 : ℚ) < v.d := by exact_mod_cast v.d_pos
  have hle : (dcK m v y : ℚ) ≤ (v.d : ℚ) * (3 / 4) := by
    rw [h]; exact mul_le_mul_of_nonneg_left hδle (le_of_lt hdpos)
  have hlt : (v.d : ℚ) * (3 / 4) < v.d := by nlinarith
  have : (dcK m v y : ℚ) < v.d := lt_of_le_of_lt hle hlt
  exact_mod_cast this

lemma toNat_pos_of_int {k : ℤ} (hk : 0 < k) : 0 < k.toNat := by
  have hk0 : 0 ≤ k := le_of_lt hk
  have hcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  have : (0 : ℤ) < k.toNat := by
    rwa [hcast]
  exact Int.natCast_pos.mp this

lemma toNat_lt_nat {k : ℤ} {n : ℕ} (hk : 0 ≤ k) (hlt : k < n) : k.toNat < n := by
  rw [Int.toNat_lt hk]
  exact_mod_cast hlt

lemma sqQ_toQ3_dcQy (y : ℤ × ℤ × ℤ) : sqQ (toQ3 y) = dcQy y := by
  simp [sqQ, sqB, toQ3, dcQy]

/-- The Davenport–Cassels reflection, written with integer coordinates. -/
lemma dcReflect_coords {m : ℕ} (v : RatVec3) (y : ℤ × ℤ × ℤ)
    (hvQ : sqQ v.toQ = m) (hkpos : 0 < dcK m v y) :
    let k := dcK m v y
    let tnum : ℤ := (m : ℤ) - dcQy y
    let b := dcB v y
    dcReflect v.toQ (toQ3 y) m =
      ((k * y.1 - tnum * b.1 : ℚ) / k,
        (k * y.2.1 - tnum * b.2.1 : ℚ) / k,
        (k * y.2.2 - tnum * b.2.2 : ℚ) / k) := by
  intro k tnum b
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hkpos)
  have hd0 : (v.d : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp v.d_pos)
  have hb1 : (b.1 : ℚ) = (v.d : ℚ) * (v.toQ.1 - y.1) := by
    simp [dcB, RatVec3.toQ, b]; field_simp [hd0]
  have hb2 : (b.2.1 : ℚ) = (v.d : ℚ) * (v.toQ.2.1 - y.2.1) := by
    simp [dcB, RatVec3.toQ, b]; field_simp [hd0]
  have hb3 : (b.2.2 : ℚ) = (v.d : ℚ) * (v.toQ.2.2 - y.2.2) := by
    simp [dcB, RatVec3.toQ, b]; field_simp [hd0]
  have hQδ :
      sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) = (k : ℚ) / v.d := by
    have h := dcK_eq_d_mul_sqQ_δ v y hvQ
    have : (k : ℚ) = (v.d : ℚ) *
        sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) := by
      simpa [k] using h
    field_simp [hd0] at this ⊢
    linarith
  have hQy : sqQ (toQ3 y) = (dcQy y : ℚ) := sqQ_toQ3_dcQy y
  have htnum : (m : ℚ) - sqQ (toQ3 y) = (tnum : ℚ) := by
    simp [tnum, hQy]
  have ht :
      ((m : ℚ) - sqQ (toQ3 y)) /
        sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2) =
          (tnum : ℚ) * v.d / k := by
    rw [htnum, hQδ]; field_simp [hd0, hk0]
  -- Expand the reflection coordinatewise.
  have hexpand (yi bi δi : ℚ) (hbi : bi = (v.d : ℚ) * δi) :
      yi - (((m : ℚ) - sqQ (toQ3 y)) /
        sqQ (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2)) * δi =
        (k * yi - tnum * bi) / k := by
    rw [ht, hbi]
    field_simp [hk0]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [dcReflect, toQ3]
    exact hexpand (y.1 : ℚ) (b.1 : ℚ) (v.toQ.1 - y.1) hb1
  · simp [dcReflect, toQ3]
    exact hexpand (y.2.1 : ℚ) (b.2.1 : ℚ) (v.toQ.2.1 - y.2.1) hb2
  · simp [dcReflect, toQ3]
    exact hexpand (y.2.2 : ℚ) (b.2.2 : ℚ) (v.toQ.2.2 - y.2.2) hb3

/-- If a natural number is a sum of three rational squares, it is a sum of three integer squares. -/
lemma three_sq_of_rat_vec (m : ℕ) :
    ∀ (d : ℕ) (v : RatVec3), v.d = d → sqQ v.toQ = m →
      ∃ a b c : ℤ, a * a + b * b + c * c = m := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro v hvd hvQ
    let y : ℤ × ℤ × ℤ := (round (v.toQ.1), round (v.toQ.2.1), round (v.toQ.2.2))
    let δ : ℚ × ℚ × ℚ :=
      (v.toQ.1 - y.1, v.toQ.2.1 - y.2.1, v.toQ.2.2 - y.2.2)
    have hδle : sqQ δ ≤ 3 / 4 := by
      simpa [δ] using sqQ_err_lt_one v.toQ
    by_cases hδ0 : sqQ δ = 0
    · have hδz : δ = 0 := (sqQ_eq_zero_iff δ).mp hδ0
      have hy1 : (y.1 : ℚ) = v.toQ.1 := by
        have : v.toQ.1 - y.1 = 0 := congrArg (fun t => t.1) hδz
        linarith
      have hy2 : (y.2.1 : ℚ) = v.toQ.2.1 := by
        have : v.toQ.2.1 - y.2.1 = 0 := congrArg (fun t => t.2.1) hδz
        linarith
      have hy3 : (y.2.2 : ℚ) = v.toQ.2.2 := by
        have : v.toQ.2.2 - y.2.2 = 0 := congrArg (fun t => t.2.2) hδz
        linarith
      refine ⟨y.1, y.2.1, y.2.2, ?_⟩
      have : sqQ (toQ3 y) = (m : ℚ) := by
        simp [toQ3, hy1, hy2, hy3]
        simpa [RatVec3.toQ] using hvQ
      have hcast : (y.1 * y.1 + y.2.1 * y.2.1 + y.2.2 * y.2.2 : ℚ) = m := by
        simpa [sqQ_toQ3] using this
      exact_mod_cast hcast
    · have hkpos : 0 < dcK m v y :=
        dcK_pos_of_δ v y hvQ (by simpa [δ] using hδ0)
      have hklt : dcK m v y < v.d :=
        dcK_lt_d v y hvQ (by simpa [δ] using hδle)
      have hkd : (dcK m v y).toNat < d := by
        have := toNat_lt_nat (le_of_lt hkpos) hklt
        simpa [hvd] using this
      let tnum : ℤ := (m : ℤ) - dcQy y
      let b := dcB v y
      let k := dcK m v y
      have hkpos' : 0 < k := hkpos
      let v' : RatVec3 :=
        ⟨k * y.1 - tnum * b.1, k * y.2.1 - tnum * b.2.1, k * y.2.2 - tnum * b.2.2,
          k.toNat, toNat_pos_of_int hkpos'⟩
      have hv'd : v'.d = k.toNat := rfl
      have hkcast : (k.toNat : ℚ) = (k : ℚ) := by
        exact_mod_cast Int.toNat_of_nonneg (le_of_lt hkpos)
      have htoQ : v'.toQ = dcReflect v.toQ (toQ3 y) m := by
        have hcoords := dcReflect_coords v y hvQ hkpos
        simp [RatVec3.toQ, v', k, tnum, b, hkcast] at hcoords ⊢
        exact hcoords.symm
      have hδne : sqQ (v.toQ.1 - (toQ3 y).1, v.toQ.2.1 - (toQ3 y).2.1,
          v.toQ.2.2 - (toQ3 y).2.2) ≠ 0 := by
        simpa [δ, toQ3] using hδ0
      have hv'Q : sqQ v'.toQ = m := by
        rw [htoQ]
        exact dcReflect_sqQ v.toQ (toQ3 y) m hvQ hδne
      exact ih k.toNat hkd v' hv'd hv'Q

lemma three_sq_of_rat {m : ℕ} {ξ : ℚ × ℚ × ℚ} (hξ : sqQ ξ = m) :
    ∃ a b c : ℤ, a * a + b * b + c * c = m := by
  obtain ⟨v, hv⟩ := exists_RatVec3 ξ
  exact three_sq_of_rat_vec m v.d v rfl (by simpa [hv] using hξ)

/-- An integer square is `0`, `1` or `4` modulo `8`. -/
lemma Int.sq_mod_eight (a : ℤ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have h : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨
      a % 8 = 4 ∨ a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by omega
  have hsq : a ^ 2 % 8 = (a % 8) ^ 2 % 8 := by
    simpa [pow_two] using Int.mul_emod a a 8
  rcases h with h | h | h | h | h | h | h | h <;> simp [hsq, h]

/-- No integer congruent to `7` modulo `8` is a sum of three squares. -/
lemma not_three_sq_of_mod_eight {n : ℤ} (hn : n % 8 = 7) :
    ¬ ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  rintro ⟨a, b, c, h⟩
  have hn' : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 7 := by rw [h]; exact hn
  have ha := Int.sq_mod_eight a
  have hb := Int.sq_mod_eight b
  have hc := Int.sq_mod_eight c
  have hsum : (a ^ 2 + b ^ 2 + c ^ 2) % 8 =
      ((a ^ 2 % 8) + (b ^ 2 % 8) + (c ^ 2 % 8)) % 8 := by
    rw [Int.add_emod, Int.add_emod (a ^ 2) (b ^ 2), Int.add_emod]
    simp [Int.add_emod]
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rcases hc with hc | hc | hc <;>
    simp [hsum, ha, hb, hc] at hn'

/-- Pairing a 3-square representation of `4n+1` produces a representation of `8n+2`. -/
lemma eight_n_add_two_of_three_sq {n : ℕ} {α β γ : ℤ}
    (h : α ^ 2 + β ^ 2 + γ ^ 2 = 4 * n + 1) :
    (α + β) ^ 2 + (α - β) ^ 2 + 2 * γ ^ 2 = 8 * n + 2 := by
  linear_combination 2 * h

lemma two_mul_even_sq {γ : ℤ} (h : Even γ) : ∃ c : ℤ, 2 * γ ^ 2 = 8 * c ^ 2 := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [hc]
  ring

/-- If `4n+1` is a sum of three integer squares then `8n+2 = A²+B²+8C²`. -/
lemma form_of_three_sq {n : ℕ} {α β γ : ℤ}
    (h : α ^ 2 + β ^ 2 + γ ^ 2 = 4 * n + 1) (hγ : Even γ) :
    ∃ A B C : ℤ, A ^ 2 + B ^ 2 + 8 * C ^ 2 = 8 * n + 2 := by
  obtain ⟨C, hC⟩ := two_mul_even_sq hγ
  refine ⟨α + β, α - β, C, ?_⟩
  have := eight_n_add_two_of_three_sq h
  linarith

/-- `4n+1` is never of the forbidden shape `4^a(8b+7)`. -/
lemma four_mul_add_one_not_forbidden (n : ℕ) :
    ¬ ∃ a b : ℕ, 4 * n + 1 = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, h⟩
  have hmod : (4 * n + 1) % 4 = 1 := by omega
  cases a with
  | zero =>
    have : (8 * b + 7) % 8 = 7 := by omega
    have h' : (4 * n + 1) % 8 = 1 ∨ (4 * n + 1) % 8 = 5 := by omega
    have : (4 * n + 1) % 8 = 7 := by
      simpa [h, pow_zero] using this
    omega
  | succ a =>
    have : 4 ∣ 4 ^ (a + 1) * (8 * b + 7) := by
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_pow (by decide : 4 ∣ 4) (Nat.succ_ne_zero _)
    have : 4 ∣ 4 * n + 1 := by simpa [h] using this
    omega

/-! Extra companion identities (compiled here before porting). -/

lemma y_term_add_Tp_succ {p : ℕ} (hp : Odd p) :
    ((p + 1) / 2) * (2 * ((p + 1) / 2) + 1) + p * (p + 1) / 2 = (p + 1) ^ 2 := by
  have hdiv : 2 * ((p + 1) / 2) = p + 1 := by
    have : (p + 1) % 2 = 0 := by
      have : p % 2 = 1 := Nat.odd_iff.mp hp
      omega
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
  have hpT : 2 * (p * (p + 1) / 2) = p * (p + 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self p))
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * (((p + 1) / 2) * (2 * ((p + 1) / 2) + 1) + p * (p + 1) / 2)
        = 2 * (((p + 1) / 2) * (2 * ((p + 1) / 2) + 1)) + 2 * (p * (p + 1) / 2) := by ring
    _ = (2 * ((p + 1) / 2)) * (2 * ((p + 1) / 2) + 1) + p * (p + 1) := by
        rw [hpT]; ring
    _ = (p + 1) * ((p + 1) + 1) + p * (p + 1) := by rw [hdiv]
    _ = (p + 1) * (p + 2) + p * (p + 1) := by ring
    _ = (p + 1) * (p + 2 + p) := by ring
    _ = (p + 1) * (2 * p + 2) := by ring
    _ = 2 * (p + 1) ^ 2 := by ring

lemma y_term_add_Tpred {p : ℕ} (hp : Odd p) (hp0 : 0 < p) :
    ((p - 1) / 2) * (2 * ((p - 1) / 2) + 1) + (p - 1) * p / 2 = p * (p - 1) := by
  have hdiv : 2 * ((p - 1) / 2) = p - 1 := by
    have : p % 2 = 1 := Nat.odd_iff.mp hp
    exact Nat.mul_div_cancel' (by omega)
  have hT : 2 * ((p - 1) * p / 2) = (p - 1) * p := by
    have : Even ((p - 1) * p) := by
      have : Even (p - 1) := by
        have : p % 2 = 1 := Nat.odd_iff.mp hp
        exact Nat.even_iff.mpr (by omega)
      exact this.mul_right p
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp this)
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  calc
    2 * (((p - 1) / 2) * (2 * ((p - 1) / 2) + 1) + (p - 1) * p / 2)
        = (2 * ((p - 1) / 2)) * (2 * ((p - 1) / 2) + 1) + 2 * ((p - 1) * p / 2) := by ring
    _ = (p - 1) * ((p - 1) + 1) + (p - 1) * p := by rw [hdiv, hT]
    _ = (p - 1) * p + (p - 1) * p := by
        congr 2; exact Nat.sub_add_cancel hp0
    _ = 2 * (p * (p - 1)) := by ring

lemma y_term_add_Tpred_succ {p : ℕ} (hp : Odd p) (hp0 : 0 < p) :
    ((p + 1) / 2) * (2 * ((p + 1) / 2) + 1) + (p - 1) * p / 2 = p ^ 2 + p + 1 := by
  have hdiv : 2 * ((p + 1) / 2) = p + 1 := by
    have : (p + 1) % 2 = 0 := by
      have : p % 2 = 1 := Nat.odd_iff.mp hp
      omega
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
  have hT : 2 * ((p - 1) * p / 2) = (p - 1) * p := by
    have : Even ((p - 1) * p) := by
      have : Even (p - 1) := by
        have : p % 2 = 1 := Nat.odd_iff.mp hp
        exact Nat.even_iff.mpr (by omega)
      exact this.mul_right p
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp this)
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  have hlhs :
      2 * (((p + 1) / 2) * (2 * ((p + 1) / 2) + 1) + (p - 1) * p / 2)
        = (p + 1) * (p + 2) + (p - 1) * p := by
    calc
      2 * (((p + 1) / 2) * (2 * ((p + 1) / 2) + 1) + (p - 1) * p / 2)
          = (2 * ((p + 1) / 2)) * (2 * ((p + 1) / 2) + 1) + 2 * ((p - 1) * p / 2) := by ring
      _ = (p + 1) * ((p + 1) + 1) + (p - 1) * p := by rw [hdiv, hT]
      _ = (p + 1) * (p + 2) + (p - 1) * p := by ring
  have : (p + 1) * (p + 2) + (p - 1) * p = 2 * (p ^ 2 + p + 1) := by
    have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp0
    have hadd : (p - 1) * p + p = p * p := by
      calc
        (p - 1) * p + p = (p - 1 + 1) * p := by ring
        _ = p * p := by rw [Nat.sub_add_cancel hp1]
    have hL : (p + 1) * (p + 2) + (p - 1) * p + p
        = (p + 1) * (p + 2) + p * p := by rw [Nat.add_assoc, hadd]
    have hR : 2 * (p ^ 2 + p + 1) + p = (p + 1) * (p + 2) + p * p := by ring
    have hLR : (p + 1) * (p + 2) + (p - 1) * p + p = 2 * (p ^ 2 + p + 1) + p :=
      hL.trans hR.symm
    exact Nat.add_right_cancel hLR
  rw [hlhs, this]

-- Compile-check the extra Bertrand scale arguments used in Spec.lean.
lemma bertrand_half_scale {n : ℕ} (h : 1500 < n) :
    0 < n.sqrt / 2 ∧
    ∀ p, Nat.Prime p → n.sqrt / 2 < p → p ≠ 2 := by
  have hsq : 38 ≤ n.sqrt := by
    have : 38 * 38 ≤ n := by omega
    exact Nat.le_sqrt.mpr this
  constructor
  · omega
  · intro p hp hpgt hp2
    have : n.sqrt / 2 < 2 := by simpa [hp2] using hpgt
    omega

lemma bertrand_twon_scale {n : ℕ} (h : 1500 < n) :
    0 < (2 * n).sqrt :=
  Nat.sqrt_pos.mpr (by omega)

lemma ZMod.isSquare_neg_two_mul {m n : ℕ} (hc : m.Coprime n)
    (hm : IsSquare (-2 : ZMod m)) (hn : IsSquare (-2 : ZMod n)) :
    IsSquare (-2 : ZMod (m * n)) := by
  have hpair : (-2 : ZMod m × ZMod n) = (-2, -2) := by
    ext <;> simp
  have hsq : IsSquare (-2 : ZMod m × ZMod n) := by
    rw [hpair]
    obtain ⟨x, hx⟩ := hm
    obtain ⟨y, hy⟩ := hn
    exact ⟨(x, y), by simp [hx, hy]⟩
  have := hsq.map (ZMod.chineseRemainder hc).symm
  convert this
  have : (ZMod.chineseRemainder hc).symm 2 = 2 := by
    rw [← map_ofNat (ZMod.chineseRemainder hc).symm 2]
  simp [this]

lemma Nat.mod_eight_ne_five_or_seven_of_mem_primeFactors_of_isSquare_neg_two
    {p n : ℕ} (hp : p ∈ n.primeFactors) (hs : IsSquare (-2 : ZMod n)) :
    p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3 := by
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hpp⟩
  have hp2 : IsSquare (-2 : ZMod p) :=
    ZMod.isSquare_neg_two_of_dvd (Nat.dvd_of_mem_primeFactors hp) hs
  by_cases h2 : p = 2
  · exact Or.inl h2
  · exact Or.inr ((ZMod.exists_sq_eq_neg_two_iff (p := p) h2).mp hp2)

lemma ZMod.isSquare_neg_two_iff_forall_mem_primeFactors {n : ℕ} (hn : Squarefree n) :
    IsSquare (-2 : ZMod n) ↔ ∀ q ∈ n.primeFactors, q = 2 ∨ q % 8 = 1 ∨ q % 8 = 3 := by
  refine ⟨fun H q hq ↦
    Nat.mod_eight_ne_five_or_seven_of_mem_primeFactors_of_isSquare_neg_two hq H, fun H ↦ ?_⟩
  induction n using induction_on_primes with
  | zero => exact False.elim (hn.ne_zero rfl)
  | one => exact ⟨0, Subsingleton.elim _ _⟩
  | prime_mul p n hpp ih =>
    have : Fact p.Prime := ⟨hpp⟩
    have hcp : p.Coprime n := by
      by_contra hc
      exact hpp.not_isUnit (hn p <| mul_dvd_mul_left p <| hpp.dvd_iff_not_coprime.mpr hc)
    have hp₁ : IsSquare (-2 : ZMod p) := by
      have hp_mem : p ∈ (p * n).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpp, Nat.dvd_mul_right .., Squarefree.ne_zero hn⟩
      have hform := H _ hp_mem
      by_cases hp2 : p = 2
      · subst hp2
        refine ⟨0, ?_⟩
        have h20 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
        simp [h20]
      · exact (ZMod.exists_sq_eq_neg_two_iff (p := p) hp2).mpr (hform.resolve_left hp2)
    exact ZMod.isSquare_neg_two_mul hcp hp₁ <| ih hn.of_mul_right fun q hqp => H q <|
      Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hqp,
        dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hqp) _, Squarefree.ne_zero hn⟩

lemma Nat.eq_sq_add_two_sq_iff_primes {n : ℕ} :
    (∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2) ↔
      ∀ q ∈ n.primeFactors, q % 8 = 5 ∨ q % 8 = 7 → Even (padicValNat q n) := by
  rcases n.eq_zero_or_pos with (rfl | hn₀)
  · exact ⟨fun _ q _ _ ↦ padicValNat.zero.symm ▸ Even.zero, fun _ ↦ ⟨0, 0, rfl⟩⟩
  refine Nat.eq_sq_add_two_sq_iff_eq_sq_mul.trans ⟨fun ⟨a, b, h₁, h₂⟩ q hq h ↦ ?_, fun H ↦ ?_⟩
  · have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    have : q ∣ b → q ∈ b.primeFactors := by grind
    grind (splits := 10) [padicValNat.mul, padicValNat.pow,
      padicValNat.eq_zero_of_not_dvd,
      Nat.mod_eight_ne_five_or_seven_of_mem_primeFactors_of_isSquare_neg_two]
  · obtain ⟨b, a, hb₀, ha₀, hab, hb⟩ := Nat.sq_mul_squarefree_of_pos hn₀
    refine ⟨a, b, hab.symm, (ZMod.isSquare_neg_two_iff_forall_mem_primeFactors hb).mpr ?_⟩
    intro q hq
    have hqP : Nat.Prime q := Nat.prime_of_mem_primeFactors hq
    have : Fact q.Prime := ⟨hqP⟩
    have hdivn : q ∣ n :=
      (Nat.dvd_of_mem_primeFactors hq).trans ⟨a ^ 2, by rw [mul_comm, hab]⟩
    have : b.factorization q = 1 := by
      have hle : b.factorization q ≤ 1 := hb.natFactorization_le_one q
      have hpos : 1 ≤ b.factorization q :=
        (hqP.dvd_iff_one_le_factorization (ne_of_gt hb₀)).mp (Nat.dvd_of_mem_primeFactors hq)
      exact le_antisymm hle hpos
    by_contra hbad
    have h57 : q % 8 = 5 ∨ q % 8 = 7 := by
      have hq2 : q ≠ 2 := fun h2 => hbad (Or.inl h2)
      have hodd : q % 2 = 1 := (hqP.eq_two_or_odd).resolve_left hq2
      have hq1 : q % 8 ≠ 1 := fun h => hbad (Or.inr (Or.inl h))
      have hq3 : q % 8 ≠ 3 := fun h => hbad (Or.inr (Or.inr h))
      have hmod : q % 8 < 8 := Nat.mod_lt q (by decide)
      have heven8 : ∀ r : ℕ, r % 8 = 0 ∨ r % 8 = 2 ∨ r % 8 = 4 ∨ r % 8 = 6 → r % 2 = 0 := by
        intro r hr
        have : 2 ∣ r % 8 := by rcases hr with hr | hr | hr | hr <;> simp [hr]
        have hsplit : r = 8 * (r / 8) + r % 8 := (Nat.div_add_mod r 8).symm
        have : 2 ∣ r := by
          rw [hsplit]
          exact dvd_add (dvd_mul_of_dvd_left (by decide : 2 ∣ 8) _) this
        exact Nat.mod_eq_zero_of_dvd this
      match hq8 : q % 8 with
      | 0 => exact (by have := heven8 q (Or.inl hq8); omega)
      | 1 => exact (hq1 hq8).elim
      | 2 => exact (by have := heven8 q (Or.inr (Or.inl hq8)); omega)
      | 3 => exact (hq3 hq8).elim
      | 4 => exact (by have := heven8 q (Or.inr (Or.inr (Or.inl hq8))); omega)
      | 5 => exact Or.inl rfl
      | 6 => exact (by have := heven8 q (Or.inr (Or.inr (Or.inr hq8))); omega)
      | 7 => exact Or.inr rfl
      | n+8 =>
        omega
    have hmem_n : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqP, hdivn, hn₀.ne'⟩
    have he := H q hmem_n h57
    have hbval : padicValNat q b = 1 := by
      rwa [← Nat.factorization_def b hqP]
    have ha0 : a ≠ 0 := ha₀.ne'
    have hb0 : b ≠ 0 := hb₀.ne'
    have hmul := padicValNat.mul (p := q) (a := a ^ 2) (b := b) (pow_ne_zero 2 ha0) hb0
    have hval : padicValNat q n = padicValNat q (a ^ 2) + 1 := by
      rw [hab] at hmul
      simpa [hbval] using hmul
    have hpow := padicValNat.pow (p := q) (n := 2) ha0
    have hodd : Odd (padicValNat q n) := by
      rw [hval, hpow]
      exact (even_two.mul_right _).add_one
    exact Nat.not_even_iff_odd.mpr hodd he



/-! ### InS via the form `a² + 8b²` -/

def InS (m : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + y * (2 * y + 1) = m

lemma inS_iff_eight_form {m : ℕ} :
    InS m ↔ ∃ a b : ℕ, a % 4 = 1 ∧ a ^ 2 + 8 * b ^ 2 = 8 * m + 1 := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨4 * y + 1, x, by omega, ?_⟩
    calc
      (4 * y + 1) ^ 2 + 8 * x ^ 2
          = 16 * y ^ 2 + 8 * y + 1 + 8 * x ^ 2 := by ring
      _ = 8 * (x ^ 2 + y * (2 * y + 1)) + 1 := by ring
      _ = 8 * m + 1 := by rw [h]
  · rintro ⟨a, b, ha, h⟩
    obtain ⟨y, hy⟩ : ∃ y, a = 4 * y + 1 := ⟨a / 4, by omega⟩
    refine ⟨b, y, ?_⟩
    have hz : (4 * y + 1) ^ 2 + 8 * b ^ 2
        = 8 * (b ^ 2 + y * (2 * y + 1)) + 1 := by ring
    have : 8 * (b ^ 2 + y * (2 * y + 1)) + 1 = 8 * m + 1 := by
      rw [← hz, ← hy, h]
    have : 8 * (b ^ 2 + y * (2 * y + 1)) = 8 * m := by omega
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) this

lemma even_im_of_form_mod_eight {u v : ℕ}
    (h : (u ^ 2 + 2 * v ^ 2) % 8 = 1) : Even v := by
  rw [Nat.even_iff]
  have hred : ((u % 8) ^ 2 + 2 * (v % 8) ^ 2) % 8 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.pow_mod] at h
    simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] using h
  have h2 : v % 2 = (v % 8) % 2 := (Nat.mod_mod_of_dvd v (by decide : 2 ∣ 8)).symm
  rw [h2]
  have hv : v % 8 < 8 := Nat.mod_lt v (by decide)
  have hu : u % 8 < 8 := Nat.mod_lt u (by decide)
  revert hred
  interval_cases v % 8 <;> interval_cases u % 8 <;> decide

lemma inS_of_sq_add_two_sq {m u v : ℕ} (hu : u % 4 = 1) (hv : Even v)
    (h : u ^ 2 + 2 * v ^ 2 = 8 * m + 1) : InS m := by
  obtain ⟨w, rfl⟩ := hv
  refine inS_iff_eight_form.2 ⟨u, w, hu, ?_⟩
  convert h using 1
  ring


open Polynomial

lemma exists_sq_add_sq_eq_neg_one_mod_prime {p : ℕ} [hp : Fact p.Prime]
    (hodd : p ≠ 2) : ∃ x y : ZMod p, x ^ 2 + y ^ 2 = -1 := by
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card p]
    exact (hp.out.eq_two_or_odd).resolve_left hodd
  have hf : degree ((X : (ZMod p)[X]) ^ 2) = 2 := by
    simpa using (degree_X_pow (R := ZMod p) 2)
  have hg : degree ((X : (ZMod p)[X]) ^ 2 + C 1) = 2 := by
    have hX : degree ((X : (ZMod p)[X]) ^ 2) = 2 := by
      simpa using (degree_X_pow (R := ZMod p) 2)
    have hC : degree (C (1 : ZMod p)) = 0 := degree_C one_ne_zero
    have hlt : degree (C (1 : ZMod p)) < degree ((X : (ZMod p)[X]) ^ 2) := by
      rw [hC, hX]; exact WithBot.coe_lt_coe.mpr (by decide)
    rw [degree_add_eq_left_of_degree_lt hlt, hX]
  obtain ⟨a, b, hab⟩ :=
    FiniteField.exists_root_sum_quadratic (R := ZMod p) hf hg hcard
  refine ⟨a, b, ?_⟩
  have : a ^ 2 + (b ^ 2 + 1) = 0 := by
    simpa [eval_add, eval_pow, eval_X, eval_C] using hab
  linear_combination this

lemma exists_sq_add_sq_eq_neg_one_mod_prime_nat {p : ℕ} [hp : Fact p.Prime]
    (hodd : p ≠ 2) : ∃ x y : ℕ, (x ^ 2 + y ^ 2 + 1) % p = 0 := by
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_eq_neg_one_mod_prime (p := p) hodd
  refine ⟨x.val, y.val, ?_⟩
  have hz : (x ^ 2 + y ^ 2 + 1 : ZMod p) = 0 := by rw [hxy]; ring
  have : ((x.val ^ 2 + y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.natCast_val] using hz
  have hdvd : p ∣ x.val ^ 2 + y.val ^ 2 + 1 := (ZMod.natCast_eq_zero_iff _ p).mp this
  exact Nat.mod_eq_zero_of_dvd hdvd


/-! ### Hensel lifting for \(x^2+y^2+1\equiv 0\) and CRT -/

lemma zmod_two_mul_ne_zero {p : ℕ} [hp : Fact p.Prime] {y : ZMod p}
    (hodd : p ≠ 2) (hy : y ≠ 0) : (2 * y : ZMod p) ≠ 0 := by
  intro h
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : (2 : ℕ) ≡ 0 [MOD p] := by
      have := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
      exact Nat.modEq_zero_iff_dvd.mpr this
    have : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp this
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
    exact hodd this
  exact hy (mul_eq_zero.mp h |>.resolve_left h2)

/-- One Hensel step: lift a simple root of \(X^2 + y^2 + 1\) in the second variable. -/
lemma hensel_sq_add_sq_neg_one_step {p k : ℕ} [hp : Fact p.Prime]
    (hodd : p ≠ 2) (hk : 0 < k)
    {x y : ℕ} {m : ℤ}
    (hcong : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + 1 = m * (p : ℤ) ^ k)
    (hy : (y : ZMod p) ≠ 0) :
    ∃ t : ℕ, ((x : ℤ) ^ 2 + (y + t * (p : ℤ) ^ k) ^ 2 + 1)
        % ((p : ℤ) ^ (k + 1)) = 0 := by
  -- Want 2 y t + m ≡ 0 (mod p), i.e. t ≡ -m * (2y)⁻¹ (mod p)
  have hne : (2 * (y : ZMod p)) ≠ 0 := zmod_two_mul_ne_zero hodd hy
  let u := Ring.inverse (2 * (y : ZMod p))
  have hinv : (2 * (y : ZMod p)) * u = 1 := by
    simpa [u] using mul_inv_cancel₀ hne
  refine ⟨((-m : ZMod p) * u).val, ?_⟩
  set t := ((-m : ZMod p) * u).val
  have htmod : (t : ZMod p) = (-m : ZMod p) * u := by
    simp [t, ZMod.natCast_val]
  -- Expand the new value
  have hexp :
      (x : ℤ) ^ 2 + (y + t * (p : ℤ) ^ k) ^ 2 + 1
        = (m + 2 * y * t) * (p : ℤ) ^ k + (t : ℤ) ^ 2 * (p : ℤ) ^ (2 * k) := by
    have := hcong
    linear_combination this
  -- p^k divides the first summand; p^{2k} divides the second; since k≥1, 2k ≥ k+1
  have h2k : k + 1 ≤ 2 * k := by omega
  -- Show p^{k+1} divides (m + 2 y t) * p^k, i.e. p divides (m+2yt)
  have hdiv : (p : ℤ) ∣ (m + 2 * y * t) := by
    have : (m + 2 * y * t : ZMod p) = 0 := by
      have : (2 * (y : ZMod p)) * (t : ZMod p) = -m := by
        rw [htmod, ← mul_assoc, hinv, one_mul]
      linear_combination this
    exact (ZMod.intCast_eq_zero_iff _ p).mp (by simpa using this)
  obtain ⟨q, hq⟩ := hdiv
  have : (x : ℤ) ^ 2 + (y + t * (p : ℤ) ^ k) ^ 2 + 1
      = q * (p : ℤ) ^ (k + 1) + (t : ℤ) ^ 2 * (p : ℤ) ^ (2 * k) := by
    rw [hexp, hq]; ring
  have : (p : ℤ) ^ (k + 1)
      ∣ (x : ℤ) ^ 2 + (y + t * (p : ℤ) ^ k) ^ 2 + 1 := by
    rw [this]
    refine dvd_add ⟨q, by ring⟩ ?_
    refine dvd_mul_of_dvd_right ?_ _
    exact pow_dvd_pow _ h2k
  exact Int.emod_eq_zero_of_dvd this

