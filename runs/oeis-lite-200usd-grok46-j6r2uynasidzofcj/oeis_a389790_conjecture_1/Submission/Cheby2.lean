import FormalConjectures.Util.ProblemImports
open Classical
open Nat
/-! ### Chebyshev lower bound (Erdős / central binomial)

We prove `ψ (2n) ≥ n * Real.log 4 - Real.log n` and deduce a lower bound on `π`.
This is used to guarantee many interprimes in dyadic intervals.
-/

open Finset Real
open ArithmeticFunction hiding log
open scoped Chebyshev

theorem floor_two_mul_sub_two_floor (n d : ℕ) (hd : 0 < d) :
    (2 * n / d : ℕ) = 2 * (n / d : ℕ) ∨ (2 * n / d : ℕ) = 2 * (n / d : ℕ) + 1 := by
  set q := n / d
  set r := n % d
  have hn : n = d * q + r := (Nat.div_add_mod n d).symm
  have hr : r < d := Nat.mod_lt n hd
  have h2n : 2 * n = d * (2 * q) + 2 * r := by
    rw [hn]; ring
  by_cases h : 2 * r < d
  · left
    have := Nat.div_eq_of_lt_le
      (by
        have : d * (2 * q) ≤ 2 * n := by
          rw [h2n]; omega
        exact this)
      (by
        have : 2 * n < d * (2 * q + 1) := by
          rw [h2n]
          have : 2 * r < d := h
          nlinarith)
    simpa [q] using this
  · right
    have hge : d ≤ 2 * r := Nat.le_of_not_gt h
    have hlt : 2 * r < 2 * d := by nlinarith
    have := Nat.div_eq_of_lt_le
      (by
        have : d * (2 * q + 1) ≤ 2 * n := by
          rw [h2n]; omega
        exact this)
      (by
        have : 2 * n < d * (2 * q + 2) := by
          rw [h2n]
          nlinarith)
    simpa [q] using this

theorem two_mul_div_le (n d : ℕ) : 2 * (n / d) ≤ 2 * n / d := by
  by_cases hd : d = 0
  · subst hd; simp
  · have h := floor_two_mul_sub_two_floor n d (Nat.pos_of_ne_zero hd)
    omega

theorem floor_two_mul_sub_two_floor_le_one (n d : ℕ) (hd : 0 < d) :
    (2 * n / d : ℕ) - 2 * (n / d : ℕ) ≤ 1 := by
  have h := floor_two_mul_sub_two_floor n d hd
  omega

theorem log_factorial_eq_sum_Icc (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ k ∈ Icc 1 n, Real.log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [factorial]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [factorial_succ, cast_mul, Real.log_mul (by exact_mod_cast factorial_pos n)
          (by exact_mod_cast succ_pos n)]
      have hI : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
        ext x
        simp [Nat.le_succ_iff]
        omega
      rw [hI, sum_insert]
      · rw [ih]; ac_rfl
      · simp

theorem divisors_eq_filter_Icc {k n : ℕ} (hk : k ∈ Icc 1 n) :
    k.divisors = (Icc 1 n).filter (· ∣ k) := by
  ext d
  simp only [mem_divisors, mem_filter, mem_Icc]
  constructor
  · intro ⟨hdvd, hk0⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by simp at hk; omega)
    have hdle : d ≤ k := Nat.le_of_dvd (by simp at hk; omega) hdvd
    simp at hk
    exact ⟨⟨hdpos, hdle.trans hk.2⟩, hdvd⟩
  · intro ⟨⟨hd1, hdn⟩, hdvd⟩
    simp at hk
    exact ⟨hdvd, by omega⟩

theorem log_factorial_eq_sum_vonMangoldt (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ) := by
  rw [log_factorial_eq_sum_Icc]
  have h1 : ∑ k ∈ Icc 1 n, Real.log (k : ℝ) = ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, Λ d := by
    refine sum_congr rfl fun k hk => ?_
    exact (vonMangoldt_sum (n := k)).symm
  rw [h1]
  have h2 : ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, Λ d =
      ∑ k ∈ Icc 1 n, ∑ d ∈ (Icc 1 n).filter (· ∣ k), Λ d := by
    refine sum_congr rfl fun k hk => ?_
    rw [divisors_eq_filter_Icc hk]
  rw [h2]
  have h3 : ∑ k ∈ Icc 1 n, ∑ d ∈ (Icc 1 n).filter (· ∣ k), Λ d =
      ∑ d ∈ Icc 1 n, ∑ k ∈ (Icc 1 n).filter (d ∣ ·), Λ d := by
    simp_rw [sum_filter]
    rw [sum_comm]
  rw [h3]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_const, nsmul_eq_mul, mul_comm]
  have hI : Icc 1 n = Ioc 0 n := by
    ext x; simp [Nat.pos_iff_ne_zero]; constructor <;> omega
  have hcard : #{k ∈ Icc 1 n | d ∣ k} = n / d := by
    rw [hI, Nat.Ioc_filter_dvd_card_eq_div]
  simp [hcard]

theorem log_centralBinom_eq_sum (n : ℕ) :
    Real.log (n.centralBinom : ℝ) =
      ∑ d ∈ Icc 1 (2 * n), Λ d * ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast factorial_pos n
  have hpos2 : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast factorial_pos (2 * n)
  have hC : (n.centralBinom : ℝ) = (2 * n).factorial / (n.factorial : ℝ) ^ 2 := by
    rw [centralBinom, cast_div_of_dvd]
    · rw [cast_mul, cast_pow]; ring
    · exact factorial_mul_factorial_dvd_factorial_add n n
    · exact pow_ne_zero 2 (by exact_mod_cast (factorial_pos n).ne')
  rw [hC, Real.log_div hpos2.ne' (pow_ne_zero 2 hpos.ne'), Real.log_pow]
  rw [log_factorial_eq_sum_vonMangoldt (2 * n), log_factorial_eq_sum_vonMangoldt n]
  have hsplit :
      ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ) =
        ∑ d ∈ Icc 1 (2 * n), Λ d * (n / d : ℕ) := by
    have hdisj : Disjoint (Icc 1 n) (Icc (n + 1) (2 * n)) := by
      refine disjoint_left.2 ?_
      intro x hx hy
      simp at hx hy
      omega
    have hunion : Icc 1 n ∪ Icc (n + 1) (2 * n) = Icc 1 (2 * n) := by
      ext x; simp; omega
    rw [← hunion, sum_union hdisj]
    have htail : ∑ d ∈ Icc (n + 1) (2 * n), Λ d * (n / d : ℕ) = 0 := by
      apply sum_eq_zero
      intro d hd
      simp at hd
      have : n / d = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
    simp [htail]
  rw [hsplit]
  simp_rw [two_mul (∑ d ∈ Icc 1 (2 * n), Λ d * (n / d : ℕ)), ← sum_add_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hle : 2 * (n / d) ≤ 2 * n / d := two_mul_div_le n d
  have : ((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) =
      ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℕ) := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_two]
    ring
  rw [this]
  ring

theorem log_centralBinom_le_psi (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.centralBinom : ℝ) ≤ Chebyshev.psi (2 * n) := by
  rw [log_centralBinom_eq_sum, Chebyshev.psi_eq_sum_Icc]
  have hcast : (⌊((2 * n : ℕ) : ℝ)⌋₊) = 2 * n := by
    rw [Nat.floor_coe]
  rw [hcast]
  refine sum_le_sum fun d hd => ?_
  have hd0 : 0 < d := by simp at hd; omega
  have hcoeff : ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℝ) ≤ 1 := by
    have hle : (2 * n / d : ℕ) - 2 * (n / d : ℕ) ≤ 1 :=
      floor_two_mul_sub_two_floor_le_one n d hd0
    exact_mod_cast hle
  have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
  have : Λ d * ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℝ) ≤ Λ d * 1 :=
    mul_le_mul_of_nonneg_left hcoeff hΛ
  simpa using this

theorem psi_ge_mul_log4_sub_log (n : ℕ) (hn : 4 ≤ n) :
    n * Real.log 4 - Real.log n ≤ Chebyshev.psi (2 * n) := by
  have hlt := Nat.four_pow_lt_mul_centralBinom n hn
  have hpos : (0 : ℝ) < n.centralBinom := by exact_mod_cast centralBinom_pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hn)
  have : (4 : ℝ) ^ n < n * n.centralBinom := by exact_mod_cast hlt
  have hlog : n * Real.log 4 < Real.log n + Real.log n.centralBinom := by
    have := Real.log_lt_log (by positivity : (0 : ℝ) < 4 ^ n) this
    rw [Real.log_pow, Real.log_mul hn0.ne' hpos.ne'] at this
    simpa [mul_comm] using this
  have : n * Real.log 4 - Real.log n < Real.log n.centralBinom := by linarith
  have hle : Real.log n.centralBinom ≤ Chebyshev.psi (2 * n) := log_centralBinom_le_psi n (by omega)
  linarith
