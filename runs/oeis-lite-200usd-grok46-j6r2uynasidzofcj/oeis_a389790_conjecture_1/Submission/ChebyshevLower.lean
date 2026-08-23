import FormalConjectures.Util.ProblemImports
open Classical
open Nat Finset Real
open ArithmeticFunction hiding log
open scoped Nat.Prime Chebyshev

theorem log_factorial_eq_sum_Icc (n : ℕ) :
    log (n.factorial : ℝ) = ∑ k ∈ Icc 1 n, log (k : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [factorial]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      rw [factorial_succ, cast_mul, log_mul (by exact_mod_cast factorial_pos n)
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

/-- `log n! = ∑_{d ≤ n} Λ(d) * ⌊n / d⌋`. -/
theorem log_factorial_eq_sum_vonMangoldt (n : ℕ) :
    log (n.factorial : ℝ) = ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ) := by
  rw [log_factorial_eq_sum_Icc]
  have h1 : ∑ k ∈ Icc 1 n, log (k : ℝ) = ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, Λ d := by
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



theorem floor_two_mul_sub_two_floor_le_one (n d : ℕ) (hd : 0 < d) :
    (2 * n / d : ℕ) - 2 * (n / d : ℕ) ≤ 1 := by
  have := Nat.mod_add_div (2 * n) d
  have h1 := Nat.div_add_mod n d
  -- 2n = d * (2n/d) + (2n%d), n = d*(n/d) + n%d
  -- 2n/d = 2*(n/d) or 2*(n/d)+1
  have : 2 * n / d ≤ 2 * (n / d) + 1 := by
    have hn : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
    have : 2 * n = d * (2 * (n / d)) + 2 * (n % d) := by
      rw [hn]; ring
    have hmod : 2 * (n % d) < 2 * d := by
      have : n % d < d := Nat.mod_lt n hd
      omega
    have hle : 2 * n / d ≤ 2 * (n / d) + 1 := by
      -- if 2*(n%d) < d then 2n/d = 2*(n/d), else 2n/d = 2*(n/d)+1
      have : 2 * n = d * (2 * (n / d) + 1) + (2 * (n % d) - d) ∨
             2 * n = d * (2 * (n / d)) + 2 * (n % d) := by
        by_cases h : d ≤ 2 * (n % d)
        · left
          have : 2 * n = d * (2 * (n / d)) + 2 * (n % d) := by
            have hn' : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
            rw [hn']; ring
          omega
        · right
          have hn' : n = d * (n / d) + n % d := (Nat.div_add_mod n d).symm
          rw [hn']; ring
      cases this with
      | inl h =>
        have : 2 * (n % d) - d < d := by omega
        have := Nat.div_eq_of_lt_le
          (by
            have : d * (2 * (n / d) + 1) ≤ 2 * n := by omega
            exact this)
          (by
            have : 2 * n - d * (2 * (n / d) + 1) < d := by omega
            -- use Nat.div_lt_iff?
            omega)
        omega
      | inr h =>
        have : 2 * (n % d) < d := by omega
        have : 2 * n / d = 2 * (n / d) := by
          rw [h]
          exact Nat.mul_add_div_right_of_lt (by omega) (by omega)
        omega
    exact hle
  omega

theorem log_centralBinom_eq_sum (n : ℕ) :
    log (n.centralBinom : ℝ) =
      ∑ d ∈ Icc 1 (2 * n), Λ d * ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast factorial_pos n
  have hpos2 : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast factorial_pos (2 * n)
  -- C(2n,n) = (2n)! / (n!)^2
  have hC : (n.centralBinom : ℝ) = (2 * n).factorial / (n.factorial : ℝ) ^ 2 := by
    rw [centralBinom, cast_div_of_dvd]
    · rw [cast_mul, cast_pow]; ring
    · exact factorial_mul_factorial_dvd_factorial_add n n
    · exact pow_ne_zero 2 (by exact_mod_cast (factorial_pos n).ne')
  rw [hC, log_div hpos2.ne' (pow_ne_zero 2 hpos.ne'), log_pow]
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
  have : ((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ) =
      ((2 * n / d : ℕ) - 2 * (n / d : ℕ) : ℕ) := by
    have hle : 2 * (n / d) ≤ 2 * n / d := by
      have := Nat.mul_div_le n d
      -- 2 * (n/d) ≤ 2n/d
      have hd0 : 0 < d := by simp at hd; omega
      have := (floor_two_mul_sub_two_floor_le_one n d hd0)
      -- actually we need 2*(n/d) ≤ 2n/d which is standard
      exact Nat.mul_div_mul_left_le.trans ?wait
    sorry
  sorry

theorem log_centralBinom_le_psi (n : ℕ) (hn : 1 ≤ n) :
    log (n.centralBinom : ℝ) ≤ Chebyshev.psi (2 * n) := by
  sorry


theorem psi_ge_mul_log4_sub_log (n : ℕ) (hn : 4 ≤ n) :
    n * log 4 - log n ≤ Chebyshev.psi (2 * n) := by
  have hlt := Nat.four_pow_lt_mul_centralBinom n hn
  have hpos : (0 : ℝ) < n.centralBinom := by exact_mod_cast centralBinom_pos n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hn)
  have : (4 : ℝ) ^ n < n * n.centralBinom := by exact_mod_cast hlt
  have hlog : n * log 4 < log n + log n.centralBinom := by
    have := log_lt_log (by positivity : (0 : ℝ) < 4 ^ n) this
    rw [log_pow, log_mul hn0.ne' hpos.ne'] at this
    simpa [mul_comm] using this
  have : n * log 4 - log n < log n.centralBinom := by linarith
  have hle : log n.centralBinom ≤ Chebyshev.psi (2 * n) := log_centralBinom_le_psi n (by omega)
  linarith
