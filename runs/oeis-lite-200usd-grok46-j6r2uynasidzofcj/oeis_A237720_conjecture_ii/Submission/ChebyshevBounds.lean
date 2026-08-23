import FormalConjectures.Util.ProblemImports

open Nat Real Finset
open scoped Nat.Prime
open Chebyshev
open ArithmeticFunction hiding log

/-! Stirling upper bound: `n! ≤ e √n (n/e)^n` for `n > 0`. -/

theorem factorial_le_exp_mul_sqrt_mul_pow {n : ℕ} (hn : 0 < n) :
    (n ! : ℝ) ≤ rexp 1 * √(n : ℝ) * ((n : ℝ) / rexp 1) ^ n := by
  have hseq : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq, Stirling.stirlingSeq_one] at hseq
  have hden : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / rexp 1) ^ n := by positivity
  have hle : (n ! : ℝ) ≤ (rexp 1 / √(2 : ℝ)) * (√(2 * (n : ℝ)) * ((n : ℝ) / rexp 1) ^ n) :=
    (div_le_iff₀ hden).mp hseq
  have hsqrt : √(2 * (n : ℝ)) = √(2 : ℝ) * √(n : ℝ) :=
    sqrt_mul (by positivity : (0 : ℝ) ≤ 2) _
  have : (rexp 1 / √(2 : ℝ)) * √(2 * (n : ℝ)) = rexp 1 * √(n : ℝ) := by
    rw [hsqrt]
    field
  calc
    (n ! : ℝ) ≤ (rexp 1 / √(2 : ℝ)) * (√(2 * (n : ℝ)) * ((n : ℝ) / rexp 1) ^ n) := hle
    _ = ((rexp 1 / √(2 : ℝ)) * √(2 * (n : ℝ))) * ((n : ℝ) / rexp 1) ^ n := by ring
    _ = rexp 1 * √(n : ℝ) * ((n : ℝ) / rexp 1) ^ n := by rw [this]

theorem sum_log_eq_log_factorial {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Icc 1 n, log (k : ℝ) = log (n ! : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp [log_one]
  | succ n hn ih =>
    have hnpos : (0 : ℝ) < n ! := by exact_mod_cast factorial_pos n
    have hsucc : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [sum_Icc_succ_top (by lia : 1 ≤ n + 1), ih]
    have heq : ((n + 1)! : ℝ) = (n + 1 : ℝ) * n ! := by
      rw [factorial_succ]; push_cast; ring
    rw [heq, log_mul hsucc.ne' hnpos.ne', add_comm]
    simp

/-- The number of multiples of `d` in `Icc 1 n` is `n / d`. -/
theorem card_Icc_filter_dvd (n d : ℕ) (hd : 0 < d) :
    #{k ∈ Icc 1 n | d ∣ k} = n / d := by
  have himg :
      {k ∈ Icc 1 n | d ∣ k} = (Icc 1 (n / d)).image (fun m => d * m) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · intro ⟨⟨hk1, hkn⟩, hdv⟩
      obtain ⟨m, hm⟩ := hdv
      refine ⟨m, ⟨?_, ?_⟩, hm.symm⟩
      · -- 1 ≤ m
        have : 0 < d * m := by
          rw [← hm]; exact hk1
        exact (Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp this.ne').2)
      · -- m ≤ n/d
        have : d * m ≤ n := by rw [← hm]; exact hkn
        exact (Nat.le_div_iff_mul_le hd).mpr (by rwa [mul_comm])
    · intro ⟨m, ⟨hm1, hm2⟩, hmk⟩
      rw [← hmk]
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · -- 1 ≤ d*m
        have : 1 ≤ d := hd
        nlinarith
      · -- d*m ≤ n
        have : d * m ≤ d * (n / d) := Nat.mul_le_mul_left d hm2
        exact this.trans (Nat.mul_div_le n d)
  rw [himg, Finset.card_image_of_injective]
  · rw [card_Icc, Nat.add_sub_cancel]
  · intro a b h
    exact Nat.eq_of_mul_eq_mul_left hd h

theorem sum_divisors_eq_sum_mul_div (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, f d = ∑ d ∈ Icc 1 n, f d * (n / d : ℕ) := by
  have h1 : ∀ k ∈ Icc 1 n,
      ∑ d ∈ k.divisors, f d = ∑ d ∈ Icc 1 n, if d ∣ k then f d else 0 := by
    intro k hk
    rw [mem_Icc] at hk
    rw [sum_ite, sum_const_zero, add_zero]
    apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_filter, mem_divisors, mem_Icc]
    constructor
    · intro ⟨hdk, _hk0⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdk (lt_of_lt_of_le (by decide : 0 < 1) hk.1)
      have hdle : d ≤ k := Nat.le_of_dvd (lt_of_lt_of_le (by decide : 0 < 1) hk.1) hdk
      exact ⟨⟨hdpos, hdle.trans hk.2⟩, hdk⟩
    · intro ⟨⟨_hd1, _hdn⟩, hdk⟩
      exact ⟨hdk, by lia⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [mem_Icc] at hd
  have hd0 : 0 < d := lt_of_lt_of_le (by decide : 0 < 1) hd.1
  rw [card_Icc_filter_dvd n d hd0, mul_comm]

theorem log_factorial_eq_sum_vonMangoldt_mul_div {n : ℕ} (hn : 0 < n) :
    log (n ! : ℝ) = ∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) := by
  rw [← sum_log_eq_log_factorial hn]
  have : ∑ k ∈ Icc 1 n, log (k : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, vonMangoldt d := by
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    exact (vonMangoldt_sum (n := k)).symm
  rw [this, sum_divisors_eq_sum_mul_div]


lemma le_div_iff_le_div {n d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    d ≤ n / m ↔ m ≤ n / d := by
  rw [Nat.le_div_iff_mul_le hm, Nat.le_div_iff_mul_le hd, mul_comm]

/-- `∑_{m=1}^n ψ(n/m) = log n!`. -/
theorem log_factorial_eq_sum_psi {n : ℕ} (hn : 0 < n) :
    log (n ! : ℝ) = ∑ m ∈ Icc 1 n, ψ ((n : ℝ) / m) := by
  have hpsi : ∀ m ∈ Icc 1 n, ψ ((n : ℝ) / m) = ∑ d ∈ Icc 1 (n / m), vonMangoldt d := by
    intro m hm
    have hfl : ⌊(n : ℝ) / m⌋₊ = n / m := Nat.floor_div_eq_div (K := ℝ) n m
    unfold psi
    rw [hfl]
    apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_Ioc, mem_Icc]
    exact ⟨fun ⟨h0, hle⟩ => ⟨Nat.succ_le_of_lt h0, hle⟩,
           fun ⟨h1, hle⟩ => ⟨Nat.succ_le_iff.mp h1, hle⟩⟩
  rw [sum_congr rfl hpsi]
  have hswap : ∑ m ∈ Icc 1 n, ∑ d ∈ Icc 1 (n / m), vonMangoldt d =
      ∑ d ∈ Icc 1 n, vonMangoldt d * (#{m ∈ Icc 1 n | d ≤ n / m} : ℕ) := by
    have hinner : ∀ m ∈ Icc 1 n,
        ∑ d ∈ Icc 1 (n / m), vonMangoldt d =
        ∑ d ∈ Icc 1 n, (if d ≤ n / m then vonMangoldt d else 0) := by
      intro m hm
      rw [mem_Icc] at hm
      rw [sum_ite, sum_const_zero, add_zero]
      apply sum_congr _ (fun _ _ => rfl)
      ext d
      simp only [mem_filter, mem_Icc]
      constructor
      · intro ⟨hd1, hdle⟩
        exact ⟨⟨hd1, hdle.trans (Nat.div_le_self n m)⟩, hdle⟩
      · intro ⟨⟨hd1, _⟩, hdle⟩
        exact ⟨hd1, hdle⟩
    rw [sum_congr rfl hinner, sum_comm]
    refine sum_congr rfl fun d hd => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, log_factorial_eq_sum_vonMangoldt_mul_div hn]
  refine sum_congr rfl fun d hd => ?_
  rw [mem_Icc] at hd
  have hd0 : 0 < d := lt_of_lt_of_le (by decide : (0 : ℕ) < 1) hd.1
  have heq : {m ∈ Icc 1 n | d ≤ n / m} = Icc 1 (n / d) := by
    ext m
    simp only [mem_filter, mem_Icc]
    constructor
    · intro ⟨⟨hm1, hmn⟩, hle⟩
      have hm0 : 0 < m := hm1
      exact ⟨hm1, (le_div_iff_le_div hd0 hm0).mp hle⟩
    · intro ⟨hm1, hm2⟩
      have hm0 : 0 < m := hm1
      refine ⟨⟨hm1, hm2.trans (Nat.div_le_self n d)⟩, (le_div_iff_le_div hd0 hm0).mpr hm2⟩
  rw [heq, card_Icc, Nat.add_sub_cancel]



/-- `C(n, k) * k! = n.descFactorial k`. -/

theorem choose_mul_factorial_eq_descFactorial (n k : ℕ) :
    n.choose k * k ! = n.descFactorial k :=
  by rw [mul_comm]; exact (descFactorial_eq_factorial_mul_choose n k).symm

theorem pow_le_descFactorial {n k : ℕ} (h : k ≤ n) :
    (n + 1 - k) ^ k ≤ n.descFactorial k := by
  rw [descFactorial_eq_prod_range]
  have : ∀ i ∈ range k, n + 1 - k ≤ n - i := by
    intro i hi
    rw [mem_range] at hi
    omega
  calc
    (n + 1 - k) ^ k = ∏ _i ∈ range k, (n + 1 - k) := by
      rw [prod_const, card_range]
    _ ≤ ∏ i ∈ range k, (n - i) := prod_le_prod' this

theorem choose_mul_factorial_ge_pow {n k : ℕ} (h : k ≤ n) :
    (n + 1 - k) ^ k ≤ n.choose k * k ! := by
  rw [choose_mul_factorial_eq_descFactorial]
  exact pow_le_descFactorial h

theorem choose_ge_pow_div_factorial {n k : ℕ} (h : k ≤ n) :
    ((n + 1 - k : ℕ) : ℝ) ^ k / (k ! : ℝ) ≤ (n.choose k : ℝ) := by
  have : ((n + 1 - k : ℕ) ^ k : ℝ) ≤ (n.choose k * k ! : ℝ) := by
    exact_mod_cast choose_mul_factorial_ge_pow h
  have hkpos : 0 < (k ! : ℝ) := by exact_mod_cast factorial_pos k
  exact (div_le_iff₀ hkpos).mpr this




/-- If `C(n,k)` has only prime factors `≤ k`, then `C(n,k) ≤ n^{π k}`. -/
theorem choose_le_pow_primeCounting {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hfac : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k) :
    (n.choose k : ℝ) ≤ (n : ℝ) ^ (π k) := by
  have hprod := prod_pow_factorization_choose n k hkn
  -- Restrict the product to primes ≤ k (others have valuation 0 or don't divide)
  have hsubset :
      ∏ p ∈ range (n + 1),
          p ^ (n.choose k).factorization p =
      ∏ p ∈ (range (k + 1)).filter Nat.Prime,
          p ^ (n.choose k).factorization p := by
    apply prod_subset_one_on_sdiff
    · intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      -- p ∈ filter Prime (range (k+1)) → p ∈ range (n+1)
      have : p ≤ k := Nat.lt_succ_iff.mp hp.1
      have : p < n + 1 := by omega
      simp [this]
    · intro p hp
      simp only [mem_sdiff, mem_range, mem_filter, not_and] at hp
      -- p < n+1 and (p ≥ k+1 ∨ ¬ p.Prime)
      by_cases hpP : p.Prime
      · -- then p ≥ k+1, so p > k, so by hfac, p doesn't divide C, so factorization = 0
        have : ¬ p ∣ n.choose k := fun hdvd => by
          have := hfac p hpP hdvd
          omega
        rw [factorization_eq_zero_of_not_dvd this, pow_zero]
      · rw [factorization_eq_zero_of_not_prime _ hpP, pow_zero]
    · intro p hp
      exact pow_zero_or_pos.elim (fun h => h ▸ one_pos) (fun h => by
        have : 1 ≤ p := by
          simp only [mem_filter, mem_range] at hp
          exact hp.2.one_le
        exact one_le_pow₀ this)
  -- Each p^v ≤ n
  have hterm : ∀ p ∈ (range (k + 1)).filter Nat.Prime,
      (p ^ (n.choose k).factorization p : ℝ) ≤ n := by
    intro p hp
    exact_mod_cast pow_factorization_choose_le hn
  -- Product of ≤ π(k) terms each ≤ n
  have hcard : #((range (k + 1)).filter Nat.Prime) = π k := by
    -- π k = # {p ≤ k | p.Prime} = #{p ∈ range (k+1) | p.Prime}
    simp [primeCounting, primeCounting', range_succ]
    -- need to check definition
    sorry
  rw [← hprod, hsubset]
  have : (∏ p ∈ (range (k + 1)).filter Nat.Prime,
      (p ^ (n.choose k).factorization p : ℝ)) ≤
      ∏ p ∈ (range (k + 1)).filter Nat.Prime, (n : ℝ) :=
    prod_le_prod (fun _ _ => by positivity) hterm
  refine le_trans this ?_
  rw [prod_const, ← hcard]
  simp

