import FormalConjectures.Util.ProblemImports

open Nat hiding log
open Real Finset
open scoped Nat.Prime
open Chebyshev
open ArithmeticFunction hiding log

/-
Proof development for OEIS A237720 conjecture (ii).
-/

/-! ## Stirling upper bound -/

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

theorem log_factorial_le_stirling {n : ℕ} (hn : 0 < n) :
    Real.log (n ! : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbound := factorial_le_exp_mul_sqrt_mul_pow hn
  have hlog := Real.log_le_log (by positivity) hbound
  have hpos1 : 0 < rexp 1 := exp_pos 1
  have hpos2 : 0 < √(n : ℝ) := sqrt_pos.mpr (by positivity)
  have hpos3 : 0 < ((n : ℝ) / rexp 1) ^ n := by positivity
  rw [show rexp 1 * √(n : ℝ) * ((n : ℝ) / rexp 1) ^ n =
        rexp 1 * (√(n : ℝ) * ((n : ℝ) / rexp 1) ^ n) from mul_assoc _ _ _] at hlog
  rw [Real.log_mul hpos1.ne' (mul_pos hpos2 hpos3).ne',
      Real.log_mul hpos2.ne' hpos3.ne',
      Real.log_exp, Real.log_sqrt (by positivity), Real.log_pow,
      Real.log_div hn0 hpos1.ne', Real.log_exp] at hlog
  linarith

theorem sum_log_eq_log_factorial {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Icc 1 n, Real.log (k : ℝ) = Real.log (n ! : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => simp [Real.log_one]
  | succ n hn ih =>
    have hnpos : (0 : ℝ) < n ! := by exact_mod_cast factorial_pos n
    have hsucc : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    rw [sum_Icc_succ_top (by lia : 1 ≤ n + 1), ih]
    have heq : ((n + 1)! : ℝ) = (n + 1 : ℝ) * n ! := by
      rw [factorial_succ]; push_cast; ring
    rw [heq, Real.log_mul hsucc.ne' hnpos.ne', add_comm]
    simp

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
      · have : 0 < d * m := by rw [← hm]; exact hk1
        exact (Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp this.ne').2)
      · have : d * m ≤ n := by rw [← hm]; exact hkn
        exact (Nat.le_div_iff_mul_le hd).mpr (by rwa [mul_comm])
    · intro ⟨m, ⟨hm1, hm2⟩, hmk⟩
      rw [← hmk]
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · nlinarith [hd]
      · exact (Nat.mul_le_mul_left d hm2).trans (Nat.mul_div_le n d)
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
    Real.log (n ! : ℝ) = ∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) := by
  rw [← sum_log_eq_log_factorial hn]
  have : ∑ k ∈ Icc 1 n, Real.log (k : ℝ) =
      ∑ k ∈ Icc 1 n, ∑ d ∈ k.divisors, vonMangoldt d := by
    refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    exact (vonMangoldt_sum (n := k)).symm
  rw [this, sum_divisors_eq_sum_mul_div]

lemma log_factorial_eq_sum_or_zero (n : ℕ) :
    Real.log (n ! : ℝ) = ∑ d ∈ Icc 1 n, vonMangoldt d * (n / d : ℕ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.log_one]
  · exact log_factorial_eq_sum_vonMangoldt_mul_div (Nat.pos_of_ne_zero hn)

/- ## Integer Chebyshev combination -/

/-- `m + ⌊m/30⌋ - ⌊m/2⌋ - ⌊m/3⌋ - ⌊m/5⌋`. Non-underflowing form of the usual combination. -/
def chebA (m : ℕ) : ℕ :=
  m + m / 30 - (m / 2 + m / 3 + m / 5)

lemma chebA_parts_le_mod (r : ℕ) (hr : r < 30) :
    r / 2 + r / 3 + r / 5 ≤ r + r / 30 := by
  interval_cases r <;> decide

lemma chebA_parts_le (m : ℕ) : m / 2 + m / 3 + m / 5 ≤ m + m / 30 := by
  have hm : m = 30 * (m / 30) + m % 30 := (Nat.div_add_mod m 30).symm
  have h2 : m / 2 = 15 * (m / 30) + (m % 30) / 2 := by omega
  have h3 : m / 3 = 10 * (m / 30) + (m % 30) / 3 := by omega
  have h5 : m / 5 = 6 * (m / 30) + (m % 30) / 5 := by omega
  have h30 : m / 30 = m / 30 := rfl
  have hr : m % 30 < 30 := Nat.mod_lt m (by decide)
  have hind := chebA_parts_le_mod (m % 30) hr
  calc
    m / 2 + m / 3 + m / 5
        = 15 * (m / 30) + (m % 30) / 2 + 10 * (m / 30) + (m % 30) / 3
          + 6 * (m / 30) + (m % 30) / 5 := by rw [h2, h3, h5]; ring
    _ = 31 * (m / 30) + ((m % 30) / 2 + (m % 30) / 3 + (m % 30) / 5) := by ring
    _ ≤ 31 * (m / 30) + ((m % 30) + (m % 30) / 30) := Nat.add_le_add_left hind _
    _ = 30 * (m / 30) + m % 30 + (m / 30) + (m % 30) / 30 := by ring
    _ = m + m / 30 := by
        have : (m % 30) / 30 = 0 := Nat.div_eq_of_lt hr
        rw [this, add_zero, ← hm]

lemma chebA_add_thirty (m : ℕ) : chebA (m + 30) = chebA m := by
  simp only [chebA]
  have h2 : (m + 30) / 2 = m / 2 + 15 := by omega
  have h3 : (m + 30) / 3 = m / 3 + 10 := by omega
  have h5 : (m + 30) / 5 = m / 5 + 6 := by omega
  have h30 : (m + 30) / 30 = m / 30 + 1 := by omega
  rw [h2, h3, h5, h30]
  have hle := chebA_parts_le m
  omega

lemma chebA_mul_thirty_add (q r : ℕ) : chebA (30 * q + r) = chebA r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : 30 * (q + 1) + r = (30 * q + r) + 30 := by ring
    rw [this, chebA_add_thirty, ih]

lemma chebA_eq_mod (m : ℕ) : chebA m = chebA (m % 30) := by
  have hm : chebA m = chebA (30 * (m / 30) + m % 30) := by
    congr 1
    exact (Nat.div_add_mod m 30).symm.trans (by ring)
  rw [hm, chebA_mul_thirty_add]

lemma chebA_mod_values : ∀ m < 30, chebA m = 0 ∨ chebA m = 1 := by
  decide

lemma chebA_eq_zero_or_one (m : ℕ) : chebA m = 0 ∨ chebA m = 1 := by
  rw [chebA_eq_mod]
  exact chebA_mod_values (m % 30) (Nat.mod_lt m (by decide : 0 < 30))

lemma chebA_le_one (m : ℕ) : chebA m ≤ 1 := by
  rcases chebA_eq_zero_or_one m with h | h <;> omega

lemma chebA_of_le_five {m : ℕ} (h1 : 1 ≤ m) (h5 : m ≤ 5) : chebA m = 1 := by
  interval_cases m <;> decide

lemma chebA_eq_one_of_div {n d : ℕ} (hd : 0 < d) (h1 : d ≤ n) (h6 : n < 6 * d) :
    chebA (n / d) = 1 := by
  have hlo : 1 ≤ n / d := (Nat.one_le_div_iff hd).mpr h1
  have hhi : n / d ≤ 5 := (Nat.div_le_iff_le_mul_add_pred hd).mpr (by omega)
  exact chebA_of_le_five hlo hhi

/-- Real form, definitionally matching `chebA` after a cast. -/
lemma chebA_cast (m : ℕ) :
    (m : ℝ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ) = (chebA m : ℝ) := by
  have hle := chebA_parts_le m
  simp only [chebA]
  have : ((m + m / 30 - (m / 2 + m / 3 + m / 5) : ℕ) : ℝ) =
      (m : ℝ) + (m / 30 : ℕ) - ((m / 2 : ℕ) + (m / 3 : ℕ) + (m / 5 : ℕ)) := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_add, Nat.cast_add]
  rw [this]
  ring

/- ## `chebU` and its relation to `ψ` -/

noncomputable def chebU (n : ℕ) : ℝ :=
  Real.log (n ! : ℝ) - Real.log (((n / 2) ! : ℝ)) - Real.log (((n / 3) ! : ℝ))
    - Real.log (((n / 5) ! : ℝ)) + Real.log (((n / 30) ! : ℝ))

lemma sum_extend_div (n k : ℕ) (_hk : 0 < k) :
    ∑ d ∈ Icc 1 (n / k), vonMangoldt d * ((n / k) / d : ℕ)
      = ∑ d ∈ Icc 1 n, vonMangoldt d * ((n / k) / d : ℕ) := by
  apply sum_subset_zero_on_sdiff
  · intro d hd
    simp only [mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.div_le_self n k)⟩
  · intro d hd
    simp only [mem_sdiff, mem_Icc, not_and] at hd
    have hdgt : n / k < d := by
      have : ¬ d ≤ n / k := fun h => hd.2 hd.1.1 h
      omega
    simp [Nat.div_eq_of_lt hdgt]
  · intro _ _; rfl

lemma psi_coe_nat (n : ℕ) : ψ (n : ℝ) = ∑ d ∈ Icc 1 n, vonMangoldt d := by
  rw [psi_eq_sum_Icc, Nat.floor_natCast]
  have h0 : vonMangoldt 0 = 0 := by
    rw [vonMangoldt_apply]
    simp [not_isPrimePow_zero]
  have hI : Icc 0 n = insert 0 (Icc 1 n) := by
    ext d
    simp only [mem_insert, mem_Icc]
    omega
  rw [hI, sum_insert (by simp), h0, zero_add]

lemma chebU_eq_sum (n : ℕ) :
    chebU n = ∑ d ∈ Icc 1 n, vonMangoldt d * (chebA (n / d) : ℝ) := by
  simp only [chebU]
  rw [log_factorial_eq_sum_or_zero n,
      log_factorial_eq_sum_or_zero (n / 2),
      log_factorial_eq_sum_or_zero (n / 3),
      log_factorial_eq_sum_or_zero (n / 5),
      log_factorial_eq_sum_or_zero (n / 30)]
  rw [sum_extend_div n 2 (by decide), sum_extend_div n 3 (by decide),
      sum_extend_div n 5 (by decide), sum_extend_div n 30 (by decide)]
  simp only [← sum_sub_distrib, ← sum_add_distrib, ← mul_sub, ← mul_add]
  refine sum_congr rfl fun d _hd => ?_
  congr 1
  have h2 : (n / 2) / d = (n / d) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d]
  have h3 : (n / 3) / d = (n / d) / 3 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d]
  have h5 : (n / 5) / d = (n / d) / 5 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d]
  have h30 : (n / 30) / d = (n / d) / 30 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d]
  rw [h2, h3, h5, h30, ← chebA_cast]

lemma chebU_le_psi (n : ℕ) : chebU n ≤ ψ (n : ℝ) := by
  rw [chebU_eq_sum, psi_coe_nat]
  refine sum_le_sum fun d _hd => ?_
  have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
  have hA : (chebA (n / d) : ℝ) ≤ 1 := by exact_mod_cast chebA_le_one (n / d)
  nlinarith

lemma sum_Icc_split_div_six (n : ℕ) :
    ∑ d ∈ Icc 1 n, vonMangoldt d =
      ∑ d ∈ Icc 1 (n / 6), vonMangoldt d + ∑ d ∈ Icc (n / 6 + 1) n, vonMangoldt d := by
  by_cases h : n / 6 + 1 ≤ n
  · rw [← sum_union]
    · congr 1
      ext d
      simp only [mem_union, mem_Icc]
      omega
    · rw [disjoint_left]
      intro d hd1 hd2
      simp only [mem_Icc] at hd1 hd2
      omega
  · have hn : n ≤ n / 6 := by omega
    have hn6 : n / 6 = n := le_antisymm (Nat.div_le_self n 6) hn
    have hempty : Icc (n / 6 + 1) n = ∅ := by
      apply eq_empty_of_forall_notMem
      intro d hd
      simp only [mem_Icc] at hd
      omega
    simp [hn6]

lemma psi_sub_psi_div_six_le_chebU (n : ℕ) :
    ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤ chebU n := by
  rw [chebU_eq_sum, psi_coe_nat, psi_coe_nat, sum_Icc_split_div_six, add_sub_cancel_left]
  have hsubset : Icc (n / 6 + 1) n ⊆ Icc 1 n := by
    intro d hd
    simp only [mem_Icc] at hd ⊢
    omega
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsubset ?_)
  · refine le_of_eq ?_
    refine (sum_congr rfl fun d hd => ?_).symm
    simp only [mem_Icc] at hd
    have hd0 : 0 < d := by omega
    have h6 : n < 6 * d := by
      have : n / 6 < d := by omega
      rw [mul_comm]
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 6)).mp this
    have ha : chebA (n / d) = 1 := chebA_eq_one_of_div hd0 hd.2 h6
    rw [ha, Nat.cast_one, mul_one]
  · intro d _hd _
    have hΛ : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    have hA : 0 ≤ (chebA (n / d) : ℝ) := by exact_mod_cast Nat.zero_le _
    nlinarith

/- ## Explicit bounds on the Chebyshev constant -/

/-- `c = ½log 2 + ⅓log 3 + ⅕log 5 − (1/30)log 30`. -/
noncomputable def chebC : ℝ :=
  (1 / 2 : ℝ) * Real.log 2 + (1 / 3 : ℝ) * Real.log 3 + (1 / 5 : ℝ) * Real.log 5
    - (1 / 30 : ℝ) * Real.log 30

lemma chebC_rewrite :
    chebC = (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3
      + (1 / 6 : ℝ) * Real.log 5 := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    have : (30 : ℝ) = 2 * 3 * 5 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  unfold chebC
  rw [h30]
  ring

lemma exp_two_div_five_lt_three_div_two : Real.exp (2 / 5) < (3 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ 2 / 5 := by norm_num
  have hx1 : (2 / 5 : ℝ) ≤ 1 := by norm_num
  have h := Real.exp_bound' hx0 hx1 (n := 8) (by decide)
  have hsum :
      (∑ m ∈ Finset.range 8, ((2 / 5 : ℝ) ^ m) / (m.factorial : ℝ))
        + (2 / 5 : ℝ) ^ 8 * (8 + 1) / ((Nat.factorial 8 : ℝ) * 8) < (3 / 2 : ℝ) := by
    norm_num [Nat.factorial]
  linarith

lemma one_div_five_lt_log_five_div_four : (1 / 5 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have hpos : (0 : ℝ) < 5 / 4 := by norm_num
  apply (Real.exp_lt_exp).1
  rw [Real.exp_log hpos]
  have hx0 : (0 : ℝ) ≤ 1 / 5 := by norm_num
  have hx1 : (1 / 5 : ℝ) ≤ 1 := by norm_num
  have h := Real.exp_bound' hx0 hx1 (n := 6) (by decide)
  have hsum :
      (∑ m ∈ Finset.range 6, ((1 / 5 : ℝ) ^ m) / (m.factorial : ℝ))
        + (1 / 5 : ℝ) ^ 6 * (6 + 1) / ((Nat.factorial 6 : ℝ) * 6) < (5 / 4 : ℝ) := by
    norm_num [Nat.factorial]
  linarith

lemma two_div_five_lt_log_three_div_two : (2 / 5 : ℝ) < Real.log (3 / 2 : ℝ) := by
  have hpos : (0 : ℝ) < 3 / 2 := by norm_num
  apply (Real.exp_lt_exp).1
  rw [Real.exp_log hpos]
  exact exp_two_div_five_lt_three_div_two

lemma log_three_eq : Real.log (3 : ℝ) = Real.log 2 + Real.log (3 / 2 : ℝ) := by
  calc
    Real.log (3 : ℝ) = Real.log (2 * (3 / 2 : ℝ)) := by norm_num
    _ = Real.log 2 + Real.log (3 / 2 : ℝ) :=
      Real.log_mul (by norm_num) (by norm_num)

lemma log_five_eq : Real.log (5 : ℝ) = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
  calc
    Real.log (5 : ℝ) = Real.log ((2 : ℝ) ^ 2 * (5 / 4 : ℝ)) := by norm_num
    _ = Real.log ((2 : ℝ) ^ 2) + Real.log (5 / 4 : ℝ) :=
      Real.log_mul (by positivity) (by norm_num)
    _ = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
      rw [Real.log_pow]; norm_cast

lemma log_three_gt : (1093 / 1000 : ℝ) < Real.log (3 : ℝ) := by
  rw [log_three_eq]
  have h2 := log_two_gt_d9
  have h32 := two_div_five_lt_log_three_div_two
  linarith

lemma log_five_gt : (1586 / 1000 : ℝ) < Real.log (5 : ℝ) := by
  rw [log_five_eq]
  have h2 := log_two_gt_d9
  have h54 := one_div_five_lt_log_five_div_four
  linarith

lemma chebC_gt_nine_tenths : (9 / 10 : ℝ) < chebC := by
  rw [chebC_rewrite]
  have h2 := log_two_gt_d9
  have h3 := log_three_gt
  have h5 := log_five_gt
  nlinarith

lemma log_three_div_two_lt : Real.log (3 / 2 : ℝ) < (41 / 100 : ℝ) := by
  have hpos : (0 : ℝ) ≤ 41 / 100 := by norm_num
  have hsum : (3 / 2 : ℝ) < ∑ m ∈ Finset.range 6,
      ((41 / 100 : ℝ) ^ m) / (m.factorial : ℝ) := by
    norm_num [Nat.factorial]
  have hle := Real.sum_le_exp_of_nonneg hpos 6
  have : (3 / 2 : ℝ) < Real.exp (41 / 100) := lt_of_lt_of_le hsum hle
  have hpos' : (0 : ℝ) < 3 / 2 := by norm_num
  exact (Real.log_lt_iff_lt_exp hpos').mpr this

lemma log_five_div_four_lt : Real.log (5 / 4 : ℝ) < (23 / 100 : ℝ) := by
  have hpos : (0 : ℝ) ≤ 23 / 100 := by norm_num
  have hsum : (5 / 4 : ℝ) < ∑ m ∈ Finset.range 5,
      ((23 / 100 : ℝ) ^ m) / (m.factorial : ℝ) := by
    norm_num [Nat.factorial]
  have hle := Real.sum_le_exp_of_nonneg hpos 5
  have : (5 / 4 : ℝ) < Real.exp (23 / 100) := lt_of_lt_of_le hsum hle
  have hpos' : (0 : ℝ) < 5 / 4 := by norm_num
  exact (Real.log_lt_iff_lt_exp hpos').mpr this

lemma log_three_lt : Real.log (3 : ℝ) < (1104 / 1000 : ℝ) := by
  rw [log_three_eq]
  have h2 := log_two_lt_d9
  have h32 := log_three_div_two_lt
  linarith

lemma log_five_lt : Real.log (5 : ℝ) < (1617 / 1000 : ℝ) := by
  rw [log_five_eq]
  have h2 := log_two_lt_d9
  have h54 := log_five_div_four_lt
  linarith

lemma chebC_lt : chebC < (925 / 1000 : ℝ) := by
  rw [chebC_rewrite]
  have h2 := log_two_lt_d9
  have h3 := log_three_lt
  have h5 := log_five_lt
  nlinarith

lemma log_factorial_ge_basic {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  have h := Stirling.le_log_factorial_stirling hm.ne'
  have hlog : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne'))
  have hpi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.two_le_pi]
  linarith

lemma log_abs_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hlogle : Real.log (1 - x) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  have hrec : Real.log (1 / (1 - x)) = -Real.log (1 - x) := by
    rw [Real.log_div (by norm_num) (ne_of_gt hpos), Real.log_one, zero_sub]
  have hle : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hid : 1 / (1 - x) - 1 = x / (1 - x) := by field
  have hneg : -Real.log (1 - x) ≤ x / (1 - x) := by linarith
  have hstd : -(x / (1 - x)) ≤ Real.log (1 - x) := neg_le.mp hneg
  have hxfrac : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [abs_of_nonpos hlogle]
  linarith

/-- The continuous main term equals `chebC * n`. -/
lemma chebC_mul_eq {n : ℝ} (hn : 0 < n) :
    chebC * n =
      n * Real.log n
        - (n / 2) * Real.log (n / 2)
        - (n / 3) * Real.log (n / 3)
        - (n / 5) * Real.log (n / 5)
        + (n / 30) * Real.log (n / 30) := by
  unfold chebC
  have hn0 : n ≠ 0 := hn.ne'
  rw [Real.log_div hn0 (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div hn0 (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div hn0 (by norm_num : (5 : ℝ) ≠ 0),
      Real.log_div hn0 (by norm_num : (30 : ℝ) ≠ 0)]
  ring

lemma log_factorial_le_loose {m : ℕ} (hm : 0 < m) :
    Real.log (m ! : ℝ) ≤ (m : ℝ) * Real.log m - m + Real.log m + 1 := by
  have h := log_factorial_le_stirling hm
  have hlog : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne'))
  linarith

lemma nat_div_lt_add_one (n k : ℕ) (_hk : 0 < k) :
    (n : ℝ) / (k : ℝ) < ((n / k : ℕ) : ℝ) + 1 := by
  have hfl : ⌊(n : ℝ) / (k : ℝ)⌋₊ = n / k := Nat.floor_div_eq_div (K := ℝ) n k
  have := Nat.lt_floor_add_one ((n : ℝ) / (k : ℝ))
  rwa [hfl] at this

lemma floor_mul_log_sub {n k : ℕ} (hk : 0 < k) (hn : 60 ≤ n)
    (hnk : 0 < n / k) :
    |((n / k : ℕ) : ℝ) * Real.log ((n / k : ℕ) : ℝ)
        - ((n : ℝ) / (k : ℝ)) * Real.log ((n : ℝ) / (k : ℝ))|
      ≤ Real.log n + 2 := by
  set m : ℕ := n / k
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hnk
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 60) hn)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hle : (m : ℝ) ≤ (n : ℝ) / (k : ℝ) := Nat.cast_div_le
  have hlt : (n : ℝ) / (k : ℝ) < (m : ℝ) + 1 := nat_div_lt_add_one n k hk
  have hr0 : 0 ≤ (n : ℝ) / (k : ℝ) - m := sub_nonneg.mpr hle
  have hr1 : (n : ℝ) / (k : ℝ) - (m : ℝ) < 1 := sub_lt_iff_lt_add'.mpr hlt
  set r : ℝ := (n : ℝ) / (k : ℝ) - m
  have hr_def : (n : ℝ) / (k : ℝ) = (m : ℝ) + r := by simp [r]
  have hsplit :
      (m : ℝ) * Real.log m - ((n : ℝ) / (k : ℝ)) * Real.log ((n : ℝ) / (k : ℝ))
        = (m : ℝ) * (Real.log m - Real.log ((n : ℝ) / (k : ℝ)))
          - r * Real.log ((n : ℝ) / (k : ℝ)) := by
    rw [hr_def]; ring
  rw [hsplit]
  refine le_trans (abs_sub _ _) ?_
  have hnk_pos : 0 < (n : ℝ) / (k : ℝ) := div_pos hnpos hkpos
  have hk_le_n : k ≤ n := by
    have : 1 * k ≤ n := (Nat.le_div_iff_mul_le hk).mp hnk
    rwa [one_mul] at this
  have hlog_nk : 0 ≤ Real.log ((n : ℝ) / (k : ℝ)) :=
    Real.log_nonneg ((one_le_div hkpos).mpr (by exact_mod_cast hk_le_n))
  -- |m (log m - log(m+r))| = m (log(m+r) - log m) = m log(1 + r/m) ≤ m * (r/m) = r < 1
  have hdiff_nonneg :
      Real.log m ≤ Real.log ((n : ℝ) / (k : ℝ)) :=
    Real.log_le_log hmpos hle
  have hterm1 :
      |(m : ℝ) * (Real.log m - Real.log ((n : ℝ) / (k : ℝ)))| ≤ r := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m),
        abs_of_nonpos (sub_nonpos.mpr hdiff_nonneg)]
    have hneg : -(Real.log m - Real.log ((n : ℝ) / (k : ℝ)))
        = Real.log ((n : ℝ) / (k : ℝ)) - Real.log m := by ring
    rw [hneg]
    have : Real.log ((n : ℝ) / (k : ℝ)) - Real.log m
        = Real.log (1 + r / m) := by
      have hr_div : ((n : ℝ) / (k : ℝ)) / m = 1 + r / m := by
        rw [hr_def]; field [hmpos.ne']
      rw [← Real.log_div hnk_pos.ne' hmpos.ne', hr_div]
    rw [this]
    have hx : 0 ≤ r / m := div_nonneg hr0 hmpos.le
    have hlogle : Real.log (1 + r / m) ≤ r / m := by
      have : Real.log (1 + r / m) ≤ (1 + r / m) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      linarith
    have : (m : ℝ) * (r / m) = r := by field [hmpos.ne']
    nlinarith
  have hterm2 : |r * Real.log ((n : ℝ) / (k : ℝ))| ≤ Real.log n + 1 := by
    rw [abs_mul, abs_of_nonneg hr0, abs_of_nonneg hlog_nk]
    have hlogle : Real.log ((n : ℝ) / (k : ℝ)) ≤ Real.log n :=
      Real.log_le_log hnk_pos (div_le_self hnpos.le (by
        have : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk.ne')
        exact this))
    nlinarith [hr1, Real.log_nonneg (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 60) hn)
      exact this)]
  nlinarith [hr1]

lemma nat_div_pos_of_le {n k : ℕ} (hk : 0 < k) (h : k ≤ n) : 0 < n / k :=
  Nat.div_pos h hk

private noncomputable def chebMain (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log n)
    - ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)
    - ((n / 3 : ℕ) : ℝ) * Real.log ((n / 3 : ℕ) : ℝ)
    - ((n / 5 : ℕ) : ℝ) * Real.log ((n / 5 : ℕ) : ℝ)
    + ((n / 30 : ℕ) : ℝ) * Real.log ((n / 30 : ℕ) : ℝ)

private noncomputable def chebLin (n : ℕ) : ℝ :=
  - (n : ℝ) + (n / 2 : ℕ) + (n / 3 : ℕ) + (n / 5 : ℕ) - (n / 30 : ℕ)

lemma abs_div_err (n k : ℕ) (hk : 0 < k) :
    |((n / k : ℕ) : ℝ) - (n : ℝ) / (k : ℝ)| < 1 := by
  have hle : ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / (k : ℝ) := Nat.cast_div_le
  have hlt := nat_div_lt_add_one n k hk
  rw [abs_sub_lt_iff]
  constructor <;> linarith

lemma chebMain_sub_chebC {n : ℕ} (hn : 60 ≤ n) :
    |chebMain n - chebC * n| ≤ 5 * Real.log n + 10 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 60) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have h2 : 0 < n / 2 := nat_div_pos_of_le (by decide) (le_trans (by decide : 2 ≤ 60) hn)
  have h3 : 0 < n / 3 := nat_div_pos_of_le (by decide) (le_trans (by decide : 3 ≤ 60) hn)
  have h5 : 0 < n / 5 := nat_div_pos_of_le (by decide) (le_trans (by decide : 5 ≤ 60) hn)
  have h30 : 0 < n / 30 := nat_div_pos_of_le (by decide) (le_trans (by decide : 30 ≤ 60) hn)
  have E1 := floor_mul_log_sub (n := n) (k := 1) (by decide) hn (by simp [hn0])
  have E2 := floor_mul_log_sub (n := n) (k := 2) (by decide) hn h2
  have E3 := floor_mul_log_sub (n := n) (k := 3) (by decide) hn h3
  have E5 := floor_mul_log_sub (n := n) (k := 5) (by decide) hn h5
  have E30 := floor_mul_log_sub (n := n) (k := 30) (by decide) hn h30
  have hC := chebC_mul_eq hnR
  -- chebMain n - c*n is the sum of 5 floor-log errors (k=1 is 0 essentially)
  have : chebMain n - chebC * n =
      (((n : ℝ) * Real.log n - ((n : ℝ) / 1) * Real.log ((n : ℝ) / 1))
        - (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)
            - ((n : ℝ) / 2) * Real.log ((n : ℝ) / 2))
        - (((n / 3 : ℕ) : ℝ) * Real.log ((n / 3 : ℕ) : ℝ)
            - ((n : ℝ) / 3) * Real.log ((n : ℝ) / 3))
        - (((n / 5 : ℕ) : ℝ) * Real.log ((n / 5 : ℕ) : ℝ)
            - ((n : ℝ) / 5) * Real.log ((n : ℝ) / 5))
        + (((n / 30 : ℕ) : ℝ) * Real.log ((n / 30 : ℕ) : ℝ)
            - ((n : ℝ) / 30) * Real.log ((n : ℝ) / 30))) := by
    unfold chebMain
    rw [hC]
    ring_nf
  rw [this]
  set e1 := (n : ℝ) * Real.log n - ((n : ℝ) / 1) * Real.log ((n : ℝ) / 1)
  set e2 := ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)
      - ((n : ℝ) / 2) * Real.log ((n : ℝ) / 2)
  set e3 := ((n / 3 : ℕ) : ℝ) * Real.log ((n / 3 : ℕ) : ℝ)
      - ((n : ℝ) / 3) * Real.log ((n : ℝ) / 3)
  set e5 := ((n / 5 : ℕ) : ℝ) * Real.log ((n / 5 : ℕ) : ℝ)
      - ((n : ℝ) / 5) * Real.log ((n : ℝ) / 5)
  set e30 := ((n / 30 : ℕ) : ℝ) * Real.log ((n / 30 : ℕ) : ℝ)
      - ((n : ℝ) / 30) * Real.log ((n : ℝ) / 30)
  have hnest : |e1 - e2 - e3 - e5 + e30| ≤ |e1| + |e2| + |e3| + |e5| + |e30| := by
    calc
      |e1 - e2 - e3 - e5 + e30| = |(e1 - e2 - e3 - e5) + e30| := by ring_nf
      _ ≤ |e1 - e2 - e3 - e5| + |e30| := abs_add_le _ _
      _ ≤ |e1 - e2 - e3| + |e5| + |e30| := by
          have := abs_sub (e1 - e2 - e3) e5
          linarith
      _ ≤ |e1 - e2| + |e3| + |e5| + |e30| := by
          have := abs_sub (e1 - e2) e3
          linarith
      _ ≤ |e1| + |e2| + |e3| + |e5| + |e30| := by
          have := abs_sub e1 e2
          linarith
  refine le_trans hnest ?_
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 60) hn))
  have he1 : |e1| ≤ Real.log n + 2 := by
    simpa [e1, div_one] using E1
  nlinarith [he1, (by simpa [e2] using E2 : |e2| ≤ Real.log n + 2),
    (by simpa [e3] using E3 : |e3| ≤ Real.log n + 2),
    (by simpa [e5] using E5 : |e5| ≤ Real.log n + 2),
    (by simpa [e30] using E30 : |e30| ≤ Real.log n + 2)]

lemma chebLin_abs (n : ℕ) : |chebLin n| ≤ 5 := by
  have e2 := abs_div_err n 2 (by decide)
  have e3 := abs_div_err n 3 (by decide)
  have e5 := abs_div_err n 5 (by decide)
  have e30 := abs_div_err n 30 (by decide)
  have : chebLin n =
      (((n / 2 : ℕ) : ℝ) - (n : ℝ) / 2)
        + (((n / 3 : ℕ) : ℝ) - (n : ℝ) / 3)
        + (((n / 5 : ℕ) : ℝ) - (n : ℝ) / 5)
        - (((n / 30 : ℕ) : ℝ) - (n : ℝ) / 30) := by
    unfold chebLin
    ring
  rw [this]
  set a := ((n / 2 : ℕ) : ℝ) - (n : ℝ) / 2
  set b := ((n / 3 : ℕ) : ℝ) - (n : ℝ) / 3
  set c := ((n / 5 : ℕ) : ℝ) - (n : ℝ) / 5
  set d := ((n / 30 : ℕ) : ℝ) - (n : ℝ) / 30
  have hnest : |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
    calc
      |a + b + c - d| = |(a + b + c) + -d| := by ring_nf
      _ ≤ |a + b + c| + |-d| := abs_add_le _ _
      _ ≤ |a + b| + |c| + |d| := by
          have := abs_add_le (a + b) c
          simp only [abs_neg]
          linarith
      _ ≤ |a| + |b| + |c| + |d| := by
          have := abs_add_le a b
          linarith
  refine le_trans hnest ?_
  nlinarith [e2, e3, e5, e30]

lemma chebU_sub_chebC_abs {n : ℕ} (hn : 60 ≤ n) :
    |chebU n - chebC * n| ≤ 8 * Real.log n + 25 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 60) hn
  have h2 : 0 < n / 2 := nat_div_pos_of_le (by decide) (le_trans (by decide : 2 ≤ 60) hn)
  have h3 : 0 < n / 3 := nat_div_pos_of_le (by decide) (le_trans (by decide : 3 ≤ 60) hn)
  have h5 : 0 < n / 5 := nat_div_pos_of_le (by decide) (le_trans (by decide : 5 ≤ 60) hn)
  have h30 : 0 < n / 30 := nat_div_pos_of_le (by decide) (le_trans (by decide : 30 ≤ 60) hn)
  have L1u := log_factorial_le_loose hn0
  have L1l := log_factorial_ge_basic hn0
  have L2u := log_factorial_le_loose h2
  have L2l := log_factorial_ge_basic h2
  have L3u := log_factorial_le_loose h3
  have L3l := log_factorial_ge_basic h3
  have L5u := log_factorial_le_loose h5
  have L5l := log_factorial_ge_basic h5
  have L30u := log_factorial_le_loose h30
  have L30l := log_factorial_ge_basic h30
  have hlog2 : Real.log ((n / 2 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast h2) (by
      have : n / 2 ≤ n := Nat.div_le_self _ _; exact_mod_cast this)
  have hlog3 : Real.log ((n / 3 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast h3) (by
      have : n / 3 ≤ n := Nat.div_le_self _ _; exact_mod_cast this)
  have hlog5 : Real.log ((n / 5 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast h5) (by
      have : n / 5 ≤ n := Nat.div_le_self _ _; exact_mod_cast this)
  have hlog30 : Real.log ((n / 30 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast h30) (by
      have : n / 30 ≤ n := Nat.div_le_self _ _; exact_mod_cast this)
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 60) hn))
  have hlower_approx :
      chebMain n + chebLin n - Real.log ((n / 2 : ℕ) : ℝ) - Real.log ((n / 3 : ℕ) : ℝ)
        - Real.log ((n / 5 : ℕ) : ℝ) - 3 ≤ chebU n := by
    unfold chebU chebMain chebLin
    linarith [L1l, L2u, L3u, L5u, L30l]
  have hupper_approx :
      chebU n ≤ chebMain n + chebLin n + Real.log n + Real.log ((n / 30 : ℕ) : ℝ) + 2 := by
    unfold chebU chebMain chebLin
    linarith [L1u, L2l, L3l, L5l, L30u]
  have hM := chebMain_sub_chebC hn
  have hL := chebLin_abs n
  have hlo : chebC * n - (8 * Real.log n + 25) ≤ chebU n := by
    have : chebC * n - (5 * Real.log n + 10) - 5 - 3 * Real.log n - 3 ≤
        chebMain n + chebLin n - Real.log ((n / 2 : ℕ) : ℝ)
          - Real.log ((n / 3 : ℕ) : ℝ) - Real.log ((n / 5 : ℕ) : ℝ) - 3 := by
      have h1 : chebC * n - (5 * Real.log n + 10) ≤ chebMain n := by
        have := abs_le.mp hM |>.1
        linarith
      have h2 : -5 ≤ chebLin n := by
        have := abs_le.mp hL |>.1
        linarith
      linarith [hlog2, hlog3, hlog5]
    linarith [hlower_approx]
  have hup : chebU n ≤ chebC * n + (8 * Real.log n + 25) := by
    have : chebMain n + chebLin n + Real.log n + Real.log ((n / 30 : ℕ) : ℝ) + 2 ≤
        chebC * n + (5 * Real.log n + 10) + 5 + Real.log n + Real.log n + 2 := by
      have h1 : chebMain n ≤ chebC * n + (5 * Real.log n + 10) := by
        have := abs_le.mp hM |>.2
        linarith
      have h2 : chebLin n ≤ 5 := by
        have := abs_le.mp hL |>.2
        linarith
      linarith [hlog30]
    linarith [hupper_approx]
  exact abs_le.mpr ⟨by linarith [hlo], by linarith [hup]⟩

lemma chebU_le_chebC {n : ℕ} (hn : 60 ≤ n) :
    chebU n ≤ chebC * n + 8 * Real.log n + 25 := by
  have := chebU_sub_chebC_abs hn
  linarith [(abs_le.mp this).2]

lemma chebC_le_chebU {n : ℕ} (hn : 60 ≤ n) :
    chebC * n - 8 * Real.log n - 25 ≤ chebU n := by
  have := chebU_sub_chebC_abs hn
  have h := (abs_le.mp this).1
  linarith

lemma psi_le_chebU_add_psi_div_six (n : ℕ) :
    ψ (n : ℝ) ≤ chebU n + ψ ((n / 6 : ℕ) : ℝ) := by
  have := psi_sub_psi_div_six_le_chebU n
  linarith

lemma log4_add_four_nonneg : 0 ≤ Real.log 4 + 4 := by
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  linarith

lemma chebC_nonneg : 0 ≤ chebC :=
  le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 9 / 10) chebC_gt_nine_tenths)

lemma psi_of_lt_sixty {m : ℕ} (hm : m < 60) :
    ψ (m : ℝ) ≤ (Real.log 4 + 4) * 60 := by
  have h := psi_le_const_mul_self (x := (m : ℝ)) (by positivity)
  have : (m : ℝ) < 60 := by exact_mod_cast hm
  nlinarith [log4_add_four_nonneg]

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_cast

lemma log_four_lt : Real.log 4 < (1387 / 1000 : ℝ) := by
  rw [log_four_eq]
  linarith [log_two_lt_d9]

lemma log_four_gt : (1386 / 1000 : ℝ) < Real.log 4 := by
  rw [log_four_eq]
  linarith [log_two_gt_d9]

lemma log_six_eq : Real.log 6 = Real.log 2 + Real.log 3 := by
  have : (6 : ℝ) = 2 * 3 := by norm_num
  rw [this, Real.log_mul (by norm_num) (by norm_num)]

lemma log_six_gt : (1786 / 1000 : ℝ) < Real.log 6 := by
  rw [log_six_eq]
  linarith [log_two_gt_d9, log_three_gt]

lemma log_six_lt : Real.log 6 < (1798 / 1000 : ℝ) := by
  rw [log_six_eq]
  linarith [log_two_lt_d9, log_three_lt]

lemma log_sixty_gt : (4 : ℝ) < Real.log 60 := by
  have h60 : Real.log 60 = Real.log 4 + Real.log 3 + Real.log 5 := by
    have : (60 : ℝ) = 4 * 3 * 5 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  rw [h60]
  linarith [log_four_gt, log_three_gt, log_five_gt]

lemma log_nat_div_le_log_sub_log_six {n : ℕ} (hn : 360 ≤ n) :
    Real.log ((n / 6 : ℕ) : ℝ) ≤ Real.log n - Real.log 6 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 360) hn)
  have h6 : (0 : ℝ) < 6 := by norm_num
  have hdiv : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := Nat.cast_div_le
  have hpos : (0 : ℝ) < ((n / 6 : ℕ) : ℝ) := by
    have : 60 ≤ n / 6 := (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mpr (by omega)
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 60) this)
  have hle := Real.log_le_log hpos hdiv
  have : Real.log ((n : ℝ) / 6) = Real.log n - Real.log 6 :=
    Real.log_div hn0.ne' (by norm_num)
  linarith

lemma psi_le_chebC_add_err {n : ℕ} (hn : 60 ≤ n) :
    ψ (n : ℝ) ≤ chebC * n + 8 * Real.log n + 25 + ψ ((n / 6 : ℕ) : ℝ) := by
  have hU := chebU_le_chebC hn
  have hs := psi_le_chebU_add_psi_div_six n
  linarith

lemma psi_upper_bound : ∀ {n : ℕ}, 60 ≤ n →
    ψ (n : ℝ) ≤ (6 / 5 : ℝ) * chebC * n + 6 * (Real.log n) ^ 2 + 400 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hlogn : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 60) hn))
    have hsplit := psi_le_chebC_add_err hn
    by_cases hsmall : n / 6 < 60
    · have hrem := psi_of_lt_sixty hsmall
      have hlog4 : Real.log 4 < (14 / 10 : ℝ) := by
        linarith [log_four_lt]
      have hconst : (Real.log 4 + 4) * 60 < (324 : ℝ) := by
        nlinarith [hlog4]
      have hgoal :
          chebC * n + 8 * Real.log n + 25 + (Real.log 4 + 4) * 60
            ≤ (6 / 5 : ℝ) * chebC * n + 6 * (Real.log n) ^ 2 + 400 := by
        have hc : 0 ≤ chebC := chebC_nonneg
        have hnR : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
        have ht : (4 : ℝ) ≤ Real.log n := le_trans (le_of_lt log_sixty_gt)
            (Real.log_le_log (by positivity) (by exact_mod_cast hn))
        nlinarith [sq_nonneg (Real.log n - 1)]
      linarith
    · have hn6 : 60 ≤ n / 6 := Nat.not_lt.mp hsmall
      have hn360 : 360 ≤ n :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 6)).mp hn6
      have hn6lt : n / 6 < n :=
        Nat.div_lt_self (lt_of_lt_of_le (by decide : 0 < 360) hn360) (by decide)
      have ih6 := ih (n / 6) hn6lt hn6
      have hlog6 := log_nat_div_le_log_sub_log_six hn360
      have hpos6 : 0 ≤ Real.log ((n / 6 : ℕ) : ℝ) :=
        Real.log_nonneg (by
          have : (1 : ℕ) ≤ n / 6 := le_trans (by decide : (1 : ℕ) ≤ 60) hn6
          exact_mod_cast this)
      have hsq :
          (Real.log ((n / 6 : ℕ) : ℝ)) ^ 2
            ≤ (Real.log n - Real.log 6) ^ 2 := by
        have : Real.log ((n / 6 : ℕ) : ℝ) ≤ Real.log n - Real.log 6 := hlog6
        have h2 : 0 ≤ Real.log n - Real.log 6 := le_trans hpos6 this
        nlinarith
      have hlog6gt := log_six_gt
      have hlog6lt := log_six_lt
      have ht : (4 : ℝ) ≤ Real.log n := le_trans (le_of_lt log_sixty_gt)
          (Real.log_le_log (by positivity) (by exact_mod_cast hn))
      have herr :
          8 * Real.log n + 25 + 6 * (Real.log ((n / 6 : ℕ) : ℝ)) ^ 2
            ≤ 6 * (Real.log n) ^ 2 := by
        have hexpand :
            6 * (Real.log n - Real.log 6) ^ 2
              = 6 * (Real.log n) ^ 2 - 12 * Real.log 6 * Real.log n
                + 6 * (Real.log 6) ^ 2 := by ring
        have hreduce :
            8 * Real.log n + 25 + 6 * (Real.log n - Real.log 6) ^ 2
              ≤ 6 * (Real.log n) ^ 2 := by
          -- 12 log6 log n - 8 log n ≥ 25 + 6 (log 6)^2
          nlinarith [hlog6gt, hlog6lt, ht, sq_nonneg (Real.log 6)]
        nlinarith
      have hC : 0 ≤ chebC := chebC_nonneg
      have hn6R : (0 : ℝ) ≤ (n / 6 : ℕ) := by exact_mod_cast (Nat.zero_le _)
      have hmain :
          chebC * n + (6 / 5 : ℝ) * chebC * (n / 6 : ℕ)
            ≤ (6 / 5 : ℝ) * chebC * n := by
        have hdiv : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := Nat.cast_div_le
        nlinarith
      linarith

lemma rpow_one_third_le_sqrt_div_two {x : ℝ} (hx : (64 : ℝ) ≤ x) :
    x ^ ((1 : ℝ) / 3) ≤ √x / 2 := by
  have hx0 : 0 < x := by linarith
  have hb : 0 ≤ √x / 2 := by positivity
  refine le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) hb ?_
  have ha3 : (x ^ ((1 : ℝ) / 3)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hb3 : (√x / 2) ^ 3 = √x ^ 3 / 8 := by
    rw [div_pow]; norm_num
  have hsqrt3 : √x ^ 3 = √x * x := by
    calc
      √x ^ 3 = √x ^ 2 * √x := by ring
      _ = x * √x := by rw [Real.sq_sqrt hx0.le]
      _ = √x * x := by ring
  rw [ha3, hb3, hsqrt3, le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have h8 : (8 : ℝ) ≤ √x := by
    have : (8 : ℝ) ^ 2 ≤ x := by linarith
    exact (Real.le_sqrt (by norm_num) hx0.le).mpr this
  nlinarith [hx0.le]

lemma log_div_log_two_nonneg {x : ℝ} (hx : (1 : ℝ) ≤ x) :
    0 ≤ Real.log x / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_nonneg (Real.log_nonneg hx) hlog2.le

lemma floor_log_div_log_two_ge_two {x : ℝ} (hx : (4 : ℝ) ≤ x) :
    2 ≤ ⌊Real.log x / Real.log 2⌋₊ := by
  rw [Nat.le_floor_iff (log_div_log_two_nonneg (by linarith))]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (2 : ℝ) ≤ Real.log x / Real.log 2 := by
    rw [le_div_iff₀ hlog2, ← log_four_eq]
    exact Real.log_le_log (by norm_num) hx
  exact this

lemma abs_psi_sub_theta_of_ge_sixtyfour {x : ℝ} (hx : (64 : ℝ) ≤ x) :
    |ψ x - θ x| ≤ √x * (Real.log x + Real.log 4) := by
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hx4 : (4 : ℝ) ≤ x := by linarith
  rw [psi_eq_theta_add_sum_theta hx2, add_sub_cancel_left]
  have hnn : 0 ≤ ∑ n ∈ Icc 2 ⌊Real.log x / Real.log 2⌋₊,
      θ (x ^ ((1 : ℝ) / n)) :=
    sum_nonneg fun _ _ => theta_nonneg _
  rw [abs_of_nonneg hnn]
  set m := ⌊Real.log x / Real.log 2⌋₊
  have hm2 : 2 ≤ m := floor_log_div_log_two_ge_two hx4
  have hm3 : 3 ≤ m := by
    rw [Nat.le_floor_iff (log_div_log_two_nonneg (by linarith))]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : (3 : ℝ) ≤ Real.log x / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      -- 3 log 2 ≤ log x, log 8 ≤ log x, 8 ≤ x
      have h8 : Real.log 8 ≤ Real.log x :=
        Real.log_le_log (by norm_num) (by linarith : (8 : ℝ) ≤ x)
      have : (3 : ℝ) * Real.log 2 = Real.log 8 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
        norm_cast
      linarith
    exact this
  have hsplit :
      ∑ n ∈ Icc 2 m, θ (x ^ ((1 : ℝ) / n)) =
        θ (x ^ ((1 : ℝ) / 2)) + ∑ n ∈ Icc 3 m, θ (x ^ ((1 : ℝ) / n)) := by
    have : Icc 2 m = insert 2 (Icc 3 m) := by
      ext n
      simp only [mem_insert, mem_Icc]
      omega
    have hnotin : 2 ∉ Icc 3 m := by
      simp only [mem_Icc, not_and, not_le]
      omega
    rw [this, sum_insert hnotin]
    simp
  rw [hsplit]
  have hsqrt : x ^ ((1 : ℝ) / 2) = √x := (Real.sqrt_eq_rpow x).symm
  have hθ2 : θ (x ^ ((1 : ℝ) / 2)) ≤ Real.log 4 * √x := by
    rw [hsqrt]
    exact theta_le_log4_mul_x (Real.sqrt_nonneg x)
  have hthird : x ^ ((1 : ℝ) / 3) ≤ √x / 2 := rpow_one_third_le_sqrt_div_two hx
  have hterms : ∀ n ∈ Icc 3 m,
      θ (x ^ ((1 : ℝ) / n)) ≤ Real.log 4 * (√x / 2) := by
    intro n hn
    simp only [mem_Icc] at hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn.1)
    have hpow_nonneg : 0 ≤ x ^ ((1 : ℝ) / n) := Real.rpow_nonneg hx0 _
    have hle : x ^ ((1 : ℝ) / n) ≤ x ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x)
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3)
      exact_mod_cast hn.1
    have hle' : x ^ ((1 : ℝ) / n) ≤ √x / 2 := le_trans hle hthird
    have := theta_le_log4_mul_x hpow_nonneg
    have hlog4 : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
    nlinarith [theta_nonneg (x ^ ((1 : ℝ) / n))]
  have hsum3 :
      ∑ n ∈ Icc 3 m, θ (x ^ ((1 : ℝ) / n))
        ≤ ∑ n ∈ Icc 3 m, Real.log 4 * (√x / 2) :=
    sum_le_sum hterms
  have hcard : (#(Icc 3 m) : ℝ) ≤ Real.log x / Real.log 2 := by
    have : #(Icc 3 m) ≤ m := by
      rw [Nat.card_Icc]
      omega
    have hmle : (m : ℝ) ≤ Real.log x / Real.log 2 :=
      Nat.floor_le (log_div_log_two_nonneg (by linarith))
    exact_mod_cast (le_trans (Nat.cast_le.mpr this) hmle)
  have hsum3' :
      ∑ n ∈ Icc 3 m, Real.log 4 * (√x / 2)
        = (#(Icc 3 m) : ℝ) * (Real.log 4 * (√x / 2)) := by
    simp [sum_const, nsmul_eq_mul]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := log_four_eq
  have hrest :
      (#(Icc 3 m) : ℝ) * (Real.log 4 * (√x / 2))
        ≤ (Real.log x / Real.log 2) * (Real.log 4 * (√x / 2)) := by
    have hsq : 0 ≤ Real.log 4 * (√x / 2) := by
      have : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
      positivity
    nlinarith [hcard]
  have hsimp :
      (Real.log x / Real.log 2) * (Real.log 4 * (√x / 2)) = √x * Real.log x := by
    rw [hlog4]
    field
  nlinarith [hθ2, hsum3, hsum3', hrest, hsimp,
    Real.sqrt_nonneg x, Real.log_nonneg (by linarith : (1 : ℝ) ≤ x),
    le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4))]

lemma theta_lower_bound {n : ℕ} (hn : 60 ≤ n) :
    chebC * n - 8 * Real.log n - 25 - |ψ (n : ℝ) - θ (n : ℝ)| ≤ θ (n : ℝ) := by
  have hU := chebC_le_chebU hn
  have hψ : chebU n ≤ ψ (n : ℝ) := chebU_le_psi n
  have : ψ (n : ℝ) - |ψ (n : ℝ) - θ (n : ℝ)| ≤ θ (n : ℝ) := by
    have := le_abs_self (ψ (n : ℝ) - θ (n : ℝ))
    linarith
  linarith

lemma theta_sum_Icc_nat (n : ℕ) :
    θ (n : ℝ) = ∑ p ∈ Icc 0 n with p.Prime, Real.log p := by
  rw [theta_eq_sum_Icc, Nat.floor_natCast]

lemma exists_prime_of_theta_lt {m n : ℕ} (h : θ (m : ℝ) < θ (n : ℝ)) :
    ∃ p, p.Prime ∧ m < p ∧ p ≤ n := by
  have hmn : m < n := by
    by_contra hle
    have : n ≤ m := Nat.not_lt.mp hle
    have : θ (n : ℝ) ≤ θ (m : ℝ) := theta_mono (Nat.cast_le.mpr this)
    linarith
  have hsplit :
      θ (n : ℝ) = θ (m : ℝ)
        + ∑ p ∈ Icc (m + 1) n with p.Prime, Real.log p := by
    rw [theta_sum_Icc_nat, theta_sum_Icc_nat]
    have hun : Icc 0 n = Icc 0 m ∪ Icc (m + 1) n := by
      ext p
      simp only [mem_union, mem_Icc]
      omega
    have hdisj : Disjoint (Icc 0 m) (Icc (m + 1) n) := by
      rw [disjoint_left]
      intro x hx hy
      simp only [mem_Icc] at hx hy
      omega
    rw [hun, filter_union,
      sum_union (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hdisj)]
  have hpos : 0 < ∑ p ∈ Icc (m + 1) n with p.Prime, Real.log p := by
    linarith
  have hne : ((Icc (m + 1) n).filter Nat.Prime).Nonempty := by
    by_contra hempty
    have : (Icc (m + 1) n).filter Nat.Prime = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [this] at hpos
  obtain ⟨p, hp⟩ := hne
  simp only [mem_filter, mem_Icc] at hp
  exact ⟨p, hp.2, by omega, hp.1.2⟩

/- ## Prime chain for the interval `(x, 5x/4]` -/

lemma exists_prime_five_four_succ {n q : ℕ} {p : ℕ} (hp : p.Prime)
    (hcover : 4 * p ≤ 5 * q)
    (H : n < q → ∃ r, r.Prime ∧ n < r ∧ 4 * r ≤ 5 * n)
    (hn : n < p) :
    ∃ r, r.Prime ∧ n < r ∧ 4 * r ≤ 5 * n := by
  by_cases h : n < q
  · exact H h
  · refine ⟨p, hp, hn, ?_⟩
    have : q ≤ n := Nat.not_lt.mp h
    have : 4 * p ≤ 5 * q := hcover
    omega

lemma sqrt_five_four_le (n : ℕ) :
    √(((5 : ℝ) * n) / 4) ≤ (112 / 100 : ℝ) * √(n : ℝ) := by
  have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hsq : ((5 : ℝ) * n) / 4 ≤ ((112 / 100 : ℝ) * √(n : ℝ)) ^ 2 := by
    have : ((112 / 100 : ℝ) * √(n : ℝ)) ^ 2 = (112 / 100 : ℝ) ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt hn0]
    rw [this]
    nlinarith
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, by linarith⟩

lemma log_five_four_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.log (((5 : ℝ) * n) / 4) = Real.log (5 / 4 : ℝ) + Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : ((5 : ℝ) * n) / 4 = (5 / 4 : ℝ) * n := by ring
  rw [this, Real.log_mul (by norm_num) hn0.ne']

lemma exp_one_gt_twentyseven_tenths : (27 / 10 : ℝ) < Real.exp 1 := by
  linarith [exp_one_gt_d9]

lemma pow_twentyseven_tenths_lt_exp (k : ℕ) (hk : 0 < k) :
    ((27 / 10 : ℝ) ^ k) < Real.exp k := by
  have hbase : (27 / 10 : ℝ) < Real.exp 1 := exp_one_gt_twentyseven_tenths
  have : (27 / 10 : ℝ) ^ k < (Real.exp 1) ^ k :=
    pow_lt_pow_left₀ hbase (by norm_num) hk.ne'
  rwa [Real.exp_one_pow] at this

lemma exp_thirteen_gt : (400000 : ℝ) < Real.exp 13 := by
  have hpow : ((27 / 10 : ℝ) ^ 13) < Real.exp 13 :=
    pow_twentyseven_tenths_lt_exp 13 (by decide)
  have hnum : (400000 : ℝ) < (27 / 10 : ℝ) ^ 13 := by norm_num
  linarith

lemma exp_fourteen_gt : (1000000 : ℝ) < Real.exp 14 := by
  have hpow : ((27 / 10 : ℝ) ^ 14) < Real.exp 14 :=
    pow_twentyseven_tenths_lt_exp 14 (by decide)
  have hnum : (1000000 : ℝ) < (27 / 10 : ℝ) ^ 14 := by norm_num
  linarith

lemma exp_twentyone_gt : (1000000000 : ℝ) < Real.exp 21 := by
  have hpow : ((27 / 10 : ℝ) ^ 21) < Real.exp 21 :=
    pow_twentyseven_tenths_lt_exp 21 (by decide)
  have hnum : (1000000000 : ℝ) < (27 / 10 : ℝ) ^ 21 := by norm_num
  linarith

lemma exp_fortytwo_gt : ((10 : ℝ) ^ 18) < Real.exp 42 := by
  have hpow : ((27 / 10 : ℝ) ^ 42) < Real.exp 42 :=
    pow_twentyseven_tenths_lt_exp 42 (by decide)
  have hnum : ((10 : ℝ) ^ 18) < (27 / 10 : ℝ) ^ 42 := by norm_num
  linarith

lemma log_lt_of_lt_exp {n : ℕ} {k : ℝ} (hn0 : 0 < n) (h : (n : ℝ) < Real.exp k) :
    Real.log n < k :=
  (Real.log_lt_iff_lt_exp (by exact_mod_cast hn0)).mpr h

lemma sqrt_n_ge_of_sq_le {n a : ℕ} (h : a * a ≤ n) :
    (a : ℝ) ≤ √(n : ℝ) := by
  have ha : 0 ≤ (a : ℝ) := by exact_mod_cast (Nat.zero_le a)
  have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have : (a : ℝ) ^ 2 ≤ n := by
    have : ((a * a : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    simpa [pow_two, Nat.cast_mul] using this
  exact (Real.le_sqrt ha hn).mpr this

lemma floor_five_mul_div_four (n : ℕ) :
    ⌊((5 : ℝ) * n) / 4⌋₊ = 5 * n / 4 := by
  have := Nat.floor_div_eq_div (K := ℝ) (5 * n) 4
  have heq : ((5 * n : ℕ) : ℝ) / 4 = (5 : ℝ) * n / 4 := by push_cast; ring
  simpa [heq] using this

lemma five_four_error_bound {n : ℕ} (hn : 1 ≤ n)
    {L : ℝ} (hL : Real.log n ≤ L) :
    Real.log (((5 : ℝ) * n) / 4) ≤ L + 23 / 100 := by
  rw [log_five_four_eq hn]
  linarith [log_five_div_four_lt]

lemma nat_sq_le {n a b : ℕ} (hab : a * a = b) (hbn : b ≤ n) : a * a ≤ n := by
  rwa [hab]

/-- Reduce `c n - K √n - D > 0` using `n = (√n)²` and `√n ≥ t0`. -/
lemma quad_pos_of_sqrt_ge {n : ℕ} {t0 c K D : ℝ}
    (hc : 0 < c) (ht0 : 0 ≤ t0) (hn0 : 0 ≤ (n : ℝ))
    (ht : t0 ≤ √(n : ℝ))
    (hslope : 0 < c * t0 - K)
    (hconst : 0 < (c * t0 - K) * t0 - D) :
    0 < c * n - K * √(n : ℝ) - D := by
  set t := √(n : ℝ)
  have htnn : 0 ≤ t := Real.sqrt_nonneg _
  have hsq : (n : ℝ) = t * t := by
    simpa [t, pow_two] using (Real.sq_sqrt hn0).symm
  have hmono : (c * t0 - K) * t0 - D ≤ (c * t - K) * t - D := by
    have hdiff : (c * t - K) * t - (c * t0 - K) * t0
        = (t - t0) * (c * (t + t0) - K) := by ring
    have hfac : 0 ≤ c * (t + t0) - K := by
      have : c * (t + t0) - K ≥ c * (t0 + t0) - K := by nlinarith
      have : c * (t0 + t0) - K = (c * t0 - K) + c * t0 := by ring
      nlinarith
    nlinarith [hdiff, hfac]
  calc
    (0 : ℝ) < (c * t0 - K) * t0 - D := hconst
    _ ≤ (c * t - K) * t - D := hmono
    _ = c * (t * t) - K * t - D := by ring
    _ = c * n - K * t - D := by rw [← hsq]

lemma one_le_five_mul_div_four {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ ((5 : ℝ) * n) / 4 := by
  have : (4 : ℝ) ≤ 5 * n := by
    exact_mod_cast (le_trans (by decide : (4 : ℕ) ≤ 5 * 1) (Nat.mul_le_mul_left 5 hn))
  linarith

lemma log_five_n_div_four_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (((5 : ℝ) * n) / 4) :=
  Real.log_nonneg (one_le_five_mul_div_four hn)

set_option maxHeartbeats 800000 in
/-- Core numerical comparison used for the large-`n` prime-interval argument. -/
lemma five_four_numeric {n : ℕ} (hn : 200000 ≤ n) :
    (9 / 200 : ℝ) * n - 925 / 1000
      > 8 * Real.log (((5 : ℝ) * n) / 4) + 425
        + √(((5 : ℝ) * n) / 4)
            * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
        + 6 * (Real.log n) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 200000) hn
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 200000) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR0 : (0 : ℝ) ≤ n := hnR.le
  have hsqrt54 := sqrt_five_four_le n
  have hlog4 := log_four_lt
  have hlogn_nn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 200000) hn))
  have hsqrtn_nn : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  -- Bound the RHS by `A + B √n` on each range, then apply `quad_pos_of_sqrt_ge`.
  rcases lt_or_ge n 400000 with hA | hA
  · have hlogn : Real.log n < 13 :=
      log_lt_of_lt_exp hn0 (lt_trans (by exact_mod_cast hA) exp_thirteen_gt)
    have hlog54 : Real.log (((5 : ℝ) * n) / 4) ≤ 1323 / 100 := by
      have := five_four_error_bound hn1 hlogn.le
      linarith
    have ht : (447 : ℝ) ≤ √(n : ℝ) :=
      sqrt_n_ge_of_sq_le (nat_sq_le (by norm_num : 447 * 447 = 199809)
        (le_trans (by decide : 199809 ≤ 200000) hn))
    have hRHS :
        8 * Real.log (((5 : ℝ) * n) / 4) + 425
          + √(((5 : ℝ) * n) / 4)
              * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
          + 6 * (Real.log n) ^ 2
        ≤ (1546 : ℝ) + (1638 / 100 : ℝ) * √(n : ℝ) := by
      have hmul : √(((5 : ℝ) * n) / 4) * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
          ≤ (112 / 100 : ℝ) * √(n : ℝ) * (1323 / 100 + 1387 / 1000) := by
        have h1 : 0 ≤ √(((5 : ℝ) * n) / 4) := Real.sqrt_nonneg _
        have h2 : 0 ≤ Real.log (((5 : ℝ) * n) / 4) + Real.log 4 := by
          have : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
          have : 0 ≤ Real.log (((5 : ℝ) * n) / 4) :=
            log_five_n_div_four_nonneg hn1
          linarith
        nlinarith [hsqrt54, hlog54, hlog4]
      nlinarith [hlog54, hlogn, hlogn_nn, hmul]
    have hpos : 0 < (9 / 200 : ℝ) * n - (1638 / 100 : ℝ) * √(n : ℝ) - (1546 + 925 / 1000) :=
      quad_pos_of_sqrt_ge (by norm_num) (by norm_num) hnR0 ht (by norm_num) (by norm_num)
    linarith
  · rcases lt_or_ge n 1000000 with hB | hB
    · have hlogn : Real.log n < 14 :=
        log_lt_of_lt_exp hn0 (lt_trans (by exact_mod_cast hB) exp_fourteen_gt)
      have hlog54 : Real.log (((5 : ℝ) * n) / 4) ≤ 1423 / 100 := by
        have := five_four_error_bound hn1 hlogn.le
        linarith
      have ht : (632 : ℝ) ≤ √(n : ℝ) :=
        sqrt_n_ge_of_sq_le (nat_sq_le (by norm_num : 632 * 632 = 399424)
          (le_trans (by decide : 399424 ≤ 400000) hA))
      have hRHS :
          8 * Real.log (((5 : ℝ) * n) / 4) + 425
            + √(((5 : ℝ) * n) / 4)
                * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
            + 6 * (Real.log n) ^ 2
          ≤ (1716 : ℝ) + (1758 / 100 : ℝ) * √(n : ℝ) := by
        have hmul : √(((5 : ℝ) * n) / 4) * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
            ≤ (112 / 100 : ℝ) * √(n : ℝ) * (1423 / 100 + 1387 / 1000) := by
          have h2 : 0 ≤ Real.log (((5 : ℝ) * n) / 4) + Real.log 4 := by
            have : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
            have : 0 ≤ Real.log (((5 : ℝ) * n) / 4) :=
              log_five_n_div_four_nonneg hn1
            linarith
          nlinarith [hsqrt54, hlog54, hlog4, Real.sqrt_nonneg (((5 : ℝ) * n) / 4)]
        nlinarith [hlog54, hlogn, hlogn_nn, hmul]
      have hpos : 0 < (9 / 200 : ℝ) * n - (1758 / 100 : ℝ) * √(n : ℝ) - (1716 + 925 / 1000) :=
        quad_pos_of_sqrt_ge (by norm_num) (by norm_num) hnR0 ht (by norm_num) (by norm_num)
      linarith
    · rcases lt_or_ge n 1000000000 with hC | hC
      · have hlogn : Real.log n < 21 :=
          log_lt_of_lt_exp hn0 (lt_trans (by exact_mod_cast hC) exp_twentyone_gt)
        have hlog54 : Real.log (((5 : ℝ) * n) / 4) ≤ 2123 / 100 := by
          have := five_four_error_bound hn1 hlogn.le
          linarith
        have ht : (1000 : ℝ) ≤ √(n : ℝ) :=
          sqrt_n_ge_of_sq_le (nat_sq_le (by norm_num : 1000 * 1000 = 1000000) hB)
        have hRHS :
            8 * Real.log (((5 : ℝ) * n) / 4) + 425
              + √(((5 : ℝ) * n) / 4)
                  * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
              + 6 * (Real.log n) ^ 2
            ≤ (3242 : ℝ) + (2534 / 100 : ℝ) * √(n : ℝ) := by
          have hmul : √(((5 : ℝ) * n) / 4) * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
              ≤ (112 / 100 : ℝ) * √(n : ℝ) * (2123 / 100 + 1387 / 1000) := by
            have h2 : 0 ≤ Real.log (((5 : ℝ) * n) / 4) + Real.log 4 := by
              have : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
              have : 0 ≤ Real.log (((5 : ℝ) * n) / 4) :=
                log_five_n_div_four_nonneg hn1
              linarith
            nlinarith [hsqrt54, hlog54, hlog4, Real.sqrt_nonneg (((5 : ℝ) * n) / 4)]
          nlinarith [hlog54, hlogn, hlogn_nn, hmul]
        have hpos : 0 < (9 / 200 : ℝ) * n - (2534 / 100 : ℝ) * √(n : ℝ) - (3242 + 925 / 1000) :=
          quad_pos_of_sqrt_ge (by norm_num) (by norm_num) hnR0 ht (by norm_num) (by norm_num)
        linarith
      · -- n ≥ 10^9: `log n ≤ 4 n^{1/4} ≤ √n / 40`
        have ht : (31622 : ℝ) ≤ √(n : ℝ) :=
          sqrt_n_ge_of_sq_le (nat_sq_le (by norm_num : 31622 * 31622 = 999950884)
            (le_trans (by decide : 999950884 ≤ 1000000000) hC))
        have hlog_rpow : Real.log n ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := by
          have h := Real.log_le_rpow_div (ε := (1 / 4 : ℝ)) hnR0 (by norm_num)
          have : (n : ℝ) ^ ((1 / 4 : ℝ)) / (1 / 4 : ℝ)
              = 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := by field
          linarith
        have hfourth : (n : ℝ) ^ ((1 / 4 : ℝ)) = √(√(n : ℝ)) := by
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hnR0]
          norm_num
        have hfourth_ge : (160 : ℝ) ≤ (n : ℝ) ^ ((1 / 4 : ℝ)) := by
          rw [hfourth]
          have h160sq : (160 : ℝ) ^ 2 ≤ √(n : ℝ) := by
            nlinarith [ht]
          exact (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _)).mpr h160sq
        have hlogn : Real.log n ≤ √(n : ℝ) / 40 := by
          have : 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) ≤ √(n : ℝ) / 40 := by
            have hpos : 0 < (n : ℝ) ^ ((1 / 4 : ℝ)) := Real.rpow_pos_of_pos hnR _
            have hsqrt_eq : √(n : ℝ)
                = (n : ℝ) ^ ((1 / 4 : ℝ)) * (n : ℝ) ^ ((1 / 4 : ℝ)) := by
              have : √(n : ℝ) = (n : ℝ) ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow n
              rw [this, ← Real.rpow_add hnR]
              norm_num
            nlinarith [hfourth_ge, hpos]
          linarith
        have hlog54 : Real.log (((5 : ℝ) * n) / 4) ≤ √(n : ℝ) / 40 + 23 / 100 :=
          five_four_error_bound hn1 hlogn
        have hsqn : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hnR0
        have hmul :
            √(((5 : ℝ) * n) / 4) * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
              ≤ (28 / 1000 : ℝ) * n + (182 / 100 : ℝ) * √(n : ℝ) := by
          -- 1.12 √n * (√n/40 + 1.617) = 1.12 n / 40 + 1.12*1.617 √n
          -- = 0.028 n + 1.811 √n
          have h2 : 0 ≤ Real.log (((5 : ℝ) * n) / 4) + Real.log 4 :=
            add_nonneg (log_five_n_div_four_nonneg hn1)
              (le_of_lt (Real.log_pos (by norm_num)))
          have : (112 / 100 : ℝ) * √(n : ℝ) * (√(n : ℝ) / 40 + 23 / 100 + 1387 / 1000)
              = (112 / 100 : ℝ) / 40 * n
                + (112 / 100 : ℝ) * (23 / 100 + 1387 / 1000) * √(n : ℝ) := by
            nlinarith [hsqn]
          nlinarith [hsqrt54, hlog54, hlog4, h2, Real.sqrt_nonneg (((5 : ℝ) * n) / 4)]
        have hsqlog : 6 * (Real.log n) ^ 2 ≤ (6 / 1600 : ℝ) * n := by
          have : (Real.log n) ^ 2 ≤ (n : ℝ) / 1600 := by
            have : (Real.log n) ^ 2 ≤ (√(n : ℝ) / 40) ^ 2 := by nlinarith [hlogn_nn, hlogn]
            have : (√(n : ℝ) / 40) ^ 2 = (n : ℝ) / 1600 := by
              field; nlinarith [hsqn]
            linarith
          linarith
        have hRHS :
            8 * Real.log (((5 : ℝ) * n) / 4) + 425
              + √(((5 : ℝ) * n) / 4)
                  * (Real.log (((5 : ℝ) * n) / 4) + Real.log 4)
              + 6 * (Real.log n) ^ 2
            ≤ (427 : ℝ) + (32 / 1000 : ℝ) * n + (3 : ℝ) * √(n : ℝ) := by
          nlinarith [hlog54, hmul, hsqlog, ht]
        have : 0 < (9 / 200 - 32 / 1000 : ℝ) * n - 3 * √(n : ℝ) - (427 + 925 / 1000) :=
          quad_pos_of_sqrt_ge (by norm_num) (by norm_num) hnR0 ht (by norm_num) (by norm_num)
        linarith

lemma exists_prime_five_four_large {n : ℕ} (hn : 200000 ≤ n) :
    ∃ p, p.Prime ∧ n < p ∧ 4 * p ≤ 5 * n := by
  set N : ℕ := 5 * n / 4
  have hN_floor : (N : ℝ) = ⌊((5 : ℝ) * n) / 4⌋₊ := by
    simp [N, floor_five_mul_div_four]
  have hN_le : (N : ℝ) ≤ ((5 : ℝ) * n) / 4 := by
    have := Nat.floor_le (show 0 ≤ ((5 : ℝ) * n) / 4 by positivity)
    simpa [hN_floor] using this
  have hN_ge : ((5 : ℝ) * n) / 4 - 1 ≤ (N : ℝ) := by
    have := Nat.lt_floor_add_one (((5 : ℝ) * n) / 4)
    have : ((5 : ℝ) * n) / 4 < (N : ℝ) + 1 := by
      simpa [hN_floor] using this
    linarith
  have hNbig : 250000 ≤ N := by
    have : 250000 ≤ 5 * n / 4 := by omega
    simpa [N] using this
  have hN60 : 60 ≤ N := le_trans (by decide) hNbig
  have hN64 : (64 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (le_trans (by decide : (64 : ℕ) ≤ 250000) hNbig)
  have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 200000) hn
  have hθN := theta_lower_bound hN60
  have hψθ : |ψ (N : ℝ) - θ (N : ℝ)|
      ≤ √(N : ℝ) * (Real.log N + Real.log 4) :=
    abs_psi_sub_theta_of_ge_sixtyfour hN64
  have hψn := psi_upper_bound (le_trans (by decide : (60 : ℕ) ≤ 200000) hn)
  have hθn : θ (n : ℝ) ≤ ψ (n : ℝ) := theta_le_psi _
  have hlogN : Real.log N ≤ Real.log (((5 : ℝ) * n) / 4) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 60) hN60)
    · exact hN_le
  have hsqrtN : √(N : ℝ) ≤ √(((5 : ℝ) * n) / 4) :=
    Real.sqrt_le_sqrt hN_le
  have hnum := five_four_numeric hn
  have hcL : (9 / 10 : ℝ) < chebC := chebC_gt_nine_tenths
  have hcU : chebC < (925 / 1000 : ℝ) := chebC_lt
  have hC0 : 0 ≤ chebC := chebC_nonneg
  have hdiff : θ (n : ℝ) < θ (N : ℝ) := by
    have : chebC * (N : ℝ) - 8 * Real.log N - 25
          - |ψ (N : ℝ) - θ (N : ℝ)|
        > (6 / 5 : ℝ) * chebC * n + 6 * (Real.log n) ^ 2 + 400 := by
      have hnR : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
      have hNpos : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
      nlinarith [hN_ge, hlogN, hsqrtN, hψθ, hnum,
        Real.log_nonneg (by linarith : (1 : ℝ) ≤ (N : ℝ)),
        Real.sqrt_nonneg (N : ℝ),
        Real.sqrt_nonneg (((5 : ℝ) * n) / 4),
        le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4))]
    linarith [hθN, hθn, hψn]
  obtain ⟨p, hp, hpn, hpN⟩ := exists_prime_of_theta_lt hdiff
  refine ⟨p, hp, hpn, ?_⟩
  have h4N : 4 * N ≤ 5 * n := by
    simpa [N] using Nat.mul_div_le (5 * n) 4
  omega

/-- There is a prime in `(n, 5n/4]` for every `n ≥ 25`.
    The prime chain covers `25 ≤ n < 222713`; the analytic argument
    handles `n ≥ 200000`. -/
lemma exists_prime_five_four_of_ge_twentyfive {n : ℕ} (hn : 25 ≤ n) :
    ∃ p, p.Prime ∧ n < p ∧ 4 * p ≤ 5 * n := by
  rcases lt_or_ge n 200000 with hsmall | hlarge
  · have hlt : n < 222713 := hsmall.trans_le (by decide)
    revert hlt
    refine exists_prime_five_four_succ (p := 222713) (q := 178183)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 178183) (q := 142547)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 142547) (q := 114041)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 114041) (q := 91969)
      (by norm_num) (by decide) ?_ 
    refine exists_prime_five_four_succ (p := 91969) (q := 74189)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 74189) (q := 59833)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 59833) (q := 48259)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 48259) (q := 38923)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 38923) (q := 31397)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 31397) (q := 25349)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 25349) (q := 20443)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 20443) (q := 16493)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 16493) (q := 13313)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 13313) (q := 10739)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 10739) (q := 8663)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 8663) (q := 6991)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 6991) (q := 5639)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 5639) (q := 4549)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 4549) (q := 3677)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 3677) (q := 2971)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 2971) (q := 2417)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 2417) (q := 1951)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 1951) (q := 1583)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 1583) (q := 1283)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 1283) (q := 1039)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 1039) (q := 839)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 839) (q := 677)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 677) (q := 547)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 547) (q := 443)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 443) (q := 359)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 359) (q := 293)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 293) (q := 239)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 239) (q := 193)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 193) (q := 157)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 157) (q := 131)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 131) (q := 109)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 109) (q := 89)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 89) (q := 73)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 73) (q := 61)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 61) (q := 53)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 53) (q := 43)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 43) (q := 37)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 37) (q := 31)
      (by norm_num) (by decide) ?_
    refine exists_prime_five_four_succ (p := 31) (q := 29)
      (by norm_num) (by decide) ?_
    intro hn29
    -- n < 29 and n ≥ 25, so n ∈ {25,26,27,28}; prime 29 works
    refine ⟨29, by norm_num, hn29, ?_⟩
    have : 25 ≤ n := hn
    omega
  · exact exists_prime_five_four_large hlarge

/- ## Next prime after `s` and the interval `[A, A+2q]` -/

lemma exists_next_prime_five_four {s : ℕ} (hs : 25 ≤ s) :
    ∃ q, q.Prime ∧ s < q ∧ 4 * q ≤ 5 * s :=
  exists_prime_five_four_of_ge_twentyfive hs

/-- If `A` itself is prime then we are immediately done. -/
lemma exists_prime_of_A_prime {n q : ℕ} (hq : q.Prime) (hA : 1 ≤ q ^ 2 - n)
    (h2 : n < q ^ 2) (hpn : q ^ 2 - n < n) :
    (q ^ 2 - n).Prime →
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  intro hpA
  refine ⟨q ^ 2 - n, hpA, hpn, ?_⟩
  have hlo : q ^ 2 ≤ n + (q ^ 2 - n) := by omega
  have hhi : n + (q ^ 2 - n) < (q + 1) ^ 2 := by
    have : n + (q ^ 2 - n) = q ^ 2 := by omega
    rw [this, add_sq]
    omega
  have : Nat.sqrt (n + (q ^ 2 - n)) = q :=
    ((Nat.eq_sqrt' (a := q) (n := n + (q ^ 2 - n))).mpr ⟨hlo, hhi⟩).symm
  rwa [this]

/-- For `q ≤ 5s/4` and `s ≥ 7`, one has `q² + 2q < 2 s²`. -/
lemma q_sq_add_two_q_lt_two_s_sq {q s : ℕ} (hs : 7 ≤ s) (hqs : 4 * q ≤ 5 * s) :
    q ^ 2 + 2 * q < 2 * s ^ 2 := by
  have hqi : (4 : ℤ) * q ≤ 5 * s := by exact_mod_cast hqs
  have hsi : (7 : ℤ) ≤ s := by exact_mod_cast hs
  have : (q : ℤ) ^ 2 + 2 * q < 2 * (s : ℤ) ^ 2 := by nlinarith
  exact_mod_cast this

lemma p_lt_n_of_interval {n q s : ℕ} (hs : 7 ≤ s) (hsn : s ^ 2 ≤ n)
    (hqs : 4 * q ≤ 5 * s) (h2 : n < q ^ 2) :
    q ^ 2 - n + 2 * q < n := by
  have hlt := q_sq_add_two_q_lt_two_s_sq hs hqs
  have hn2 : 2 * s ^ 2 ≤ 2 * n := Nat.mul_le_mul_left 2 hsn
  have hqn : n ≤ q ^ 2 := Nat.le_of_lt h2
  have : q ^ 2 + 2 * q < 2 * n := lt_of_lt_of_le hlt hn2
  omega

/-- A prime in `[A, A+2q]` with `A = q²-n` yields the conjecture. -/
lemma exists_of_prime_in_interval {n q : ℕ} (hq : q.Prime)
    (h2 : n < q ^ 2) (hp : ∃ p, p.Prime ∧ q ^ 2 - n ≤ p ∧ p ≤ q ^ 2 - n + 2 * q)
    (hpn : q ^ 2 - n + 2 * q < n) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨p, hpP, hpL, hpU⟩ := hp
  refine ⟨p, hpP, lt_of_le_of_lt hpU hpn, ?_⟩
  have hlo : q ^ 2 ≤ n + p := (Nat.sub_le_iff_le_add').mp hpL
  have hhi : n + p < (q + 1) ^ 2 := by
    have : n + p ≤ n + (q ^ 2 - n + 2 * q) := Nat.add_le_add_left hpU n
    have heq : n + (q ^ 2 - n + 2 * q) = q ^ 2 + 2 * q := by
      have : n ≤ q ^ 2 := Nat.le_of_lt h2
      omega
    have : n + p ≤ q ^ 2 + 2 * q := by rwa [heq] at this
    have : q ^ 2 + 2 * q < (q + 1) ^ 2 := by rw [add_sq]; omega
    omega
  have : Nat.sqrt (n + p) = q :=
    ((Nat.eq_sqrt' (a := q) (n := n + p)).mpr ⟨hlo, hhi⟩).symm
  rwa [this]

/-- If `A ≤ 8q` and `A ≥ 25`, the 5/4 theorem supplies a prime in `(A, 5A/4] ⊆ (A, A+2q]`. -/
lemma exists_prime_of_A_le_eight_q {A q : ℕ} (hA : 25 ≤ A) (hAq : A ≤ 8 * q) :
    ∃ p, p.Prime ∧ A < p ∧ p ≤ A + 2 * q := by
  obtain ⟨p, hp, hpA, hp4⟩ := exists_prime_five_four_of_ge_twentyfive hA
  refine ⟨p, hp, hpA, ?_⟩
  -- `4p ≤ 5A` ⇒ `p ≤ 5A/4` ⇒ `p ≤ A + A/4` ⇒ `p ≤ A + 2q` since `A ≤ 8q`
  have : 4 * p ≤ 5 * A := hp4
  have : p ≤ A + 2 * q := by
    have h1 : 4 * p ≤ 5 * A := this
    have h2 : A ≤ 8 * q := hAq
    omega
  exact this

lemma exists_prime_of_A_le_eight_q' {A q : ℕ} (hA : 1 ≤ A) (hAq : A ≤ 8 * q)
    (hq12 : 12 ≤ q) :
    ∃ p, p.Prime ∧ A ≤ p ∧ p ≤ A + 2 * q := by
  by_cases hAp : A.Prime
  · exact ⟨A, hAp, le_rfl, Nat.le_add_right _ _⟩
  by_cases h25 : 25 ≤ A
  · obtain ⟨p, hp, hpA, hpU⟩ := exists_prime_of_A_le_eight_q h25 hAq
    exact ⟨p, hp, Nat.le_of_lt hpA, hpU⟩
  -- `A ≤ 24` and `q ≥ 12` ⇒ `A ≤ 2q+1`, so Bertrand applies.
  have hLq : A ≤ 2 * q + 1 := by
    have : A ≤ 24 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h25)
    omega
  rcases eq_or_ne A 1 with rfl | hAne
  · refine ⟨2, Nat.prime_two, by omega, ?_⟩
    omega
  have hA2 : 2 ≤ A := by omega
  have hApos : A ≠ 0 := by omega
  obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul A hApos
  refine ⟨p, hp, Nat.le_of_lt hpgt, ?_⟩
  have p_ne : p ≠ 2 * A := by
    intro h
    have hpr : (2 * A).Prime := h ▸ hp
    have : ¬ (2 * A).Prime :=
      Nat.not_prime_mul (by omega) (by omega)
    exact this hpr
  have hp_lt : p < 2 * A := lt_of_le_of_ne hple p_ne
  have hp_le' : p ≤ 2 * A - 1 := Nat.le_pred_of_lt hp_lt
  have : 2 * A - 1 ≤ A + 2 * q := by omega
  exact hp_le'.trans this

/- ## Small-`n` computational check (copied from the submission skeleton) -/

lemma exists_of_sqrt_n_add_two_prime {n : ℕ} (hn : n > 2)
    (hp : (Nat.sqrt (n + 2)).Prime) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime :=
  ⟨2, Nat.prime_two, hn, hp⟩

def holdsDec (n : ℕ) : Bool :=
  decide (∃ p ∈ Finset.range n, p.Prime ∧ (Nat.sqrt (n + p)).Prime)

lemma holdsDec_spec {n : ℕ} (h : holdsDec n = true) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  unfold holdsDec at h
  have : ∃ p ∈ Finset.range n, p.Prime ∧ (Nat.sqrt (n + p)).Prime :=
    of_decide_eq_true h
  obtain ⟨p, hpmem, hp, hsqrt⟩ := this
  exact ⟨p, hp, Finset.mem_range.mp hpmem, hsqrt⟩

lemma holds_le_2000 : ∀ n ≤ 2000, n ≤ 2 ∨ holdsDec n = true := by
  native_decide

lemma sqrt_n_ge_fortyfour {n : ℕ} (hn : 2001 ≤ n) : 44 ≤ Nat.sqrt n := by
  have : 44 ^ 2 ≤ n := by
    have : 44 ^ 2 = 1936 := by decide
    omega
  exact (Nat.le_sqrt).mpr this

lemma sqrt_lt_succ (n : ℕ) : n < (Nat.sqrt n + 1) ^ 2 :=
  Nat.lt_succ_sqrt' n

/-- The large-`n` argument when `A = q² - n ≤ 8q`. -/
lemma large_of_A_le_eight {n q s : ℕ} (hq : q.Prime)
    (hs7 : 7 ≤ s) (hsq : s < q) (hs44 : 44 ≤ s)
    (hsn : s ^ 2 ≤ n) (h2 : n < q ^ 2) (hqs : 4 * q ≤ 5 * s)
    (hA8 : q ^ 2 - n ≤ 8 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  have hA : 1 ≤ q ^ 2 - n := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt h2)
  have hq12 : 12 ≤ q := by omega
  have hpn : q ^ 2 - n + 2 * q < n := p_lt_n_of_interval hs7 hsn hqs h2
  obtain ⟨p, hp, hpL, hpU⟩ := exists_prime_of_A_le_eight_q' hA hA8 hq12
  exact exists_of_prime_in_interval hq h2 ⟨p, hp, hpL, hpU⟩ hpn

/-- Main large-`n` reduction: pick the next prime `q` after `⌊√n⌋`. -/
lemma large_n_reduction {n : ℕ} (hn : 2001 ≤ n) :
    ∃ q, q.Prime ∧ n < q ^ 2 ∧
      (q ^ 2 - n ≤ 8 * q →
        ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime) ∧
      q ^ 2 - n + 2 * q < n := by
  set s := Nat.sqrt n
  have hs44 : 44 ≤ s := sqrt_n_ge_fortyfour hn
  have hs25 : 25 ≤ s := le_trans (by decide) hs44
  have hs7 : 7 ≤ s := le_trans (by decide) hs44
  obtain ⟨q, hq, hsq, hqs⟩ := exists_prime_five_four_of_ge_twentyfive hs25
  have hsn : s ^ 2 ≤ n := Nat.sqrt_le' n
  have hn1 : n < (s + 1) ^ 2 := sqrt_lt_succ n
  have h2 : n < q ^ 2 := by
    have : (s + 1) ≤ q := Nat.succ_le_iff.mpr hsq
    have : (s + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have hpn : q ^ 2 - n + 2 * q < n := p_lt_n_of_interval hs7 hsn hqs h2
  refine ⟨q, hq, h2, ?_, hpn⟩
  intro hA8
  exact large_of_A_le_eight hq hs7 hsq hs44 hsn h2 hqs hA8

















