import FormalConjectures.Util.ProblemImports

open Real Nat Finset

def prodRange (start len : ℕ) : ℕ :=
  (List.range len).foldl (fun acc i => acc * (start + i)) 1

lemma prodRange_zero (start : ℕ) : prodRange start 0 = 1 := rfl

lemma prodRange_succ (start len : ℕ) :
    prodRange start (len + 1) = prodRange start len * (start + len) := by
  simp [prodRange, List.range_succ, List.foldl_cons]

lemma nat_pow_succ_left (a n : ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

lemma prodRange_one (start : ℕ) : prodRange start 1 = start := by
  simp [prodRange]

lemma prodRange_mul_front (start : ℕ) : ∀ n,
    prodRange start (n + 1) = start * prodRange (start + 1) n
  | 0 => by simp [prodRange]
  | n + 1 => by
    rw [prodRange_succ start (n + 1)]
    rw [prodRange_mul_front start n]
    rw [prodRange_succ (start + 1) n]
    ring

lemma prodRange_peel (start n : ℕ) :
    prodRange start (n + 2) =
      start * (start + n + 1) * prodRange (start + 1) n := by
  have h1 := prodRange_succ start (n + 1)
  have h2 : start + (n + 1) = start + n + 1 := by omega
  rw [h1, h2, prodRange_mul_front]
  ring

lemma peel_ends_le (start n : ℕ) :
    start * (start + n + 1) ≤ (start + 1) * (start + n) := by
  nlinarith

lemma prodRange_pair_ge : ∀ (len start : ℕ), 1 ≤ start →
    (start * (start + len - 1)) ^ (len / 2) ≤ prodRange start len
  | 0, start, _ => by simp [prodRange]
  | 1, start, hstart => by
    simp [prodRange]
    exact hstart
  | n + 2, start, hstart => by
    rw [prodRange_peel]
    have hn2 : (n + 2) / 2 = n / 2 + 1 := by omega
    have hend : start + (n + 2) - 1 = start + n + 1 := by omega
    rw [hn2, nat_pow_succ_left, hend]
    have ih := prodRange_pair_ge n (start + 1) (by omega)
    have hmid : start + 1 + n - 1 = start + n := by omega
    rw [hmid] at ih
    have hends := peel_ends_le start n
    have hpow : (start * (start + n + 1)) ^ (n / 2) ≤
        ((start + 1) * (start + n)) ^ (n / 2) :=
      Nat.pow_le_pow_left hends _
    have hmidle : (start * (start + n + 1)) ^ (n / 2) ≤ prodRange (start + 1) n :=
      le_trans hpow ih
    exact Nat.mul_le_mul_left _ hmidle


lemma real_am2 (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma am_ends (start n : ℕ) :
    (start : ℝ) * ((start : ℝ) + n + 1) ≤
      ((2 * (start : ℝ) + n + 1) / 2) ^ 2 := by
  convert real_am2 (start : ℝ) ((start : ℝ) + n + 1) using 2
  ring

lemma prodRange_am_le : ∀ (len start : ℕ),
    (prodRange start len : ℝ) ≤
      ((2 * (start : ℝ) + (len : ℝ) - 1) / 2) ^ len
  | 0, start => by simp [prodRange]
  | 1, start => by simp [prodRange]
  | n + 2, start => by
    rw [prodRange_peel]
    push_cast
    have ham := am_ends start n
    have ih := prodRange_am_le n (start + 1)
    have hAMmid : (2 * ((start + 1 : ℕ) : ℝ) + (n : ℝ) - 1) / 2 =
        (2 * (start : ℝ) + n + 1) / 2 := by
      push_cast; ring
    rw [hAMmid] at ih
    have hAM : (2 * (start : ℝ) + ((n : ℝ) + 2) - 1) / 2 =
        (2 * (start : ℝ) + n + 1) / 2 := by ring
    rw [hAM]
    have hmul := mul_le_mul ham ih (by positivity) (by positivity)
    have hpow : ((2 * (start : ℝ) + n + 1) / 2) ^ 2 *
        ((2 * (start : ℝ) + n + 1) / 2) ^ n =
        ((2 * (start : ℝ) + n + 1) / 2) ^ (n + 2) := by
      rw [← pow_add, Nat.add_comm]
    rw [← hpow]
    exact hmul

lemma prodRange_pair_ge_odd : ∀ (q start : ℕ), 1 ≤ start →
    (start * (start + 2 * q)) ^ q * (start + q) ≤ prodRange start (2 * q + 1)
  | 0, start, _ => by simp [prodRange]
  | q + 1, start, hstart => by
    have hlen : 2 * (q + 1) + 1 = (2 * q + 1) + 2 := by omega
    rw [hlen, prodRange_peel]
    have hidx : start + (2 * q + 1) + 1 = start + 2 * (q + 1) := by omega
    rw [hidx]
    have ih := prodRange_pair_ge_odd q (start + 1) (by omega)
    have hmid : start + 1 + q = start + (q + 1) := by omega
    have hspan : start + 1 + 2 * q = start + 2 * q + 1 := by omega
    rw [hmid, hspan] at ih
    have hends : start * (start + 2 * (q + 1)) ≤
        (start + 1) * (start + 2 * q + 1) :=
      peel_ends_le start (2 * q + 1)
    have hpow : (start * (start + 2 * (q + 1))) ^ q ≤
        ((start + 1) * (start + 2 * q + 1)) ^ q :=
      Nat.pow_le_pow_left hends _
    -- (first*last)^{q+1} * middle = first*last * (first*last)^q * (start+q+1)
    have hrew : (start * (start + 2 * (q + 1))) ^ (q + 1) * (start + (q + 1)) =
        start * (start + 2 * (q + 1)) *
          ((start * (start + 2 * (q + 1))) ^ q * (start + (q + 1))) := by
      rw [nat_pow_succ_left]; ring
    rw [hrew]
    have hcore : (start * (start + 2 * (q + 1))) ^ q * (start + (q + 1)) ≤
        prodRange (start + 1) (2 * q + 1) :=
      le_trans (Nat.mul_le_mul_right _ hpow) ih
    exact Nat.mul_le_mul_left _ hcore

lemma middle_sq_ge (start q : ℕ) :
    start * (start + 2 * q) ≤ (start + q) * (start + q) := by
  nlinarith

lemma middle_ge_sqrt (start q : ℕ) :
    Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) ≤ (start + q : ℝ) := by
  refine (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
  have h := middle_sq_ge start q
  have : (((start + q) * (start + q) : ℕ) : ℝ) = (start + q : ℝ) ^ 2 := by
    push_cast; ring
  rw [← this]
  exact Nat.cast_le (α := ℝ) |>.mpr h


lemma prodRange_pair_ge_real (start len : ℕ) (hstart : 1 ≤ start) (hlen : 1 ≤ len) :
    ((start * (start + len - 1) : ℕ) : ℝ) ^ ((len : ℝ) / 2) ≤
      (prodRange start len : ℝ) := by
  rcases Nat.even_or_odd len with heven | hodd
  · obtain ⟨q, hq⟩ := heven
    have hdiv : (len : ℝ) / 2 = (q : ℝ) := by
      rw [hq]; push_cast; ring
    rw [hdiv, Real.rpow_natCast]
    have hpair := prodRange_pair_ge len start hstart
    have hhalf : len / 2 = q := by omega
    rw [hhalf] at hpair
    have : ((start * (start + len - 1) : ℕ) : ℝ) ^ q =
        (((start * (start + len - 1)) ^ q : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
    rw [this]
    exact Nat.cast_le (α := ℝ) |>.mpr hpair
  · obtain ⟨q, hq⟩ := hodd
    have hdiv : (len : ℝ) / 2 = (q : ℝ) + 1 / 2 := by
      rw [hq]; push_cast; ring
    rw [hdiv]
    have hmulpos : 1 ≤ start * (start + len - 1) := by
      have : 1 ≤ start + len - 1 := by omega
      exact Nat.mul_le_mul hstart this
    have hpos : (0 : ℝ) < ((start * (start + len - 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hmulpos)
    have hrpow :
        ((start * (start + len - 1) : ℕ) : ℝ) ^ ((q : ℝ) + 1 / 2) =
          ((start * (start + len - 1) : ℕ) : ℝ) ^ (q : ℕ) *
            Real.sqrt ((start * (start + len - 1) : ℕ) : ℝ) := by
      rw [Real.rpow_add hpos, Real.rpow_natCast, Real.sqrt_eq_rpow]
    rw [hrpow]
    have hend : start + len - 1 = start + 2 * q := by omega
    have hlen' : 2 * q + 1 = len := by omega
    have hodd' := prodRange_pair_ge_odd q start hstart
    rw [hend, ← hlen']
    have hmid : Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) ≤ (start + q : ℝ) :=
      middle_ge_sqrt start q
    have hpow_nonneg : (0 : ℝ) ≤ ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) := by
      positivity
    have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt ((start * (start + 2 * q) : ℕ) : ℝ) :=
      Real.sqrt_nonneg _
    have hmul := mul_le_mul (le_rfl : ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) ≤ _)
      hmid hsqrt_nonneg hpow_nonneg
    refine le_trans hmul ?_
    have : ((start * (start + 2 * q) : ℕ) : ℝ) ^ (q : ℕ) * (start + q : ℝ) =
        (((start * (start + 2 * q)) ^ q * (start + q) : ℕ) : ℝ) := by
      push_cast; ring
    rw [this]
    exact Nat.cast_le (α := ℝ) |>.mpr hodd'


/-- `-log(1-z) ≤ z/(1-z)` for `0 ≤ z < 1`. -/
lemma neg_log_one_sub_le_div {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z / (1 - z) := by
  by_cases hz : z = 0
  · subst hz; simp
  · have habs : |z| < 1 := by
      rw [abs_of_nonneg hz0]; exact hz1
    have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
    have hterm : ∀ n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ≤ z ^ (n + 1) := by
      intro n
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact div_le_self (pow_nonneg hz0 _) hden
    have hsg : Summable (fun n : ℕ => z ^ (n + 1)) := by
      have := (summable_geometric_of_lt_one hz0 hz1).mul_left z
      convert this using 1
      ext n
      rw [pow_succ]
      ring
    have hle : ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) ≤ ∑' n : ℕ, z ^ (n + 1) :=
      Summable.tsum_le_tsum hterm hsum.summable hsg
    have hgeom : ∑' n : ℕ, z ^ (n + 1) = z / (1 - z) := by
      have h0 : ∑' n : ℕ, z ^ n = (1 - z)⁻¹ := tsum_geometric_of_lt_one hz0 hz1
      have : ∑' n : ℕ, z ^ (n + 1) = z * ∑' n : ℕ, z ^ n := by
        simpa [pow_succ, mul_comm] using
          (tsum_mul_left (a := z) (f := fun n : ℕ => z ^ n))
      rw [this, h0]
      field_simp
    have heq : -Real.log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / ((n : ℝ) + 1) :=
      hsum.tsum_eq.symm
    linarith

lemma log_one_sub_ge_div {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -(z / (1 - z)) ≤ Real.log (1 - z) := by
  have := neg_log_one_sub_le_div hz0 hz1
  linarith

lemma log_one_sub_ge_five_four {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 5) :
    -((5 / 4) * z) ≤ Real.log (1 - z) := by
  have hz1 : z < 1 := lt_of_le_of_lt hz (by norm_num)
  have h := log_one_sub_ge_div hz0 hz1
  have hden : (4 : ℝ) / 5 ≤ 1 - z := by linarith
  have hdiv : z / (1 - z) ≤ z / (4 / 5) :=
    div_le_div_of_nonneg_left hz0 (by norm_num) hden
  have : z / (4 / 5) = (5 / 4) * z := by field_simp
  linarith

lemma log_four_lt : Real.log 4 < 7 / 5 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_cast
  linarith

lemma fact13_eq : (13 : ℕ).factorial = 6227020800 := by native_decide

lemma exp_seven_gt_1095 : (1095 : ℝ) < Real.exp 7 := by
  have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow : (2718 / 1000 : ℝ) ^ 7 < Real.exp 1 ^ 7 :=
    pow_lt_pow_left₀ hbase (by positivity) (by decide : (7 : ℕ) ≠ 0)
  have hexp : Real.exp 1 ^ 7 = Real.exp 7 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 7).symm
  have hrat : (1095 : ℝ) < (2718 / 1000 : ℝ) ^ 7 := by
    rw [div_pow]
    have hN : (1095 : ℕ) * 1000 ^ 7 < 2718 ^ 7 := by native_decide
    have : (1095 : ℝ) * 1000 ^ 7 < 2718 ^ 7 := by exact_mod_cast hN
    have hpos : (0 : ℝ) < 1000 ^ 7 := by positivity
    exact (lt_div_iff₀ hpos).mpr (by linarith)
  linarith

lemma exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have : (27 / 10 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have : (27 / 10 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left₀ this (by positivity) (by decide : (2 : ℕ) ≠ 0)
  have : Real.exp 1 ^ 2 = Real.exp 2 := by
    simpa using (Real.exp_nat_mul (1 : ℝ) 2).symm
  have : (27 / 10 : ℝ) ^ 2 = 729 / 100 := by norm_num
  linarith

lemma pow1095_three : (1095 : ℕ) ^ 3 = 1312932375 := by native_decide

lemma log_fact13_lt_23 : Real.log ((13 : ℕ).factorial : ℝ) < 23 := by
  rw [fact13_eq]
  have hpos : (0 : ℝ) < 6227020800 := by norm_num
  refine (Real.log_lt_iff_lt_exp hpos).mpr ?_
  have h7 := exp_seven_gt_1095
  have h2 := exp_two_gt_seven
  have hexp : Real.exp 23 = Real.exp 7 ^ 3 * Real.exp 2 := by
    have h23 : (23 : ℝ) = 3 * 7 + 2 := by norm_num
    rw [h23, Real.exp_add]
    have : Real.exp (3 * 7) = Real.exp 7 ^ 3 := by
      simpa using Real.exp_nat_mul (7 : ℝ) 3
    rw [this]
  have h1095 : (1095 : ℝ) ^ 3 * 7 < Real.exp 7 ^ 3 * Real.exp 2 := by
    have h1 : (1095 : ℝ) ^ 3 < Real.exp 7 ^ 3 :=
      pow_lt_pow_left₀ h7 (by positivity) (by decide : (3 : ℕ) ≠ 0)
    nlinarith [exp_pos (7 : ℝ), exp_pos (2 : ℝ)]
  have hnum : (6227020800 : ℝ) < (1095 : ℝ) ^ 3 * 7 := by
    have : (1095 : ℕ) ^ 3 * 7 = 9190526625 := by
      rw [pow1095_three]
    have : (6227020800 : ℕ) < 9190526625 := by decide
    exact_mod_cast this
  linarith

lemma ten_le_log2 (k : ℕ) (hk : 2001 ≤ k) : 10 ≤ Nat.log 2 k := by
  have hpow : 2 ^ 10 ≤ k := by omega
  exact (Nat.le_log_iff_pow_le (by decide : 1 < 2) (by omega : k ≠ 0)).2 hpow

lemma log_k_ge_log2_mul (k : ℕ) (hk : 1 ≤ k) :
    (Nat.log 2 k : ℝ) * Real.log 2 ≤ Real.log k := by
  have hpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpow : (2 : ℕ) ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
  have : ((2 : ℕ) ^ Nat.log 2 k : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpow
  have h2pos : (0 : ℝ) < (2 : ℕ) ^ Nat.log 2 k := by exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  have hlog := Real.log_le_log h2pos this
  have : Real.log (((2 : ℕ) : ℝ) ^ Nat.log 2 k) =
      (Nat.log 2 k : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
    ring
  rwa [this] at hlog

lemma leftover_numeric (L : ℕ) (hL : 10 ≤ L) :
    (168 : ℝ) / 5 + (27 : ℝ) / 8 * L < 10 * L * 0.6931471803 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hL
  push_cast
  nlinarith

lemma leftover_const_neg (k : ℕ) (hk : 2001 ≤ k) :
    (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k < 0 := by
  have hL := ten_le_log2 k hk
  have hlog := log_k_ge_log2_mul k (by omega)
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hnum := leftover_numeric (Nat.log 2 k) hL
  nlinarith

lemma j_cast (k s : ℕ) (hs : s ≤ k) :
    ((k - s + 1 : ℕ) : ℝ) = (k : ℝ) - s + 1 := by
  have : k - s + 1 = k + 1 - s := by omega
  rw [this, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  ring

lemma jp1_cast (k s : ℕ) (hs : s + 2 ≤ k) :
    ((k - s + 2 : ℕ) : ℝ) = (k : ℝ) - s + 2 := by
  have : k - s + 2 = k + 2 - s := by omega
  rw [this, Nat.cast_sub (by omega : s ≤ k + 2), Nat.cast_add, Nat.cast_two]
  ring

lemma km1_cast (k : ℕ) (hk : 1 ≤ k) :
    ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
  rw [Nat.cast_sub hk, Nat.cast_one]

lemma jp1_as_mul (k s : ℕ) (hs : s + 2 ≤ k) :
    ((k - s + 2 : ℕ) : ℝ) = (k : ℝ) * (1 - ((s : ℝ) - 2) / k) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : 2 ≤ k := by omega
    exact_mod_cast (show k ≠ 0 by omega)
  rw [jp1_cast k s hs]
  field_simp [hk0]
  ring

lemma am_as_mul (k s : ℕ) (hk : 1 ≤ k) :
    (2 * (k : ℝ) + s - 14) / 2 = (k : ℝ) * (1 + ((s : ℝ) - 14) / (2 * k)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp [hk0]
  ring

lemma log_am_le (k s : ℕ) (hk : 1 ≤ k) (hs : 14 ≤ s) :
    Real.log ((2 * (k : ℝ) + s - 14) / 2) ≤
      Real.log k + ((s : ℝ) - 14) / (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ham : (0 : ℝ) < (2 * (k : ℝ) + s - 14) / 2 := by
    have : (14 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hsR : (14 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 : (0 : ℝ) < 1 + ((s : ℝ) - 14) / (2 * k) := by
    have : (0 : ℝ) ≤ ((s : ℝ) - 14) / (2 * k) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  rw [am_as_mul k s hk, Real.log_mul (ne_of_gt hk0) (ne_of_gt h1)]
  have : Real.log (1 + ((s : ℝ) - 14) / (2 * k)) ≤
      ((s : ℝ) - 14) / (2 * k) :=
    Real.log_le_sub_one_of_pos h1 |>.trans (by linarith)
  linarith

lemma log_jp1_ge (k s : ℕ) (hk : 2001 ≤ k) (hs5 : 5 * s ≤ k) (hs : 45 ≤ s) :
    Real.log k - (5 / 4) * ((s : ℝ) - 2) / k ≤
      Real.log ((k - s + 2 : ℕ) : ℝ) := by
  have hsk : s + 2 ≤ k := by
    have : 5 * s ≤ k := hs5
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz : ((s : ℝ) - 2) / k ≤ 1 / 5 := by
    have : (s : ℝ) / k ≤ 1 / 5 := by
      have h := (Nat.cast_le (α := ℝ)).mpr hs5
      have : (5 : ℝ) * s ≤ k := by exact_mod_cast hs5
      have hk0' : (0 : ℝ) < k := hk0
      have : (s : ℝ) ≤ k / 5 := (le_div_iff₀ (by norm_num)).mpr (by linarith)
      exact (div_le_iff₀ hk0').mpr (by linarith)
    have : ((s : ℝ) - 2) / k ≤ s / k := by
      apply div_le_div_of_nonneg_right
      · linarith
      · positivity
    linarith
  have hz0 : 0 ≤ ((s : ℝ) - 2) / k := by
    apply div_nonneg
    · have : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
      linarith
    · positivity
  have hz1 : ((s : ℝ) - 2) / k < 1 := lt_of_le_of_lt hz (by norm_num)
  rw [jp1_as_mul k s hsk, Real.log_mul (ne_of_gt hk0) (by
    have : 0 < 1 - ((s : ℝ) - 2) / k := by linarith
    exact ne_of_gt this)]
  have hge := log_one_sub_ge_five_four hz0 hz
  have hrew : (5 / 4 : ℝ) * ((s : ℝ) - 2) / k = (5 / 4) * (((s : ℝ) - 2) / k) := by
    ring
  linarith [hrew]

lemma log_km1_ge' (k : ℕ) (hk : 2001 ≤ k) :
    Real.log k - 2 / k ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hz : (1 : ℝ) / k ≤ 1 / 5 := by
    apply one_div_le_one_div_of_le
    · norm_num
    · exact_mod_cast (show 5 ≤ k by omega)
  have hz0 : 0 ≤ (1 : ℝ) / k := by positivity
  have hpos : (0 : ℝ) < 1 - 1 / k := by
    have : (1 : ℝ) / k < 1 := (div_lt_one hk0).mpr (by exact_mod_cast (show 1 < k by omega))
    linarith
  have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) * (1 - 1 / k) := by
    rw [km1_cast k (by omega)]
    field_simp [hk0.ne']
  rw [this, Real.log_mul (ne_of_gt hk0) (ne_of_gt hpos)]
  have hge := log_one_sub_ge_five_four (z := (1 : ℝ) / k) hz0 hz
  have : (5 / 4 : ℝ) * (1 / k) ≤ 2 / k := by
    field_simp
    linarith
  linarith

lemma leftover_lhs_bound (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) ≤
      (7 : ℝ) / 5 + Real.log k + 23 +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) := by
  have hsle : s ≤ k := by omega
  have hs14 : 14 ≤ s := by omega
  have hjpos : (0 : ℝ) < ((k - s + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 1 by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlogj : Real.log ((k - s + 1 : ℕ) : ℝ) ≤ Real.log k :=
    Real.log_le_log hjpos (by
      have : k - s + 1 ≤ k := by omega
      exact_mod_cast this)
  have ham := log_am_le k s (by omega) hs14
  have hf := log_fact13_lt_23
  have h4 := log_four_lt
  have hs13 : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
    rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
  have hnn : (0 : ℝ) ≤ ((s - 13 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hmul := mul_le_mul_of_nonneg_left ham hnn
  exact add_le_add (add_le_add (add_le_add (le_of_lt h4) hlogj) (le_of_lt hf)) hmul

lemma leftover_rhs_bound (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log k - (5 / 4) * ((s : ℝ) - 2) / k + Real.log k - 2 / k) ≤
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) := by
  have hjp := log_jp1_ge k s hk hs5 hs
  have hkm := log_km1_ge' k hk
  have hnn : (0 : ℝ) ≤ ((s - 2 : ℕ) : ℝ) / 2 := by
    apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · norm_num
  apply mul_le_mul_of_nonneg_left _ hnn
  linarith

lemma leftover_expanded (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) ≤
      (7 : ℝ) / 5 + 23 + Real.log k +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (2 * Real.log k - (5 / 4) * ((s : ℝ) - 2) / k - 2 / k) := by
  have hl := leftover_lhs_bound k s hk hs hs5
  have hr := leftover_rhs_bound k s hk hs hs5
  linarith

lemma leftover_simplify (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) :
    (7 : ℝ) / 5 + 23 + Real.log k +
        ((s - 13 : ℕ) : ℝ) * (Real.log k + ((s : ℝ) - 14) / (2 * k)) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (2 * Real.log k - (5 / 4) * ((s : ℝ) - 2) / k - 2 / k) =
      (7 : ℝ) / 5 + 23 - 10 * Real.log k +
        ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
        (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
        ((s : ℝ) - 2) / k := by
  have hs13 : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
    rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
  have hs2 : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ s)]; norm_num
  rw [hs13, hs2]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp [hk0]
  ring

lemma leftover_errors_le (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
        (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
        ((s : ℝ) - 2) / k ≤
      (9 / 8) * (3 * Nat.log 2 k + 8 : ℝ) + 1 / 5 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsR : (45 : ℝ) ≤ s := by exact_mod_cast hs
  have hssR : (s : ℝ) * s ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by
    exact_mod_cast hss
  have hs2k : (s : ℝ) ^ 2 / k ≤ (3 * Nat.log 2 k + 8 : ℝ) := by
    have : (s : ℝ) ^ 2 ≤ (k : ℝ) * (3 * Nat.log 2 k + 8) := by
      rw [pow_two]; exact hssR
    exact (div_le_iff₀ hk0).mpr (by linarith)
  have h1 : ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) ≤ (s : ℝ) ^ 2 / (2 * k) := by
    apply div_le_div_of_nonneg_right
    · have : ((s : ℝ) - 13) * ((s : ℝ) - 14) = (s : ℝ) ^ 2 - 27 * s + 182 := by ring
      rw [this]
      nlinarith
    · positivity
  have h2 : (5 / 8) * ((s : ℝ) - 2) ^ 2 / k ≤ (5 / 8) * (s : ℝ) ^ 2 / k := by
    have : ((s : ℝ) - 2) ^ 2 = (s : ℝ) ^ 2 - 4 * s + 4 := by ring
    have hle : ((s : ℝ) - 2) ^ 2 ≤ (s : ℝ) ^ 2 := by
      rw [this]; nlinarith
    have : (5 / 8 : ℝ) * ((s : ℝ) - 2) ^ 2 ≤ (5 / 8) * (s : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hle (by norm_num)
    exact div_le_div_of_nonneg_right this (le_of_lt hk0)
  have h3 : ((s : ℝ) - 2) / k ≤ 1 / 5 := by
    have : (s : ℝ) / k ≤ 1 / 5 := by
      have : (5 : ℝ) * s ≤ k := by exact_mod_cast hs5
      exact (div_le_iff₀ hk0).mpr (by linarith)
    have : ((s : ℝ) - 2) / k ≤ s / k := by
      apply div_le_div_of_nonneg_right
      · linarith
      · positivity
    linarith
  have : (s : ℝ) ^ 2 / (2 * k) + (5 / 8) * (s : ℝ) ^ 2 / k =
      (9 / 8) * (s : ℝ) ^ 2 / k := by
    field_simp [hk0.ne']
    ring
  have hsum : ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
      (5 / 8) * ((s : ℝ) - 2) ^ 2 / k + ((s : ℝ) - 2) / k ≤
      (9 / 8) * (s : ℝ) ^ 2 / k + 1 / 5 := by
    linarith
  have hss' : (9 / 8 : ℝ) * ((s : ℝ) ^ 2 / k) ≤
      (9 / 8) * (3 * Nat.log 2 k + 8 : ℝ) :=
    mul_le_mul_of_nonneg_left hs2k (by norm_num)
  have hrew : (9 / 8 : ℝ) * (s : ℝ) ^ 2 / k = (9 / 8) * ((s : ℝ) ^ 2 / k) := by
    ring
  linarith

lemma leftover_nonpos' (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
        Real.log ((13 : ℕ).factorial : ℝ) +
        ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) -
      ((s - 2 : ℕ) : ℝ) / 2 *
        (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) < 0 := by
  have hexp := leftover_expanded k s hk hs hs5
  have hsim := leftover_simplify k s hk hs
  rw [hsim] at hexp
  have herr := leftover_errors_le k s hk hs hs5 hss
  have hconst := leftover_const_neg k hk
  have hid : (7 : ℝ) / 5 + 23 + 1 / 5 + 9 = (168 : ℝ) / 5 := by norm_num
  have h9 : (9 / 8 : ℝ) * (3 * Nat.log 2 k + 8 : ℝ) =
      (27 / 8) * Nat.log 2 k + 9 := by ring
  have hstep :
      (7 : ℝ) / 5 + 23 - 10 * Real.log k +
          ((s : ℝ) - 13) * ((s : ℝ) - 14) / (2 * k) +
          (5 / 8) * ((s : ℝ) - 2) ^ 2 / k +
          ((s : ℝ) - 2) / k ≤
        (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k := by
    linarith
  have : (168 : ℝ) / 5 + (27 : ℝ) / 8 * Nat.log 2 k - 10 * Real.log k < 0 :=
    hconst
  linarith

lemma leftover_prod (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ))) ≤
      (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^ (((s - 2 : ℕ) : ℝ) / 2) := by
  have hneg := leftover_nonpos' k s hk hs hs5 hss
  have hj : (0 : ℝ) < ((k - s + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 1 by omega)
  have hf : (0 : ℝ) < ((13 : ℕ).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have ham : (0 : ℝ) < (2 * (k : ℝ) + s - 14) / 2 := by
    have : (14 : ℝ) ≤ s := by exact_mod_cast (show 14 ≤ s by omega)
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    linarith
  have hjp : (0 : ℝ) < ((k - s + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - s + 2 by omega)
  have hkm : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hLpos : (0 : ℝ) <
      (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ))) := by
    positivity
  have hRpos : (0 : ℝ) <
      (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^ (((s - 2 : ℕ) : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast (show 0 < (k - s + 2) * (k - 1) by
      apply Nat.mul_pos <;> omega)
  have hlogL :
      Real.log ((4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
          (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)))) =
        Real.log 4 + Real.log ((k - s + 1 : ℕ) : ℝ) +
          Real.log ((13 : ℕ).factorial : ℝ) +
          ((s - 13 : ℕ) : ℝ) * Real.log ((2 * (k : ℝ) + s - 14) / 2) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
  have hlogR :
      Real.log ((((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^
          (((s - 2 : ℕ) : ℝ) / 2)) =
        ((s - 2 : ℕ) : ℝ) / 2 *
          (Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ)) := by
    rw [Real.log_rpow (by exact_mod_cast (show 0 < (k - s + 2) * (k - 1) by
      apply Nat.mul_pos <;> omega))]
    have : Real.log (((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) =
        Real.log ((k - s + 2 : ℕ) : ℝ) + Real.log ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hjp) (ne_of_gt hkm)]
    rw [this]
  have : Real.log ((4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)))) ≤
      Real.log ((((k - s + 2 : ℕ) * (k - 1) : ℕ) : ℝ) ^
        (((s - 2 : ℕ) : ℝ) / 2)) := by
    rw [hlogL, hlogR]
    linarith [hneg]
  exact (Real.log_le_log_iff hLpos hRpos).1 this

lemma largeL_core_real (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
        (prodRange k (s - 13) : ℝ) ≤
      (prodRange (k - s + 2) (s - 2) : ℝ) := by
  have hsk : s + 2 ≤ k := by omega
  have hAM := prodRange_am_le (s - 13) k
  have hpair := prodRange_pair_ge_real (k - s + 2) (s - 2)
    (by omega) (by omega)
  have hend : k - s + 2 + (s - 2) - 1 = k - 1 := by omega
  rw [hend] at hpair
  have ham_eq : (2 * (k : ℝ) + ((s - 13 : ℕ) : ℝ) - 1) / 2 =
      (2 * (k : ℝ) + s - 14) / 2 := by
    have : ((s - 13 : ℕ) : ℝ) = (s : ℝ) - 13 := by
      rw [Nat.cast_sub (by omega : 13 ≤ s)]; norm_num
    rw [this]; ring
  rw [ham_eq] at hAM
  have hprod := leftover_prod k s hk hs hs5 hss
  have hnn1 : (0 : ℝ) ≤ (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) := by
    positivity
  have hAMle : (prodRange k (s - 13) : ℝ) ≤
      ((2 * (k : ℝ) + s - 14) / 2) ^ ((s - 13 : ℕ)) := hAM
  have hmul := mul_le_mul_of_nonneg_left hAMle hnn1
  refine le_trans hmul (le_trans hprod ?_)
  exact hpair

lemma largeL_core_nat (k s : ℕ)
    (hk : 2001 ≤ k) (hs : 45 ≤ s) (hs5 : 5 * s ≤ k)
    (hss : s * s ≤ k * (3 * Nat.log 2 k + 8)) :
    4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) ≤
      prodRange (k - s + 2) (s - 2) := by
  have hR := largeL_core_real k s hk hs hs5 hss
  have hcast :
      ((4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) : ℕ) : ℝ) =
        (4 : ℝ) * ((k - s + 1 : ℕ) : ℝ) * ((13 : ℕ).factorial : ℝ) *
          (prodRange k (s - 13) : ℝ) := by
    push_cast; ring
  have : ((4 * (k - s + 1) * (13 : ℕ).factorial * prodRange k (s - 13) : ℕ) : ℝ) ≤
      (prodRange (k - s + 2) (s - 2) : ℝ) := by
    rwa [hcast]
  exact Nat.cast_le (α := ℝ) |>.mp this
