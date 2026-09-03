import Submission.LambertSharperOperatorBounds

/-! Bounds for the coefficient product of the Lambert row-cancelling operator.
These analytic bounds do not settle the nonvanishing problem. -/

namespace FactorialGeometricProductBound

open Finset LambertRawBounds LambertSharperOperatorBounds

lemma double_pow_le_succ_pow (n : ℕ) (hn : 0 < n) :
    2 * (n : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ n := by
  have h := pow_add_mul_le_add_pow (R := ℝ) (a := (n : ℝ)) (b := 1)
    (by positivity) (by positivity) n
  have he : (n : ℝ) * (n : ℝ) ^ (n - 1) = (n : ℝ) ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  rw [he] at h
  nlinarith

lemma factorial_upper_two (n : ℕ) : (n.factorial : ℝ) ≤ 2 * ((n : ℝ) / 2) ^ n := by
  cases n with
  | zero => norm_num
  | succ n =>
    induction n with
    | zero => norm_num
    | succ n ih =>
      have h := double_pow_le_succ_pow (n + 1) (by omega)
      have hpow : 2 * (((n + 1 : ℕ) : ℝ) / 2) ^ (n + 1) ≤
          ((((n + 1 : ℕ) : ℝ) + 1) / 2) ^ (n + 1) := by
        simpa [div_pow, mul_div_assoc]
          using (div_le_div_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)))
      rw [Nat.factorial_succ, Nat.cast_mul]
      calc
        _ ≤ ((n + 2 : ℕ) : ℝ) * (2 * (((n + 1 : ℕ) : ℝ) / 2) ^ (n + 1)) := by
          gcongr
        _ ≤ ((n + 2 : ℕ) : ℝ) * (((((n + 1 : ℕ) : ℝ) + 1) / 2) ^ (n + 1)) := by
          gcongr
        _ = _ := by push_cast; rw [pow_succ]; ring

lemma factorial_upper_half (n : ℕ) (hn : 6 ≤ n) :
    (n.factorial : ℝ) ≤ ((n : ℝ) / 2) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h := double_pow_le_succ_pow n (by omega)
    have hpow : 2 * ((n : ℝ) / 2) ^ n ≤ (((n : ℝ) + 1) / 2) ^ n := by
      simpa [div_pow, mul_div_assoc] using
        (div_le_div_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 ^ n))
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ ((n : ℝ) + 1) / 2 by positivity)]

lemma rate_upper_half (d : ℕ) (hd : 6 ≤ d) : rate d ≤ (d : ℝ) / 2 := by
  apply le_of_pow_le_pow_left₀ (show d ≠ 0 by omega) (by positivity)
  rw [rate_pow d (by omega)]
  exact factorial_upper_half d hd

/-- Pairing the factors of an ascending factorial gives a lower bound
by the product of its two endpoints. -/
lemma ascFactorial_square_lower (k m : ℕ) :
    ((k + 1) * (k + m)) ^ m ≤ ((k + 1).ascFactorial m) ^ 2 := by
  have hprod : (∏ j ∈ Finset.range m, (k + 1) * (k + m)) ≤
      ∏ j ∈ Finset.range m, (k + j + 1) * (k + m - j) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro j hj
    have hj' : j < m := Finset.mem_range.mp hj
    have hsub : k + m - j + j = k + m := Nat.sub_add_cancel (by omega)
    have hmul := Nat.zero_le (j * (m - j - 1))
    have hx : m - j - 1 + j + 1 = m := by omega
    nlinarith
  have hf : (∏ j ∈ Finset.range m, (k + j + 1)) = (k + 1).ascFactorial m := by
    rw [Nat.ascFactorial_eq_prod_range]
    congr 1
    ext j
    omega
  have hr : (∏ j ∈ Finset.range m, (k + m - j)) = (k + 1).ascFactorial m := by
    rw [← hf, ← Finset.prod_range_reflect (fun j => k + j + 1) m]
    apply Finset.prod_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  simpa [Finset.prod_const, Finset.prod_mul_distrib, hf, hr, pow_two] using hprod



lemma normalized_factorial_lower_half (d k : ℕ) (hd : 0 < d) (hk : 2*k ≤ d) :
    (k.factorial : ℝ) / rate d ^ k ≤ 2 * (3 / 4 : ℝ) ^ k := by
  have hbase : (k : ℝ) / 2 ≤ (3 / 4 : ℝ) * rate d := by
    have h := rate_lower_third d hd
    have hkR : 2 * (k : ℝ) ≤ d := by exact_mod_cast hk
    nlinarith
  apply (div_le_iff₀ (pow_pos (rate_pos d) k)).mpr
  calc
    (k.factorial : ℝ) ≤ 2 * ((k : ℝ) / 2) ^ k := factorial_upper_two k
    _ ≤ 2 * ((3 / 4 : ℝ) * rate d) ^ k := by gcongr
    _ = _ := by rw [mul_pow]; ring

lemma normalized_factorial_upper_half (d k : ℕ) (hd : 6 ≤ d)
    (hlo : d ≤ 2*k) (hhi : k ≤ d) :
    (k.factorial : ℝ) / rate d ^ k ≤ (3 / 4 : ℝ) ^ (d-k) := by
  let m := d-k
  let a : ℝ := (k+1).ascFactorial m
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast Nat.ascFactorial_pos k m
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hloR : (d : ℝ) ≤ 2 * k := by exact_mod_cast hlo
  have hu := rate_upper_half d hd
  have hsq : rate d ^ 2 ≤ (3 / 4 : ℝ) ^ 2 * ((k+1) * (d : ℝ)) := by
    have hu2 : rate d ^ 2 ≤ ((d : ℝ) / 2) ^ 2 :=
      pow_le_pow_left₀ (rate_pos d).le hu 2
    have hmul := mul_le_mul_of_nonneg_right hloR hdR.le
    nlinarith
  have hasq : (((k : ℝ)+1) * (d : ℝ)) ^ m ≤ a ^ 2 := by
    have hh := ascFactorial_square_lower k m
    have he : k+m=d := Nat.add_sub_of_le hhi
    rw [he] at hh
    dsimp [a]
    exact_mod_cast hh
  have hp : (rate d ^ m) ^ 2 ≤ ((3 / 4 : ℝ) ^ m * a) ^ 2 := by
    calc
      _ = (rate d ^ 2) ^ m := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ ((3 / 4 : ℝ) ^ 2 * (((k : ℝ)+1) * (d : ℝ))) ^ m :=
        pow_le_pow_left₀ (sq_nonneg _) hsq m
      _ = ((3 / 4 : ℝ) ^ m) ^ 2 * ((((k : ℝ)+1) * (d : ℝ)) ^ m) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; congr 1; congr 1; omega
      _ ≤ ((3 / 4 : ℝ) ^ m) ^ 2 * a ^ 2 := by gcongr
      _ = _ := by rw [mul_pow]
  have hroot : rate d ^ m ≤ (3 / 4 : ℝ) ^ m * a :=
    (sq_le_sq₀ (pow_nonneg (rate_pos d).le m) (by positivity)).mp hp
  have hid : (k.factorial : ℝ) / rate d ^ k = rate d ^ m / a := by
    apply (div_eq_div_iff (pow_pos (rate_pos d) k).ne' ha.ne').mpr
    rw [← pow_add, Nat.add_comm m k, Nat.add_sub_of_le hhi, rate_pow d (by omega)]
    dsimp [a]
    have he := Nat.factorial_mul_ascFactorial k m
    rw [show k+m=d from Nat.add_sub_of_le hhi] at he
    exact_mod_cast he
  rw [hid]
  exact (div_le_iff₀ ha).mpr hroot

lemma geometric_sum_le_four (N : ℕ) :
    (∑ k ∈ Finset.range N, (3 / 4 : ℝ) ^ k) ≤ 4 := by
  have h := geom_sum_mul_neg (3 / 4 : ℝ) N
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) N]

/-- The complete normalized factorial sum is bounded independently of d. -/
theorem normalized_factorial_sum_le_twelve (d : ℕ) (hd : 6 ≤ d) :
    (∑ k ∈ Finset.range (d+1), (k.factorial : ℝ) / rate d ^ k) ≤ 12 := by
  have hp := rate_pos d
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d+1)) :
      (k.factorial : ℝ) / rate d ^ k ≤
        2 * (3/4 : ℝ) ^ k + (3/4 : ℝ) ^ (d-k) := by
    have hkd : k ≤ d := by simpa using Finset.mem_range.mp hk
    by_cases hh : 2*k ≤ d
    · have h := normalized_factorial_lower_half d k (by omega) hh
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) (d-k)]
    · have h := normalized_factorial_upper_half d k hd (by omega) hkd
      linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/4) k]
  have hsum := Finset.sum_le_sum hterm
  have hrev : (∑ k ∈ Finset.range (d+1), (3/4 : ℝ) ^ (d-k)) =
      ∑ k ∈ Finset.range (d+1), (3/4 : ℝ) ^ k := by
    simpa using Finset.sum_range_reflect (fun k => (3/4 : ℝ) ^ k) (d+1)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hrev] at hsum
  linarith [geometric_sum_le_four (d+1)]

/-- Unlike the earlier bound 2^K, this bound is independent of the
number of cancelled rows. -/
theorem weightedProduct_range_le_exp_twelve (K d : ℕ) (hd : 6 ≤ d)
    (hKd : K+1 ≤ d) :
    weightedProduct (List.range' 2 K) (rate d) ≤ Real.exp 12 := by
  let s := (List.range' 2 K).toFinset
  have hp := rate_pos d
  have hsub : s ⊆ Finset.range (d+1) := by
    intro k hk
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp (List.mem_toFinset.mp hk)
    apply Finset.mem_range.mpr
    omega
  have hsum : (∑ k ∈ s, (k.factorial : ℝ) / rate d ^ k) ≤ 12 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity))
    exact normalized_factorial_sum_le_twelve d hd
  have heq : weightedProduct (List.range' 2 K) (rate d) =
      ∏ k ∈ s, (1 + (k.factorial : ℝ) / rate d ^ k) := by
    symm
    exact List.prod_toFinset _ List.nodup_range'
  rw [heq]
  calc
    _ ≤ ∏ k ∈ s, Real.exp ((k.factorial : ℝ) / rate d ^ k) := by
      apply Finset.prod_le_prod (by intros; positivity)
      intro k _
      simpa [add_comm] using Real.add_one_le_exp ((k.factorial : ℝ) / rate d ^ k)
    _ = Real.exp (∑ k ∈ s, (k.factorial : ℝ) / rate d ^ k) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 12 := Real.exp_le_exp.mpr hsum

open Erdos68Development LambertDifferenceOperators LambertTotalBounds

/-- Uniform operator prefactor for each uncancelled row. -/
theorem rawApply_row_uniform_bound (K d n : ℕ) (hd : 6 ≤ d) (hKd : K+1 ≤ d) :
    |rawApply (List.range' 2 K) (geometricRowTail d) n| ≤
      2 * Real.exp 12 / rate d ^ n := by
  have hp := rate_pos d
  calc
    _ ≤ 2 * weightedProduct (List.range' 2 K) (rate d) / rate d ^ n :=
      rawApply_row_weighted_bound _ d n (by omega)
    _ ≤ _ := by
      gcongr
      exact weightedProduct_range_le_exp_twelve K d hd hKd

/-- Stirling's bound gives the full exponent n with the same uniform prefactor. -/
theorem rawApply_row_uniform_exp_bound (K d n : ℕ) (hd : 6 ≤ d) (hKd : K+1 ≤ d) :
    |rawApply (List.range' 2 K) (geometricRowTail d) n| ≤
      (2 * Real.exp 12 * (Real.exp 1) ^ n) / (d : ℝ) ^ n := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : ((d : ℝ) / Real.exp 1) ^ n ≤ rate d ^ n :=
    pow_le_pow_left₀ (by positivity) (rate_lower_exp d (by omega)) n
  calc
    _ ≤ 2 * Real.exp 12 / rate d ^ n := rawApply_row_uniform_bound K d n hd hKd
    _ ≤ 2 * Real.exp 12 / ((d : ℝ) / Real.exp 1) ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by rw [div_pow]; field_simp

/-- An absolute operator constant, independent of K, in the total error bound.
This still does not assert that the error is nonzero. -/
theorem range_operator_uniform_bound (K n : ℕ) (hK : 4 ≤ K) (hn : 2 ≤ n) :
    |rawApply (List.range' 2 K)
      (fun n => (∑' k : ℕ, term k) - (prefixQ n : ℝ)) n| ≤
      (2 * Real.exp 12 * (Real.exp 1) ^ n) / ((K+1 : ℕ) : ℝ) ^ (n-1) := by
  have hc : ∀ k < K, k + 2 ∈ List.range' 2 K := by
    intro k hk
    exact List.mem_range'.mpr ⟨k, hk, by omega⟩
  rw [cutoff_tail_rows _ K n hc]
  let C := 2 * Real.exp 12 * (Real.exp 1) ^ n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := summable_bound C K n (by omega)
  have h := tsum_of_norm_bounded
    (f := fun k => rawApply (List.range' 2 K) (geometricRowTail (k+K+2)) n)
    hs.hasSum (fun k => by
      simpa only [Real.norm_eq_abs] using
        rawApply_row_uniform_exp_bound K (k+K+2) n (by omega) (by omega))
  calc
    _ ≤ ∑' k : ℕ, C / ((k+K+2 : ℕ) : ℝ) ^ n := by
      simpa only [Real.norm_eq_abs] using h
    _ = C * (∑' k : ℕ, 1 / ((k+K+2 : ℕ) : ℝ) ^ n) := by
      simp only [div_eq_mul_inv, one_mul, tsum_mul_left]
    _ ≤ C * (1 / ((K+1 : ℕ) : ℝ) ^ (n-1)) :=
      mul_le_mul_of_nonneg_left (pseries_tail_bound K n hn) hC
    _ = _ := by dsimp [C]; ring


end FactorialGeometricProductBound
#print axioms FactorialGeometricProductBound.normalized_factorial_sum_le_twelve
#print axioms FactorialGeometricProductBound.weightedProduct_range_le_exp_twelve
#print axioms FactorialGeometricProductBound.range_operator_uniform_bound
