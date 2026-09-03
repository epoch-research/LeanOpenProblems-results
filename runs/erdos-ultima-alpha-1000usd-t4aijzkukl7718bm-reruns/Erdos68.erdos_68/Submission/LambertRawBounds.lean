import Submission.LambertDifferenceOperators

/-! Uniform bounds for individual uncancelled rows of the raw Lambert
operators. These bounds do not supply nonvanishing of integer forms. -/
namespace LambertRawBounds

open Finset LambertDifferenceOperators

lemma factorial_geometric_mean (k d : ℕ) (hkd : k ≤ d) :
    k.factorial ^ d ≤ d.factorial ^ k := by
  have h₁ := Nat.pow_le_pow_left (Nat.factorial_le_pow k) (d - k)
  have h₂ := Nat.pow_le_pow_left (Nat.factorial_mul_pow_sub_le_factorial hkd) k
  calc
    k.factorial ^ d = k.factorial ^ k * k.factorial ^ (d - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkd]
    _ ≤ k.factorial ^ k * (k ^ k) ^ (d - k) := Nat.mul_le_mul_left _ h₁
    _ = (k.factorial * k ^ (d - k)) ^ k := by
      rw [mul_pow]
      congr 1
      simp only [← pow_mul]
      rw [Nat.mul_comm k (d - k)]
    _ ≤ _ := h₂

lemma factorial_square_lower (d : ℕ) : d ^ d ≤ d.factorial ^ 2 := by
  have hprod : (∏ j ∈ Finset.range d, d) ≤
      ∏ j ∈ Finset.range d, (j + 1) * (d - j) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro j hj
    have hj' : j < d := Finset.mem_range.mp hj
    have hsub : d - j + j = d := Nat.sub_add_cancel (by omega)
    have hmul := Nat.mul_le_mul_left j (show 1 ≤ d - j by omega)
    nlinarith
  have hr : (∏ j ∈ Finset.range d, (d - j)) = d.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one, ← Finset.prod_range_reflect (fun j => j + 1) d]
    apply Finset.prod_congr rfl
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  simpa [Finset.prod_const, Finset.prod_mul_distrib, hr,
    ← Nat.factorial_eq_prod_range_add_one, pow_two] using hprod

noncomputable def rate (d : ℕ) : ℝ := (d.factorial : ℝ) ^ ((d : ℝ)⁻¹)

lemma rate_pos (d : ℕ) : 0 < rate d := by
  unfold rate
  positivity

lemma rate_pow (d : ℕ) (hd : 0 < d) : rate d ^ d = d.factorial :=
  Real.rpow_inv_natCast_pow (by positivity) hd.ne'

lemma one_le_rate (d : ℕ) (hd : 0 < d) : 1 ≤ rate d := by
  apply le_of_pow_le_pow_left₀ hd.ne' (rate_pos d).le
  rw [one_pow, rate_pow d hd]
  exact_mod_cast Nat.factorial_pos d

lemma factorial_le_rate_pow (k d : ℕ) (hd : 0 < d) (hkd : k ≤ d) :
    (k.factorial : ℝ) ≤ rate d ^ k := by
  apply le_of_pow_le_pow_left₀ hd.ne' (pow_nonneg (rate_pos d).le _)
  rw [← pow_mul, Nat.mul_comm k d, pow_mul, rate_pow d hd]
  exact_mod_cast factorial_geometric_mean k d hkd

lemma cast_le_rate_sq (d : ℕ) (hd : 0 < d) : (d : ℝ) ≤ rate d ^ 2 := by
  apply le_of_pow_le_pow_left₀ hd.ne' (pow_nonneg (rate_pos d).le _)
  rw [← pow_mul, Nat.mul_comm 2 d, pow_mul, rate_pow d hd]
  exact_mod_cast factorial_square_lower d

lemma row_le_rate (d n : ℕ) (hd : 2 ≤ d) :
    geometricRowTail d n ≤ 2 / rate d ^ n := by
  have hd0 : 0 < d := by omega
  have ha : (2 : ℝ) ≤ d.factorial := by
    exact_mod_cast (show 2 ≤ d.factorial from by
      simpa using Nat.factorial_le hd)
  have hpow : rate d ^ n ≤ (d.factorial : ℝ) ^ (n / d + 1) := by
    calc
      _ ≤ rate d ^ (d * (n / d + 1)) := by
        apply pow_le_pow_right₀ (one_le_rate d hd0)
        have h₁ := Nat.mod_lt n hd0
        have h₂ := Nat.mod_add_div n d
        rw [Nat.mul_add, Nat.mul_one]
        omega
      _ = _ := by rw [pow_mul, rate_pow d hd0]
  unfold geometricRowTail
  apply (div_le_div_iff₀ (mul_pos (by positivity) (by linarith)) (pow_pos (rate_pos d) n)).mpr
  simp only [one_mul]
  calc
    rate d ^ n ≤ (d.factorial : ℝ) ^ (n / d + 1) := hpow
    _ ≤ 2 * ((d.factorial : ℝ) ^ (n / d) * (d.factorial - 1)) := by
      rw [pow_succ]
      nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg d.factorial) (n / d))
        (show (0 : ℝ) ≤ d.factorial - 2 by linarith)]

noncomputable def rawShift (d : ℕ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  d.factorial * r (n + d) - r n

noncomputable def rawApply : List ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], r => r
  | d :: ds, r => rawApply ds (rawShift d r)

lemma rawShift_bound (d : ℕ) (r : ℕ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hC : 0 ≤ C) (hd : (d.factorial : ℝ) ≤ x ^ d)
    (hr : ∀ n, |r n| ≤ C / x ^ n) (n : ℕ) :
    |rawShift d r n| ≤ 2 * C / x ^ n := by
  unfold rawShift
  calc
    _ ≤ |(d.factorial : ℝ) * r (n + d)| + |r n| := abs_sub _ _
    _ = (d.factorial : ℝ) * |r (n + d)| + |r n| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (d.factorial : ℝ) * (C / x ^ (n + d)) + C / x ^ n := by
      gcongr
      · exact hr (n + d)
      · exact hr n
    _ ≤ x ^ d * (C / x ^ (n + d)) + C / x ^ n := by gcongr
    _ = 2 * C / x ^ n := by
      rw [pow_add]
      field_simp
      ring

lemma rawApply_bound (ds : List ℕ) (r : ℕ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hC : 0 ≤ C)
    (hds : ∀ d ∈ ds, (d.factorial : ℝ) ≤ x ^ d)
    (hr : ∀ n, |r n| ≤ C / x ^ n) (n : ℕ) :
    |rawApply ds r n| ≤ 2 ^ ds.length * C / x ^ n := by
  induction ds generalizing r C with
  | nil => simpa [rawApply] using hr n
  | cons d ds ih =>
    have hb := rawShift_bound d r x C hx hC (hds d (by simp)) hr
    have hi := ih (rawShift d r) (2 * C) (by positivity)
      (fun e he => hds e (by simp [he])) hb
    simpa [rawApply, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hi

/-- A uniform per-row estimate, before summing the uncancelled rows. -/
theorem rawApply_row_bound (ds : List ℕ) (d n : ℕ) (hd : 2 ≤ d)
    (hds : ∀ k ∈ ds, k ≤ d) :
    |rawApply ds (geometricRowTail d) n| ≤ 2 ^ (ds.length + 1) / rate d ^ n := by
  have hr : ∀ n, |geometricRowTail d n| ≤ 2 / rate d ^ n := by
    intro n
    rw [abs_of_nonneg]
    · exact row_le_rate d n hd
    · unfold geometricRowTail
      have hf : (2 : ℝ) ≤ d.factorial := by
        exact_mod_cast (show 2 ≤ d.factorial from by simpa using Nat.factorial_le hd)
      have hfp : (0 : ℝ) < d.factorial - 1 := by linarith
      positivity
  have h := rawApply_bound ds (geometricRowTail d) (rate d) 2 (rate_pos d)
    (by norm_num) (fun k hk => factorial_le_rate_pow k d (by omega) (hds k hk)) hr n
  simpa [pow_succ] using h

/-- An integer-power version avoiding fractional exponents in the bound. -/
theorem rawApply_row_bound_floor (ds : List ℕ) (d n : ℕ) (hd : 2 ≤ d)
    (hds : ∀ k ∈ ds, k ≤ d) :
    |rawApply ds (geometricRowTail d) n| ≤
      2 ^ (ds.length + 1) / (d : ℝ) ^ (n / 2) := by
  have hpow : (d : ℝ) ^ (n / 2) ≤ rate d ^ n := by
    calc
      _ ≤ (rate d ^ 2) ^ (n / 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (cast_le_rate_sq d (by omega)) _
      _ ≤ rate d ^ n := by
        rw [← pow_mul]
        apply pow_le_pow_right₀ (one_le_rate d (by omega))
        omega
  exact (rawApply_row_bound ds d n hd hds).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow)


lemma rawShift_mul_left (d : ℕ) (c : ℝ) (r : ℕ → ℝ) :
    rawShift d (fun n => c * r n) = fun n => c * rawShift d r n := by
  funext n
  simp only [rawShift]
  ring

lemma rawApply_mul_left (ds : List ℕ) (c : ℝ) (r : ℕ → ℝ) :
    rawApply ds (fun n => c * r n) = fun n => c * rawApply ds r n := by
  induction ds generalizing r with
  | nil => rfl
  | cons d ds ih => simp [rawApply, rawShift_mul_left, ih]

lemma rawShift_eq (d : ℕ) (r : ℕ → ℝ) :
    rawShift d r = fun n => (d.factorial : ℝ) * rowShift d r n := by
  funext n
  unfold rawShift rowShift
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma rawApply_eq (ds : List ℕ) (r : ℕ → ℝ) :
    rawApply ds r = fun n =>
      (ds.map (fun d => (d.factorial : ℝ))).prod * applyShifts ds r n := by
  induction ds generalizing r with
  | nil => simp [rawApply, applyShifts]
  | cons d ds ih =>
    rw [rawApply, rawShift_eq, rawApply_mul_left, ih]
    simp only [List.map_cons, List.prod_cons, applyShifts]
    funext n
    ring

theorem rawApply_geometricRowTail_zero (ds : List ℕ) (d : ℕ)
    (hd : 0 < d) (hm : d ∈ ds) :
    rawApply ds (geometricRowTail d) = fun _ => 0 := by
  rw [rawApply_eq, applyShifts_geometricRowTail ds d hd hm]
  simp

end LambertRawBounds

#print axioms LambertRawBounds.factorial_geometric_mean
#print axioms LambertRawBounds.factorial_square_lower
#print axioms LambertRawBounds.rawApply_row_bound
#print axioms LambertRawBounds.rawApply_row_bound_floor

#print axioms LambertRawBounds.rawApply_geometricRowTail_zero
