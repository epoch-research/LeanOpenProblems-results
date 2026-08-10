import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

lemma a_mod_p (n j p : ℕ) (hp : p ∣ 11184810) : (a n * 2^j + 1) % p = (9454129 * 2^j + 1) % p := by
  dsimp [a]
  rcases hp with ⟨c, hc⟩
  have h_sub : 11184810 * n = p * (c * n) := by
    rw [hc]
    ring
  have h1 : (9454129 + 11184810 * n) * 2^j + 1 = (9454129 * 2^j + 1) + p * (c * n * 2^j) := by
    rw [h_sub]
    ring
  rw [h1]
  rw [Nat.add_mul_mod_self_left]

lemma b_mod_p (n j p : ℕ) (hp : p ∣ 11184810) : ((a n + 28) * 2^j + 1) % p = (9454157 * 2^j + 1) % p := by
  dsimp [a]
  rcases hp with ⟨c, hc⟩
  have h_sub : 11184810 * n = p * (c * n) := by
    rw [hc]
    ring
  have h1 : (9454129 + 11184810 * n + 28) * 2^j + 1 = (9454157 * 2^j + 1) + p * (c * n * 2^j) := by
    rw [h_sub]
    ring
  rw [h1]
  rw [Nat.add_mul_mod_self_left]

lemma pow_mod_step (q r p : ℕ) (h : 2^24 % p = 1) : 2^(24 * q + r) % p = 2^r % p := by
  induction q with
  | zero =>
    have h0 : 24 * 0 + r = r := by omega
    rw [h0]
  | succ q ih =>
    have h1 : 2^(24 * (q + 1) + r) = 2^24 * 2^(24 * q + r) := by
      ring_nf
    rw [h1]
    rw [Nat.mul_mod]
    rw [h]
    rw [Nat.one_mul]
    rw [Nat.mod_mod]
    exact ih

lemma pow_mod_24 (j p : ℕ) (h : 2^24 % p = 1) : 2^j % p = 2^(j % 24) % p := by
  have h_eq : j = 24 * (j / 24) + j % 24 := by omega
  nth_rw 1 [h_eq]
  exact pow_mod_step (j / 24) (j % 24) p h

lemma mul_add_one_mod (A B p : ℕ) : (A * B + 1) % p = (A * (B % p) + 1) % p := by
  have h_eq : A * B + 1 = A * (p * (B / p) + B % p) + 1 := by
    congr 2
    exact (Nat.div_add_mod B p).symm
  rw [h_eq]
  have h_exp : A * (p * (B / p) + B % p) + 1 = (A * (B % p) + 1) + p * (A * (B / p)) := by
    ring
  rw [h_exp]
  rw [Nat.add_mul_mod_self_left]

lemma a_mod_p_combined (n j p : ℕ) (hp_dvd : p ∣ 11184810) (hp_pow : 2^24 % p = 1) :
  (a n * 2^j + 1) % p = (9454129 * 2^(j % 24) + 1) % p := by
  rw [a_mod_p n j p hp_dvd]
  rw [mul_add_one_mod 9454129 (2^j) p]
  rw [pow_mod_24 j p hp_pow]
  rw [← mul_add_one_mod 9454129 (2^(j % 24)) p]

lemma b_mod_p_combined (n j p : ℕ) (hp_dvd : p ∣ 11184810) (hp_pow : 2^24 % p = 1) :
  ((a n + 28) * 2^j + 1) % p = (9454157 * 2^(j % 24) + 1) % p := by
  rw [b_mod_p n j p hp_dvd]
  rw [mul_add_one_mod 9454157 (2^j) p]
  rw [pow_mod_24 j p hp_pow]
  rw [← mul_add_one_mod 9454157 (2^(j % 24)) p]

lemma a_gt_p (n j p : ℕ) (hj : j > 0) (hp : p ≤ 241) : p < a n * 2^j + 1 := by
  dsimp [a]
  have h2 : 2^j ≥ 2 := by
    have h_pow : 2^j ≥ 2^1 := Nat.pow_le_pow_right (by decide) hj
    exact h_pow
  have h_prod : (9454129 + 11184810 * n) * 2^j ≥ 9454129 * 2 := by
    have h_left : 9454129 ≤ 9454129 + 11184810 * n := by omega
    gcongr
  omega

lemma b_gt_p (n j p : ℕ) (hj : j > 0) (hp : p ≤ 241) : p < (a n + 28) * 2^j + 1 := by
  dsimp [a]
  have h2 : 2^j ≥ 2 := by
    have h_pow : 2^j ≥ 2^1 := Nat.pow_le_pow_right (by decide) hj
    exact h_pow
  have h_prod : (9454129 + 11184810 * n + 28) * 2^j ≥ 9454129 * 2 := by
    have h_left : 9454129 ≤ 9454129 + 11184810 * n + 28 := by omega
    gcongr
  omega

lemma is_sierpinski_number_a (n : ℕ) : is_sierpinski_number (a n) := by
  dsimp [is_sierpinski_number]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [a]
    omega
  · dsimp [a]
    omega
  · intro j hj
    have h_lt : j % 24 < 24 := Nat.mod_lt j (by decide)
    generalize hr : j % 24 = r
    rw [hr] at h_lt
    interval_cases r
    · -- case r = 0
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 1
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 2
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 17 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 17 hj (by decide)
    · -- case r = 3
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 4
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 5
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 6
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 7 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 7 hj (by decide)
    · -- case r = 7
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 8
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 9
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 10
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 13 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 13 hj (by decide)
    · -- case r = 11
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 12
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 13
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 14
      apply Nat.not_prime_of_dvd_of_lt (m := 241)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 241 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 241 hj (by decide)
    · -- case r = 15
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 16
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 17
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 18
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 7 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 7 hj (by decide)
    · -- case r = 19
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 20
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 5 hj (by decide)
    · -- case r = 21
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
    · -- case r = 22
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 13 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 13 hj (by decide)
    · -- case r = 23
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [a_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact a_gt_p n j 3 hj (by decide)
lemma is_sierpinski_number_b (n : ℕ) : is_sierpinski_number (a n + 28) := by
  dsimp [is_sierpinski_number]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [a]
    omega
  · dsimp [a]
    omega
  · intro j hj
    have h_lt : j % 24 < 24 := Nat.mod_lt j (by decide)
    generalize hr : j % 24 = r
    rw [hr] at h_lt
    interval_cases r
    · -- case r = 0
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 1
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 2
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 3
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 7 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 7 hj (by decide)
    · -- case r = 4
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 5
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 6
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 7
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 17 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 17 hj (by decide)
    · -- case r = 8
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 9
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 10
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 11
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 13 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 13 hj (by decide)
    · -- case r = 12
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 13
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 14
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 15
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 17 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 17 hj (by decide)
    · -- case r = 16
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 17
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 18
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 19
      apply Nat.not_prime_of_dvd_of_lt (m := 241)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 241 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 241 hj (by decide)
    · -- case r = 20
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 21
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 5 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 5 hj (by decide)
    · -- case r = 22
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 3 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 3 hj (by decide)
    · -- case r = 23
      apply Nat.not_prime_of_dvd_of_lt (m := 13)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [b_mod_p_combined n j 13 (by decide) (by decide)]
        rw [hr]
        rfl
      · decide
      · exact b_gt_p n j 13 hj (by decide)

lemma pow_mod_step_general (D : ℕ) (q r p : ℕ) (h : 2^D % p = 1) : 2^(D * q + r) % p = 2^r % p := by
  induction q with
  | zero =>
    have h0 : D * 0 + r = r := by omega
    rw [h0]
  | succ q ih =>
    have h1 : 2^(D * (q + 1) + r) = 2^D * 2^(D * q + r) := by
      ring_nf
    rw [h1]
    rw [Nat.mul_mod]
    rw [h]
    rw [Nat.one_mul]
    rw [Nat.mod_mod]
    exact ih

lemma pow_mod_48 (j p : ℕ) (h : 2^48 % p = 1) : 2^j % p = 2^(j % 48) % p := by
  have h_eq : j = 48 * (j / 48) + j % 48 := by omega
  nth_rw 1 [h_eq]
  exact pow_mod_step_general 48 (j / 48) (j % 48) p h

lemma k_mod_p_combined (j p : ℕ) (hp_pow : 2^48 % p = 1) :
  (5292270077783 * 2^j + 1) % p = (5292270077783 * 2^(j % 48) + 1) % p := by
  rw [mul_add_one_mod 5292270077783 (2^j) p]
  rw [pow_mod_48 j p hp_pow]
  rw [← mul_add_one_mod 5292270077783 (2^(j % 48)) p]

lemma k_gt_p (j p : ℕ) (hj : j > 0) (hp : p ≤ 673) : p < 5292270077783 * 2^j + 1 := by
  have h2 : 2^j ≥ 2 := by
    have h_pow : 2^j ≥ 2^1 := Nat.pow_le_pow_right (by decide) hj
    exact h_pow
  have h_prod : 5292270077783 * 2^j ≥ 5292270077783 * 2 := Nat.mul_le_mul_left 5292270077783 h2
  omega

lemma is_sierpinski_number_k : is_sierpinski_number 5292270077783 := by
  dsimp [is_sierpinski_number]
  refine ⟨rfl, by decide, ?_⟩
  · intro j hj
    have h_lt : j % 48 < 48 := Nat.mod_lt j (by decide)
    generalize hr : j % 48 = r
    rw [hr] at h_lt
    interval_cases r
    · -- case r = 0
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 1
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 7 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 7 hj (by decide)
    · -- case r = 2
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 3
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 4
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 5
      apply Nat.not_prime_of_dvd_of_lt (m := 257)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 257 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 257 hj (by decide)
    · -- case r = 6
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 7
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 8
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 9
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 17 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 17 hj (by decide)
    · -- case r = 10
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 11
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 12
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 13
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 7 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 7 hj (by decide)
    · -- case r = 14
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 15
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 16
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 17
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 17 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 17 hj (by decide)
    · -- case r = 18
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 19
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 20
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 21
      apply Nat.not_prime_of_dvd_of_lt (m := 257)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 257 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 257 hj (by decide)
    · -- case r = 22
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 23
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 24
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 25
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 7 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 7 hj (by decide)
    · -- case r = 26
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 27
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 28
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 29
      apply Nat.not_prime_of_dvd_of_lt (m := 97)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 97 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 97 hj (by decide)
    · -- case r = 30
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 31
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 32
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 33
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 17 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 17 hj (by decide)
    · -- case r = 34
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 35
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 36
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 37
      apply Nat.not_prime_of_dvd_of_lt (m := 7)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 7 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 7 hj (by decide)
    · -- case r = 38
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 39
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 40
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 41
      apply Nat.not_prime_of_dvd_of_lt (m := 17)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 17 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 17 hj (by decide)
    · -- case r = 42
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 43
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)
    · -- case r = 44
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 45
      apply Nat.not_prime_of_dvd_of_lt (m := 673)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 673 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 673 hj (by decide)
    · -- case r = 46
      apply Nat.not_prime_of_dvd_of_lt (m := 3)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 3 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 3 hj (by decide)
    · -- case r = 47
      apply Nat.not_prime_of_dvd_of_lt (m := 5)
      · rw [Nat.dvd_iff_mod_eq_zero]
        rw [k_mod_p_combined j 5 (by decide)]
        rw [hr]
        rfl
      · decide
      · exact k_gt_p j 5 hj (by decide)

/--
oeis_270994_conjecture_0.disproof: Disproof of the conjecture.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have h_spec := h 473165
  rcases h_spec with ⟨_, _, h_gap⟩
  have h_false := h_gap 5292270077783 is_sierpinski_number_k (by decide) (by decide)
  exact h_false

