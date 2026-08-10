import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

lemma dvd_pow_of_pos {a b : ℕ} (h : a ∣ b) {c : ℕ} (hc : c > 0) : a ∣ b ^ c := by
  cases c with
  | zero => omega
  | succ c =>
    rw [pow_succ]
    exact dvd_mul_of_dvd_right h _

lemma a_split (n : ℕ) (hn : n ≥ 2) :
    a n = (1) ^ (n.factorial) + 2 ^ ((n - 1).factorial) +
      Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) := by
  have h_eq : n = (n - 2) + 2 := by omega
  have h_sub1 : n - 2 + 2 - 1 = n - 1 := by omega
  have h_sum : (∑ k ∈ Finset.range (n - 2), (k + 1 + 1 + 1)! ^ (n - 2 + 2 - (k + 1 + 1))!) = (∑ i ∈ Finset.range (n - 2), (i + 3)! ^ (n - i - 2)!) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega
  unfold a
  conv_lhs => rw [h_eq]
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  rw [h_sub1]
  rw [h_sum]
  have h2 : (0 + 1 + 1).factorial = 2 := rfl
  have h1 : (0 + 1).factorial = 1 := rfl
  have h0 : n - 2 + 2 - 0 = n := by omega
  rw [h2, h1, h0]
  ring

lemma a_mod_256 (n : ℕ) : a (n + 11) % 256 = 1 := by
  have h_split_eq : a (n + 11) = 1 + 2 ^ (n + 10).factorial + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) := by
    have h_split_a := a_split (n + 11) (by omega)
    have h_sub1 : n + 11 - 1 = n + 10 := by omega
    have h_sub2 : n + 11 - 2 = n + 9 := by omega
    have h_sum_eq : (∑ i ∈ Finset.range (n + 11 - 2), (i + 3)! ^ (n + 11 - i - 2)!) = (∑ i ∈ Finset.range (n + 9), (i + 3)! ^ (n + 9 - i)!) := by
      rw [h_sub2]
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      omega
    rw [h_split_a, h_sub1, h_sum_eq]
    have h_one_pow : 1 ^ (n + 11).factorial = 1 := Nat.one_pow _
    rw [h_one_pow]
  rw [h_split_eq]
  have h_two : 2 ^ (n + 10).factorial % 256 = 0 := by
    have h_ge : (n + 10).factorial ≥ 8 := by
      have : n + 10 ≥ 10 := by omega
      have h_fac := Nat.factorial_le this
      have h_fac3628800 : Nat.factorial 10 = 3628800 := rfl
      rw [h_fac3628800] at h_fac
      omega
    have h_pow : 2 ^ (n + 10).factorial = 256 * 2 ^ ((n + 10).factorial - 8) := by
      have : (n + 10).factorial = 8 + ((n + 10).factorial - 8) := by omega
      conv_lhs => rw [this]
      rw [pow_add]
      rfl
    rw [h_pow]
    simp only [Nat.mul_mod_right]
  have h_sum : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) % 256 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro i hi
    have hi_lt : i < n + 9 := Finset.mem_range.mp hi
    by_cases h_cases : i < n + 7
    · by_cases hi_zero : i = 0
      · rw [hi_zero]
        simp only [zero_add]
        have h_fac3 : Nat.factorial 3 = 6 := rfl
        rw [h_fac3]
        have hm : (n + 9).factorial ≥ 8 := by
          have : n + 9 ≥ 9 := by omega
          have h_sub := Nat.factorial_le this
          have h_fac362880 : Nat.factorial 9 = 362880 := rfl
          rw [h_fac362880] at h_sub
          omega
        have h_div : 256 ∣ 6 ^ (n + 9).factorial := by
          have : (n + 9).factorial = 8 + ((n + 9).factorial - 8) := by omega
          rw [this, pow_add]
          have h_6_pow8 : 6 ^ 8 = 256 * 6561 := by rfl
          rw [h_6_pow8]
          exact dvd_mul_of_dvd_left (dvd_mul_right 256 6561) _
        exact h_div
      · have h_even : 8 ∣ (i + 3).factorial := by
          have : i + 3 ≥ 4 := by omega
          have h_dvd := Nat.factorial_dvd_factorial this
          have h_fac24 : Nat.factorial 4 = 24 := rfl
          rw [h_fac24] at h_dvd
          exact dvd_trans (by decide) h_dvd
        obtain ⟨k, hk⟩ := h_even
        rw [hk, mul_pow]
        have hm : (n + 9 - i).factorial ≥ 6 := by
          have : n + 9 - i ≥ 3 := by omega
          have h_sub := Nat.factorial_le this
          have h_fac6 : Nat.factorial 3 = 6 := rfl
          rw [h_fac6] at h_sub
          exact h_sub
        have h_div : 256 ∣ 8 ^ (n + 9 - i).factorial := by
          have : (n + 9 - i).factorial = 3 + ((n + 9 - i).factorial - 3) := by omega
          rw [this, pow_add]
          have : 8 ^ 3 = 256 * 2 := rfl
          rw [this]
          exact dvd_mul_of_dvd_left (dvd_mul_right 256 2) _
        exact dvd_mul_of_dvd_left h_div _
    · have hi_eq : i = n + 7 ∨ i = n + 8 := by omega
      rcases hi_eq with rfl | rfl
      · have h_sub : n + 9 - (n + 7) = 2 := by omega
        have h_sub_fact : (n + 9 - (n + 7)).factorial = 2 := by rw [h_sub]; rfl
        rw [h_sub_fact]
        simp only [pow_two]
        have h_sub2 : n + 7 + 3 = n + 10 := by omega
        have h_dvd : 16 ∣ (n + 10).factorial := by
          have : n + 10 ≥ 10 := by omega
          have h_dvd := Nat.factorial_dvd_factorial this
          have : 16 ∣ Nat.factorial 10 := by decide
          exact dvd_trans this h_dvd
        obtain ⟨k, hk⟩ := h_dvd
        rw [h_sub2, hk]
        have : (16 * k) * (16 * k) = 256 * (k * k) := by ring
        rw [this]
        exact dvd_mul_right 256 _
      · have h_sub : n + 9 - (n + 8) = 1 := by omega
        have h_sub_fact : (n + 9 - (n + 8)).factorial = 1 := by rw [h_sub]; rfl
        rw [h_sub_fact]
        simp only [pow_one]
        have h_sub3 : n + 8 + 3 = n + 11 := by omega
        have h_term_eq : (n + 8 + 3).factorial = (n + 11).factorial := by rw [h_sub3]
        rw [h_term_eq]
        have h_dvd5 : 256 ∣ Nat.factorial 11 := by decide
        have h_dvdn : Nat.factorial 11 ∣ (n + 11).factorial := Nat.factorial_dvd_factorial (by omega)
        exact dvd_trans h_dvd5 h_dvdn
  rw [Nat.add_mod, h_sum]
  simp only [add_zero, Nat.mod_mod]
  rw [Nat.add_mod 1 (2 ^ (n + 10).factorial)]
  rw [h_two]

lemma mod_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 128 = 1 ∧ X % 64 = 1 := by
  have h_eq : X = 256 * (X / 256) + 1 := by
    have := Nat.div_add_mod X 256
    omega
  constructor
  · rw [h_eq]
    have : 256 * (X / 256) + 1 = 1 + 128 * (2 * (X / 256)) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · rw [h_eq]
    have : 256 * (X / 256) + 1 = 1 + 64 * (4 * (X / 256)) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma mod_32_of_mod_256 {X : ℕ} (h : X % 256 = 1) : X % 32 = 1 := by
  have h_eq : X = 256 * (X / 256) + 1 := by
    have := Nat.div_add_mod X 256
    omega
  rw [h_eq]
  have : 256 * (X / 256) + 1 = 1 + 32 * (8 * (X / 256)) := by ring
  rw [this]
  rw [Nat.add_mul_mod_self_left]

lemma mod_128_of_mod_480_eq_449 {B : ℕ} (h : B % 480 = 449) : B % 128 = 33 ∨ B % 128 = 65 := by
  have : B = 480 * (B / 480) + B % 480 := (Nat.div_add_mod B 480).symm
  rw [h] at this
  rw [this]
  have h_mod : B / 480 % 4 = 0 ∨ B / 480 % 4 = 1 ∨ B / 480 % 4 = 2 ∨ B / 480 % 4 = 3 := by omega
  rcases h_mod with h0 | h1 | h2 | h3
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    rw [hk]
    right
    have : 480 * (4 * k) + 449 = 65 + 128 * (15 * k + 3) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 4 * k + 1 := ⟨B / 480 / 4, by omega⟩
    rw [hk]
    left
    have : 480 * (4 * k + 1) + 449 = 33 + 128 * (15 * k + 7) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 4 * k + 2 := ⟨B / 480 / 4, by omega⟩
    rw [hk]
    right
    have : 480 * (4 * k + 2) + 449 = 65 + 128 * (15 * k + 10) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  · obtain ⟨k, hk⟩ : ∃ k, B / 480 = 4 * k + 3 := ⟨B / 480 / 4, by omega⟩
    rw [hk]
    left
    have : 480 * (4 * k + 3) + 449 = 33 + 128 * (15 * k + 14) := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]

lemma thirty_three_pow_odd (k : ℕ) : 33 ^ (2 * k + 1) % 64 = 33 := by
  have h_pow : 33 ^ (2 * k + 1) = 33 * 1089 ^ k := by
    rw [pow_succ, mul_comm]
    congr 1
    have : 33 ^ 2 = 1089 := rfl
    rw [pow_mul, this]
  rw [h_pow]
  have h_pow2 : 1089 ^ k % 64 = 1 := by
    have : 1089 ^ k % 64 = (1089 % 64) ^ k % 64 := Nat.pow_mod 1089 k 64
    have h_mod : 1089 % 64 = 1 := rfl
    rw [h_mod] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2]

lemma B_pow_mod_64_eq_33 (B p : ℕ) (hB : B % 64 = 33) (hp_odd : p % 2 = 1) : B ^ p % 64 = 33 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  have h_mod : B ^ (2 * k + 1) % 64 = (B % 64) ^ (2 * k + 1) % 64 := Nat.pow_mod B (2 * k + 1) 64
  rw [hB] at h_mod
  rw [h_mod]
  exact thirty_three_pow_odd k

lemma sixty_five_pow_odd (k : ℕ) : 65 ^ (2 * k + 1) % 128 = 65 := by
  have h_pow : 65 ^ (2 * k + 1) = 65 * 4225 ^ k := by
    rw [pow_succ, mul_comm]
    congr 1
    have : 65 ^ 2 = 4225 := rfl
    rw [pow_mul, this]
  rw [h_pow]
  have h_pow2 : 4225 ^ k % 128 = 1 := by
    have : 4225 ^ k % 128 = (4225 % 128) ^ k % 128 := Nat.pow_mod 4225 k 128
    have h_mod : 4225 % 128 = 1 := rfl
    rw [h_mod] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2]

lemma B_pow_mod_128_eq_65 (B p : ℕ) (hB : B % 128 = 65) (hp_odd : p % 2 = 1) : B ^ p % 128 = 65 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk]
  have h_mod : B ^ (2 * k + 1) % 128 = (B % 128) ^ (2 * k + 1) % 128 := Nat.pow_mod B (2 * k + 1) 128
  rw [hB] at h_mod
  rw [h_mod]
  exact sixty_five_pow_odd k

lemma chinese_remainder_helper (r : ℕ) (h3 : r % 3 = 2) (h5 : r % 5 = 4) (h16 : r % 16 = 1) (h_lt : r < 480) : r % 32 = 17 ∨ r = 449 := by
  obtain ⟨k, hk⟩ : ∃ k, r = 16 * k + 1 := ⟨r / 16, by omega⟩
  have h_k_lt : k < 30 := by omega
  revert h_k_lt h3 h5 h16
  rcases k with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k
  all_goals (try rw [hk])
  all_goals (try decide)
  all_goals (try intro h_k_lt h3 h5 h16)
  all_goals (try exfalso)
  all_goals (try omega)

lemma chinese_remainder_X (X : ℕ) (h3 : X % 3 = 2) (h5 : X % 5 = 4) (h16 : X % 16 = 1) : X % 32 = 17 ∨ X % 480 = 449 := by
  have h_eq : X = 480 * (X / 480) + X % 480 := (Nat.div_add_mod X 480).symm
  have h3_r : X % 480 % 3 = 2 := by
    have : (480 * (X / 480) + X % 480) % 3 = X % 480 % 3 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 3 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 3 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h3
  have h5_r : X % 480 % 5 = 4 := by
    have : (480 * (X / 480) + X % 480) % 5 = X % 480 % 5 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 5 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 5 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h5
  have h16_r : X % 480 % 16 = 1 := by
    have : (480 * (X / 480) + X % 480) % 16 = X % 480 % 16 := by
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 16 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 16 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [← this]
    rw [← h_eq]
    exact h16
  have h_lt : X % 480 < 480 := Nat.mod_lt _ (by decide)
  have h_cases : X % 480 % 32 = 17 ∨ X % 480 = 449 := chinese_remainder_helper (X % 480) h3_r h5_r h16_r h_lt
  rcases h_cases with h17 | h449
  · left
    have : X % 32 = X % 480 % 32 := by
      conv_lhs => rw [h_eq]
      rw [Nat.add_mod]
      have h_mul : (480 * (X / 480)) % 32 = 0 := by
        rw [Nat.mul_mod]
        have : 480 % 32 = 0 := rfl
        rw [this, zero_mul]
        rfl
      rw [h_mul, zero_add, Nat.mod_mod]
    rw [this, h17]
  · right
    exact h449


-- This is a mock-up of the context around line 1319 of Spec.lean
lemma mock_branch (b e p n : ℕ) (h_eq : a (n + 11) = b ^ e) (hp_odd : p % 2 = 1)
    (h_B_mod3 : b ^ (e / p) % 3 = 2) (h_B_mod5 : b ^ (e / p) % 5 = 4)
    (h_B_eq : b ^ e = (b ^ (e / p)) ^ p) (hb8 : b ^ e % 8 = 1) (h_B_mod8 : b ^ (e / p) % 8 = 1) : False := by
  have h_B_mod16_cases : b ^ (e / p) % 16 = 1 ∨ b ^ (e / p) % 16 = 9 := by
    have : b ^ (e / p) % 8 = 1 := h_B_mod8
    omega
  rcases h_B_mod16_cases with hB16_1 | hB16_9
  · have h_cases : b ^ (e / p) % 32 = 17 ∨ b ^ (e / p) % 480 = 449 := chinese_remainder_X (b ^ (e / p)) h_B_mod3 h_B_mod5 hB16_1
    rcases h_cases with h_B_mod32 | h_B_449
    · -- Case: b ^ (e / p) % 32 = 17
      have h_a_mod32 : a (n + 11) % 32 = 1 := mod_32_of_mod_256 (a_mod_256 n)
      have h_mod_pow : (b ^ (e / p)) ^ p % 32 = 17 := by
        obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        have h_B_mod32_rw : b ^ (e / (2 * k + 1)) % 32 = 17 := by
          rw [← hk]
          exact h_B_mod32
        rw [hk]
        let B := b ^ (e / (2 * k + 1))
        have h_sq : B ^ 2 % 32 = 17 ^ 2 % 32 := by
          rw [pow_two, pow_two]
          have h_B_32 : B % 32 = 17 := h_B_mod32_rw
          have h_mod_mul : (B * B) % 32 = (17 * 17) % 32 := by
            rw [Nat.mul_mod, h_B_32]
          exact h_mod_mul
        have h_sq_val : 17 ^ 2 % 32 = 1 := by decide
        rw [h_sq_val] at h_sq
        have h_pow : B ^ (2 * k + 1) = (B ^ 2) ^ k * B := by
          rw [pow_succ, pow_mul]
        rw [h_pow]
        have h_pow2 : ((B ^ 2) ^ k) % 32 = 1 := by
          have : ((B ^ 2) ^ k) % 32 = ((B ^ 2) % 32) ^ k % 32 := Nat.pow_mod (B ^ 2) k 32
          rw [h_sq] at this
          simp only [Nat.one_pow] at this
          exact this
        rw [Nat.mul_mod, h_pow2, one_mul, Nat.mod_mod]
        exact h_B_mod32_rw
      have h_B_pow_eq : (b ^ (e / p)) ^ p = a (n + 11) := by
        rw [← h_B_eq]
        exact h_eq.symm
      rw [h_B_pow_eq] at h_mod_pow
      rw [h_a_mod32] at h_mod_pow
      revert h_mod_pow
      decide
    · -- Case: b ^ (e / p) % 480 = 449
      have h_B_128 : b ^ (e / p) % 128 = 1 := by
        have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        obtain ⟨k, hk⟩ := hp
        let B := b ^ (e / p)
        have h_B_pow : B ^ p % 128 = 1 := by
          have h_eq : B ^ p = a (n + 11) := by
            rw [← h_B_eq]
            exact h_eq.symm
          rw [h_eq]
          have h256 := a_mod_256 n
          have h128_64 := mod_of_mod_256 h256
          exact h128_64.1
        have h128_cases := mod_128_of_mod_480_eq_449 h_B_449
        rcases h128_cases with h128_33 | h128_65
        · have h64_33 : B % 64 = 33 := by
            have : B = 128 * (B / 128) + B % 128 := (Nat.div_add_mod B 128).symm
            rw [h128_33] at this
            rw [this]
            have : 128 * (B / 128) + 33 = 33 + 64 * (2 * (B / 128)) := by ring
            rw [this]
            rw [Nat.add_mul_mod_self_left]
          have h_pow_eq := B_pow_mod_64_eq_33 B p h64_33 hp_odd
          have h_pow_128 : B ^ p % 64 = 1 := by
            have h256 := a_mod_256 n
            have h128_64 := mod_of_mod_256 h256
            have h_eq : B ^ p = a (n + 11) := by
              rw [← h_B_eq]
              exact h_eq.symm
            rw [h_eq]
            exact h128_64.2
          rw [h_pow_eq] at h_pow_128
          contradiction
        · have h_pow_eq := B_pow_mod_128_eq_65 B p h128_65 hp_odd
          rw [h_pow_eq] at h_B_pow
          contradiction
      have h_B_128_other : b ^ (e / p) % 128 = 33 ∨ b ^ (e / p) % 128 = 65 := mod_128_of_mod_480_eq_449 h_B_449
      rcases h_B_128_other with h128_33 | h128_65
      · rw [h128_33] at h_B_128
        contradiction
      · rw [h128_65] at h_B_128
        contradiction
  · sorry
