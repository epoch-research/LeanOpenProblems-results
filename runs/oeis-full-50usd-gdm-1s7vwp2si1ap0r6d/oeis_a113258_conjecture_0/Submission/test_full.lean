import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 4000000
set_option maxRecDepth 500000

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

attribute [irreducible] a

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

lemma thirty_three_pow_odd (k : ℕ) : 33 ^ (2 * k + 1) % 64 = 33 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_pow : 33 ^ (2 * (k + 1) + 1) = 33 ^ (2 * k + 1) * 1089 := by ring
    rw [h_pow, Nat.mul_mod, ih]

lemma b_pow_mod_64_eq_33 (b p : ℕ) (hb : b % 64 = 33) (hp_odd : p % 2 = 1) : b ^ p % 64 = 33 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk, Nat.pow_mod, hb]
  exact thirty_three_pow_odd k

lemma sixty_five_pow_odd (k : ℕ) : 65 ^ (2 * k + 1) % 128 = 65 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_pow : 65 ^ (2 * (k + 1) + 1) = 65 ^ (2 * k + 1) * 4225 := by ring
    rw [h_pow, Nat.mul_mod, ih]

lemma b_pow_mod_128_eq_65 (b p : ℕ) (hb : b % 128 = 65) (hp_odd : p % 2 = 1) : b ^ p % 128 = 65 := by
  have hp : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp
  rw [hk, Nat.pow_mod, hb]
  exact sixty_five_pow_odd k

lemma nine_pow_odd (k : ℕ) : 9 ^ (2 * k + 1) % 16 = 9 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_pow : 9 ^ (2 * (k + 1) + 1) = 9 ^ (2 * k + 1) * 81 := by ring
    rw [h_pow, Nat.mul_mod, ih]

lemma mod_16_pow (b p : ℕ) (hp : p % 2 = 1) (hb : b % 16 = 9) : b ^ p % 16 = 9 := by
  have hp_eq : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  obtain ⟨k, hk⟩ := hp_eq
  rw [hk, Nat.pow_mod, hb]
  exact nine_pow_odd k

lemma seventeen_pow_odd (k : ℕ) : 17 ^ (2 * k + 1) % 32 = 17 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_pow : 17 ^ (2 * (k + 1) + 1) = 17 ^ (2 * k + 1) * 289 := by ring
    rw [h_pow, Nat.mul_mod, ih]

lemma mock_branch (b e p n : ℕ) (h_eq : a (n + 11) = b ^ e) (hp_odd : p % 2 = 1)
    (h_B_mod3 : b ^ (e / p) % 3 = 2) (h_B_mod5 : b ^ (e / p) % 5 = 4)
    (h_B_eq : b ^ e = (b ^ (e / p)) ^ p) (hb8 : b ^ e % 8 = 1) (h_B_mod8 : b ^ (e / p) % 8 = 1) : False := by
  have h_b_mod16_cases : b ^ (e / p) % 16 = 1 ∨ b ^ (e / p) % 16 = 9 := by omega
  rcases h_b_mod16_cases with hB16_1 | hB16_9
  · have h_b_mod32_cases : b ^ (e / p) % 32 = 1 ∨ b ^ (e / p) % 32 = 17 := by omega
    rcases h_b_mod32_cases with hB32_1 | hB32_17
    · have h_b_mod64_cases : b ^ (e / p) % 64 = 1 ∨ b ^ (e / p) % 64 = 33 := by omega
      rcases h_b_mod64_cases with hB64_1 | hB64_33
      · have h_b_mod128_cases : b ^ (e / p) % 128 = 1 ∨ b ^ (e / p) % 128 = 65 := by omega
        rcases h_b_mod128_cases with hB128_1 | hB128_65
        · -- here we would have b ^ (e / p) % 128 = 1, but we want False, which we'll handle outside
          sorry
        · -- Case: b ^ (e / p) % 128 = 65
          have h_pow_eq := b_pow_mod_128_eq_65 (b ^ (e / p)) p hB128_65 hp_odd
          have h_B_pow_128 : (b ^ (e / p)) ^ p % 128 = 1 := by
            have h_eq2 : (b ^ (e / p)) ^ p = a (n + 11) := h_B_eq.symm.trans h_eq.symm
            have h_mod2 : (b ^ (e / p)) ^ p % 128 = a (n + 11) % 128 := congr_arg (fun x => x % 128) h_eq2
            rw [h_mod2]
            have h256 : a (n + 11) % 256 = 1 := a_mod_256 n
            have h128_64 : a (n + 11) % 128 = 1 ∧ a (n + 11) % 64 = 1 := mod_of_mod_256 h256
            exact h128_64.1
          rw [h_pow_eq] at h_B_pow_128
          contradiction
      · -- Case: b ^ (e / p) % 64 = 33
        have h_pow_eq := b_pow_mod_64_eq_33 (b ^ (e / p)) p hB64_33 hp_odd
        have h_pow_64 : (b ^ (e / p)) ^ p % 64 = 1 := by
          have h_eq2 : (b ^ (e / p)) ^ p = a (n + 11) := h_B_eq.symm.trans h_eq.symm
          have h_mod2 : (b ^ (e / p)) ^ p % 64 = a (n + 11) % 64 := congr_arg (fun x => x % 64) h_eq2
          rw [h_mod2]
          have h256 : a (n + 11) % 256 = 1 := a_mod_256 n
          have h128_64 : a (n + 11) % 128 = 1 ∧ a (n + 11) % 64 = 1 := mod_of_mod_256 h256
          exact h128_64.2
        rw [h_pow_eq] at h_pow_64
        contradiction
    · -- Case: b ^ (e / p) % 32 = 17
      have h_pow_eq : (b ^ (e / p)) ^ p % 32 = 17 := by
        obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        rw [hk, Nat.pow_mod, hB32_17]
        exact seventeen_pow_odd k
      have h_pow_32 : (b ^ (e / p)) ^ p % 32 = 1 := by
        have h_eq2 : (b ^ (e / p)) ^ p = a (n + 11) := h_B_eq.symm.trans h_eq.symm
        have h_mod2 : (b ^ (e / p)) ^ p % 32 = a (n + 11) % 32 := congr_arg (fun x => x % 32) h_eq2
        rw [h_mod2]
        exact mod_32_of_mod_256 (a_mod_256 n)
      rw [h_pow_eq] at h_pow_32
      contradiction
  · -- Case: b ^ (e / p) % 16 = 9
    have h_pow_eq := mod_16_pow (b ^ (e / p)) p hp_odd hB16_9
    have h_pow_16 : (b ^ (e / p)) ^ p % 16 = 1 := by
      have h_eq2 : (b ^ (e / p)) ^ p = a (n + 11) := h_B_eq.symm.trans h_eq.symm
      have h_mod2 : (b ^ (e / p)) ^ p % 16 = a (n + 11) % 16 := congr_arg (fun x => x % 16) h_eq2
      rw [h_mod2]
      have h256 : a (n + 11) % 256 = 1 := a_mod_256 n
      have h128_64 : a (n + 11) % 128 = 1 ∧ a (n + 11) % 64 = 1 := mod_of_mod_256 h256
      have h64 : a (n + 11) % 64 = 1 := h128_64.2
      have h_eq : a (n + 11) = 64 * (a (n + 11) / 64) + 1 := by
        have := Nat.div_add_mod (a (n + 11)) 64
        omega
      rw [h_eq]
      have : 64 * (a (n + 11) / 64) + 1 = 1 + 16 * (4 * (a (n + 11) / 64)) := by ring
      rw [this]
      rw [Nat.add_mul_mod_self_left]
    rw [h_pow_eq] at h_pow_16
    contradiction
