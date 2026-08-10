import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 4000000
set_option maxRecDepth 500000

open Nat

/--
A113258: Ascending descending base exponent transform of factorials.
$$a(n) = \sum_{i = 1}^n (i!) ^ {(n-i+1)!}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

lemma two_pow_even_mod_three (k : ℕ) : 2 ^ (2 * k) % 3 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_pow : 2 ^ (2 * (k + 1)) = 2 ^ (2 * k) * 4 := by ring
    rw [h_pow]
    rw [Nat.mul_mod, ih]

lemma dvd_pow_of_pos {a b : ℕ} (h : a ∣ b) {c : ℕ} (hc : c > 0) : a ∣ b ^ c := by
  cases c with
  | zero => omega
  | succ c =>
    rw [pow_succ]
    exact dvd_mul_of_dvd_right h _

lemma not_power_of_prime_div_not_sq_div {n : ℕ} (p : ℕ) (hp : Nat.Prime p) (h_div : p ∣ n) (h_ndiv : ¬ p ^ 2 ∣ n) :
    ∀ (b e : ℕ), 1 < b → 1 < e → b ^ e ≠ n := by
  intro b e hb he h_eq
  have hp_div : p ∣ b ^ e := by rw [h_eq]; exact h_div
  have hp_b : p ∣ b := Nat.Prime.dvd_of_dvd_pow hp hp_div
  have h_sq_div : p ^ 2 ∣ b ^ e := by
    have : e = 2 + (e - 2) := by omega
    rw [this, pow_add]
    have h_sq : p ^ 2 ∣ b ^ 2 := pow_dvd_pow_of_dvd hp_b 2
    exact dvd_mul_of_dvd_left h_sq _
  rw [h_eq] at h_sq_div
  exact h_ndiv h_sq_div

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

lemma a_mod_three (n : ℕ) (hn : n ≥ 5) : a n % 3 = 2 := by
  have hn2 : n ≥ 2 := by omega
  rw [a_split n hn2]
  have h_one : 1 ^ n.factorial = 1 := Nat.one_pow _
  have h_two : 2 ^ (n - 1).factorial % 3 = 1 := by
    have h_dvd : 2 ∣ (n - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    obtain ⟨k, hk⟩ := h_dvd
    rw [hk]
    exact two_pow_even_mod_three k
  have h_sum : Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) % 3 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro i hi
    exact dvd_pow_of_pos (Nat.dvd_factorial (by omega) (by omega)) (Nat.factorial_pos _)
  rw [h_one]
  have h_add : (1 + 2 ^ (n - 1).factorial + Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2)))) % 3 = 2 := by
    rw [Nat.add_mod, h_sum]
    simp only [add_zero, Nat.mod_mod]
    rw [Nat.add_mod]
    have h_one_mod : 1 % 3 = 1 := rfl
    rw [h_one_mod, h_two]
  exact h_add

lemma a_mod_eight (n : ℕ) (hn : n ≥ 5) : a n % 8 = 1 := by
  have hn2 : n ≥ 2 := by omega
  rw [a_split n hn2]
  have h_one : 1 ^ n.factorial = 1 := Nat.one_pow _
  have h_two : 2 ^ (n - 1).factorial % 8 = 0 := by
    have h_ge : (n - 1).factorial ≥ 3 := by
      have h4 : 4 ≤ n - 1 := by omega
      have h_fac : Nat.factorial 4 ≤ (n - 1).factorial := Nat.factorial_le h4
      have h_fac24 : Nat.factorial 4 = 24 := rfl
      rw [h_fac24] at h_fac
      omega
    have h_pow : 2 ^ (n - 1).factorial = 8 * 2 ^ ((n - 1).factorial - 3) := by
      have : (n - 1).factorial = 3 + ((n - 1).factorial - 3) := by omega
      conv_lhs => rw [this]
      rw [pow_add]
      rfl
    rw [h_pow]
    simp only [Nat.mul_mod_right]
  have h_sum : Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro i hi
    have hi_lt : i < n - 2 := Finset.mem_range.mp hi
    by_cases h_cases : i < n - 4
    · have h_even : 2 ∣ (i + 3).factorial := Nat.dvd_factorial (by omega) (by omega)
      obtain ⟨k, hk⟩ := h_even
      rw [hk, mul_pow]
      have hm : (n - i - 2).factorial ≥ 3 := by
        have h_sub : Nat.factorial 3 ≤ (n - i - 2).factorial := Nat.factorial_le (by omega)
        have h_fac6 : Nat.factorial 3 = 6 := rfl
        rw [h_fac6] at h_sub
        omega
      have h_div : 8 ∣ 2 ^ (n - i - 2).factorial := by
        have : (n - i - 2).factorial = 3 + ((n - i - 2).factorial - 3) := by omega
        rw [this, pow_add]
        exact dvd_mul_right 8 _
      exact dvd_mul_of_dvd_left h_div _
    · have hi_eq : i = n - 4 ∨ i = n - 3 := by omega
      rcases hi_eq with rfl | rfl
      · have h_sub : n - (n - 4) - 2 = 2 := by omega
        rw [h_sub]
        simp only [Nat.factorial_two]
        have h_sub2 : n - 4 + 3 = n - 1 := by omega
        have h_dvd : 4 ∣ (n - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
        obtain ⟨k, hk⟩ := h_dvd
        have h_term_eq : (n - 4 + 3).factorial ^ 2 = (n - 1).factorial ^ 2 := by rw [h_sub2]
        rw [h_term_eq, hk, mul_pow]
        have : 4 ^ 2 = 8 * 2 := rfl
        rw [this, mul_assoc]
        exact dvd_mul_right 8 _
      · have h_sub : n - (n - 3) - 2 = 1 := by omega
        rw [h_sub]
        simp only [Nat.factorial_one, pow_one]
        have h_sub3 : n - 3 + 3 = n := by omega
        have h_term_eq : (n - 3 + 3).factorial = n.factorial := by rw [h_sub3]
        rw [h_term_eq]
        have h_dvd5 : 8 ∣ Nat.factorial 5 := by decide
        have h_dvdn : Nat.factorial 5 ∣ n.factorial := Nat.factorial_dvd_factorial hn
        exact dvd_trans h_dvd5 h_dvdn
  rw [h_one]
  have h_add : (1 + 2 ^ (n - 1).factorial + Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2)))) % 8 = 1 := by
    rw [Nat.add_mod, h_sum]
    simp only [add_zero, Nat.mod_mod]
    rw [Nat.add_mod]
    have h_one_mod : 1 % 8 = 1 := rfl
    rw [h_one_mod, h_two]
  exact h_add

lemma a_mod_five (n : ℕ) (hn : n ≥ 5) : a n % 5 = 4 := by
  have hn2 : n ≥ 2 := by omega
  rw [a_split n hn2]
  have h_one : 1 ^ n.factorial = 1 := Nat.one_pow _
  have h_sum_split : Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) =
      6 ^ (n - 2).factorial + 24 ^ (n - 3).factorial +
      Finset.sum (Finset.range (n - 4)) (fun i => (Nat.factorial (i + 5)) ^ (Nat.factorial (n - i - 4))) := by
    have h_eq : n - 2 = (n - 4) + 2 := by omega
    conv_lhs => rw [h_eq]
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have h_sum_eq : (∑ k ∈ Finset.range (n - 4), (k + 1 + 1 + 3)! ^ (n - (k + 1 + 1) - 2)!) = (∑ i ∈ Finset.range (n - 4), (i + 5)! ^ (n - i - 4)!) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
    rw [h_sum_eq]
    have h3 : (0 + 3).factorial = 6 := rfl
    have h4 : (0 + 1 + 3).factorial = 24 := rfl
    have h_sub_a : n - 0 - 2 = n - 2 := by omega
    have h_sub_b : n - 1 - 2 = n - 3 := by omega
    rw [h3, h4, h_sub_a, h_sub_b]
    ring
  rw [h_sum_split]
  have h_two : 2 ^ (n - 1).factorial % 5 = 1 := by
    have h_div4 : 4 ∣ (n - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    obtain ⟨k, hk⟩ := h_div4
    rw [hk]
    have h_pow : 2 ^ (4 * k) = (2 ^ 4) ^ k := by rw [← pow_mul]
    rw [h_pow]
    have : 2 ^ 4 = 16 := rfl
    rw [this]
    have h_pow_mod (j : ℕ) : 16 ^ j % 5 = 1 := by
      induction j with
      | zero => rfl
      | succ j ih =>
        have : 16 ^ (j + 1) = 16 ^ j * 16 := by ring
        rw [this, Nat.mul_mod, ih]
    exact h_pow_mod _
  have h_six : 6 ^ (n - 2).factorial % 5 = 1 := by
    have h_pow_mod (k : ℕ) : 6 ^ k % 5 = 1 := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have : 6 ^ (k + 1) = 6 ^ k * 6 := by ring
        rw [this, Nat.mul_mod, ih]
    exact h_pow_mod _
  have h_24 : 24 ^ (n - 3).factorial % 5 = 1 := by
    have h_ge : (n - 3).factorial % 2 = 0 := by
      have h_dvd : 2 ∣ (n - 3).factorial := Nat.dvd_factorial (by omega) (by omega)
      exact Nat.mod_eq_zero_of_dvd h_dvd
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h_ge
    rw [hk]
    have h_pow : 24 ^ (2 * k) = (24 ^ 2) ^ k := by rw [← pow_mul]
    rw [h_pow]
    have : 24 ^ 2 = 576 := rfl
    rw [this]
    have h_pow_mod (j : ℕ) : 576 ^ j % 5 = 1 := by
      induction j with
      | zero => rfl
      | succ j ih =>
        have : 576 ^ (j + 1) = 576 ^ j * 576 := by ring
        rw [this, Nat.mul_mod, ih]
    exact h_pow_mod _
  have h_sum : Finset.sum (Finset.range (n - 4)) (fun i => (Nat.factorial (i + 5)) ^ (Nat.factorial (n - i - 4))) % 5 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro i hi
    exact dvd_pow_of_pos (Nat.dvd_factorial (by omega) (by omega)) (Nat.factorial_pos _)
  rw [h_one]
  have h_add : (1 + 2 ^ (n - 1).factorial + (6 ^ (n - 2).factorial + 24 ^ (n - 3).factorial + Finset.sum (Finset.range (n - 4)) (fun i => (Nat.factorial (i + 5)) ^ (Nat.factorial (n - i - 4))))) % 5 = 4 := by
    rw [Nat.add_mod, Nat.add_mod (6 ^ (n - 2).factorial + 24 ^ (n - 3).factorial), h_sum]
    simp only [add_zero, Nat.mod_mod]
    rw [Nat.add_mod (6 ^ (n - 2).factorial)]
    rw [h_six, h_24]
    rw [Nat.add_mod 1]
    rw [h_two]
  exact h_add


lemma odd_of_pow_mod_three_eq_two (b e : ℕ) (h : (b ^ e) % 3 = 2) : e % 2 = 1 := by
  have : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases this with h_even | h_odd
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h_even
    rw [hk, mul_comm, pow_mul] at h
    have h_sq : ((b ^ k) ^ 2) % 3 = 0 ∨ ((b ^ k) ^ 2) % 3 = 1 := by
      have h_mod : (b ^ k) % 3 = 0 ∨ (b ^ k) % 3 = 1 ∨ (b ^ k) % 3 = 2 := by omega
      rcases h_mod with h0 | h1 | h2
      · left; rw [pow_two, Nat.mul_mod, h0]
      · right; rw [pow_two, Nat.mul_mod, h1]
      · right; rw [pow_two, Nat.mul_mod, h2]
    rcases h_sq with h0 | h1
    · rw [h0] at h; contradiction
    · rw [h1] at h; contradiction
  · exact h_odd

lemma b_mod_three_eq_two (b e : ℕ) (he : e % 2 = 1) (h : (b ^ e) % 3 = 2) : b % 3 = 2 := by
  have h_mod : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases h_mod with h0 | h1 | h2
  · rw [Nat.pow_mod, h0] at h
    have he_pos : e > 0 := by omega
    have h_zero : 0 ^ e = 0 := Nat.zero_pow he_pos
    rw [h_zero] at h
    contradiction
  · rw [Nat.pow_mod, h1] at h
    rw [Nat.one_pow] at h
    contradiction
  · exact h2

lemma two_mul_four_pow_mod_five (k : ℕ) : (2 * 4 ^ k) % 5 = 2 ∨ (2 * 4 ^ k) % 5 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    have h_pow : 2 * 4 ^ (k + 1) = (2 * 4 ^ k) * 4 := by ring
    rw [h_pow, Nat.mul_mod]
    rcases ih with h | h
    · rw [h]; right; rfl
    · rw [h]; left; rfl

lemma three_mul_four_pow_mod_five (k : ℕ) : (3 * 4 ^ k) % 5 = 3 ∨ (3 * 4 ^ k) % 5 = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    have h_pow : 3 * 4 ^ (k + 1) = (3 * 4 ^ k) * 4 := by ring
    rw [h_pow, Nat.mul_mod]
    rcases ih with h | h
    · rw [h]; right; rfl
    · rw [h]; left; rfl

lemma b_mod_five_eq_four (b e : ℕ) (he : e % 2 = 1) (h : (b ^ e) % 5 = 4) : b % 5 = 4 := by
  have h_mod : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  rcases h_mod with h0 | h1 | h2 | h3 | h4
  · rw [Nat.pow_mod, h0] at h
    have he_pos : e > 0 := by omega
    have h_zero : 0 ^ e = 0 := Nat.zero_pow he_pos
    rw [h_zero] at h
    contradiction
  · rw [Nat.pow_mod, h1] at h
    rw [Nat.one_pow] at h
    contradiction
  · rw [Nat.pow_mod, h2] at h
    have hk : e = 2 * (e / 2) + 1 := by
      have h_div_mod := Nat.div_add_mod e 2
      omega
    have ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, hk⟩
    rw [hk] at h
    have h_pow : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 2 ^ 2 = 4 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_cases := two_mul_four_pow_mod_five k
    rcases h_cases with h_eq | h_eq
    · rw [h_eq] at h; contradiction
    · rw [h_eq] at h; contradiction
  · rw [Nat.pow_mod, h3] at h
    have hk : e = 2 * (e / 2) + 1 := by
      have h_div_mod := Nat.div_add_mod e 2
      omega
    have ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, hk⟩
    rw [hk] at h
    have h_pow : 3 ^ (2 * k + 1) = 3 * 9 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 3 ^ 2 = 9 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_pow_red : 9 ^ k % 5 = 4 ^ k % 5 := Nat.pow_mod 9 k 5
    have h_red : (3 * 9 ^ k) % 5 = (3 * 4 ^ k) % 5 := by
      rw [Nat.mul_mod, Nat.mul_mod 3, h_pow_red]
      simp only [Nat.mod_mod]
      rw [← Nat.mul_mod]
    rw [h_red] at h
    have h_cases := three_mul_four_pow_mod_five k
    rcases h_cases with h_eq | h_eq
    · rw [h_eq] at h; contradiction
    · rw [h_eq] at h; contradiction
  · exact h4

lemma even_pow_mod_eight_ne_one (x e : ℕ) (hx : x % 2 = 0) (he : e > 0) : (x ^ e) % 8 ≠ 1 := by
  intro h
  have hdvd : 2 ∣ x := Nat.dvd_of_mod_eq_zero hx
  have h_dvd_pow : 2 ∣ x ^ e := dvd_pow_of_pos hdvd he
  have h_odd : (x ^ e) % 2 = 1 := by
    have h_eq : x ^ e = 8 * (x ^ e / 8) + 1 := by
      have := Nat.div_add_mod (x ^ e) 8
      omega
    rw [h_eq]
    omega
  have h_even : (x ^ e) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd_pow
  omega

lemma odd_pow_mod_eight_ne_one (x k : ℕ) (hx : x = 3 ∨ x = 5 ∨ x = 7) : (x ^ (2 * k + 1)) % 8 ≠ 1 := by
  intro h
  rcases hx with rfl | rfl | rfl
  · have h_pow : 3 ^ (2 * k + 1) = 3 * 9 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 3 ^ 2 = 9 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_pow_red : 9 ^ k % 8 = 1 := by
      have : 9 % 8 = 1 := rfl
      have h_pow_mod : 9 ^ k % 8 = (9 % 8) ^ k % 8 := Nat.pow_mod 9 k 8
      rw [this, Nat.one_pow] at h_pow_mod
      exact h_pow_mod
    have h_red : (3 * 9 ^ k) % 8 = 3 := by
      rw [Nat.mul_mod, h_pow_red]
    rw [h_red] at h
    contradiction
  · have h_pow : 5 ^ (2 * k + 1) = 5 * 25 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 5 ^ 2 = 25 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_pow_red : 25 ^ k % 8 = 1 := by
      have : 25 % 8 = 1 := rfl
      have h_pow_mod : 25 ^ k % 8 = (25 % 8) ^ k % 8 := Nat.pow_mod 25 k 8
      rw [this, Nat.one_pow] at h_pow_mod
      exact h_pow_mod
    have h_red : (5 * 25 ^ k) % 8 = 5 := by
      rw [Nat.mul_mod, h_pow_red]
    rw [h_red] at h
    contradiction
  · have h_pow : 7 ^ (2 * k + 1) = 7 * 49 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 7 ^ 2 = 49 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_pow_red : 49 ^ k % 8 = 1 := by
      have : 49 % 8 = 1 := rfl
      have h_pow_mod : 49 ^ k % 8 = (49 % 8) ^ k % 8 := Nat.pow_mod 49 k 8
      rw [this, Nat.one_pow] at h_pow_mod
      exact h_pow_mod
    have h_red : (7 * 49 ^ k) % 8 = 7 := by
      rw [Nat.mul_mod, h_pow_red]
    rw [h_red] at h
    contradiction

lemma b_mod_eight_eq_one (b e : ℕ) (he : e % 2 = 1) (h : (b ^ e) % 8 = 1) : b % 8 = 1 := by
  have h_mod : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨ b % 8 = 6 ∨ b % 8 = 7 := by omega
  rcases h_mod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [Nat.pow_mod, h0] at h
    have he_pos : e > 0 := by omega
    have h_zero : 0 ^ e = 0 := Nat.zero_pow he_pos
    rw [h_zero] at h
    contradiction
  · exact h1
  · rw [Nat.pow_mod, h2] at h
    have he_pos : e > 0 := by omega
    have : 2 % 2 = 0 := rfl
    have h_ne := even_pow_mod_eight_ne_one 2 e this he_pos
    contradiction
  · rw [Nat.pow_mod, h3] at h
    obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by
      have h_div_mod := Nat.div_add_mod e 2
      omega⟩
    rw [hk] at h
    have h_ne := odd_pow_mod_eight_ne_one 3 k (by simp)
    contradiction
  · rw [Nat.pow_mod, h4] at h
    have he_pos : e > 0 := by omega
    have : 4 % 2 = 0 := rfl
    have h_ne := even_pow_mod_eight_ne_one 4 e this he_pos
    contradiction
  · rw [Nat.pow_mod, h5] at h
    obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by
      have h_div_mod := Nat.div_add_mod e 2
      omega⟩
    rw [hk] at h
    have h_ne := odd_pow_mod_eight_ne_one 5 k (by simp)
    contradiction
  · rw [Nat.pow_mod, h6] at h
    have he_pos : e > 0 := by omega
    have : 6 % 2 = 0 := rfl
    have h_ne := even_pow_mod_eight_ne_one 6 e this he_pos
    contradiction
  · rw [Nat.pow_mod, h7] at h
    obtain ⟨k, hk⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by
      have h_div_mod := Nat.div_add_mod e 2
      omega⟩
    rw [hk] at h
    have h_ne := odd_pow_mod_eight_ne_one 7 k (by simp)
    contradiction

lemma b_ge_89 (b e : ℕ) (hb : 1 < b) (he : e % 2 = 1) (h3 : (b ^ e) % 3 = 2) (h5 : (b ^ e) % 5 = 4) (h8 : (b ^ e) % 8 = 1) : b ≥ 89 := by
  have m3 := b_mod_three_eq_two b e he h3
  have m5 := b_mod_five_eq_four b e he h5
  have m8 := b_mod_eight_eq_one b e he h8
  omega

lemma pow_10_mod : (2 ^ 10) % 11069 = 1024 := by decide

lemma pow_100_mod : (2 ^ 100) % 11069 = 1296 := by
  have : 2 ^ 100 = (2 ^ 10) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_10_mod]

lemma pow_1000_mod : (2 ^ 1000) % 11069 = 385 := by
  have : 2 ^ 1000 = (2 ^ 100) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_100_mod]

lemma pow_10000_mod : (2 ^ 10000) % 11069 = 6585 := by
  have : 2 ^ 10000 = (2 ^ 1000) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_1000_mod]

lemma pow_100000_mod : (2 ^ 100000) % 11069 = 1149 := by
  have : 2 ^ 100000 = (2 ^ 10000) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_10000_mod]

lemma term1_mod : ((2 ^ 10) ^ 8) % 11069 = 2307 := by
  rw [Nat.pow_mod, pow_10_mod]

lemma term2_mod : ((2 ^ 100) ^ 8) % 11069 = 9084 := by
  rw [Nat.pow_mod, pow_100_mod]

lemma term3_mod : ((2 ^ 1000) ^ 2) % 11069 = 4328 := by
  rw [Nat.pow_mod, pow_1000_mod]

lemma term4_mod : ((2 ^ 10000) ^ 6) % 11069 = 3557 := by
  rw [Nat.pow_mod, pow_10000_mod]

lemma term5_mod : ((2 ^ 100000) ^ 3) % 11069 = 4120 := by
  rw [Nat.pow_mod, pow_100000_mod]

lemma product_mod (A B C D E : ℕ) (hA : A % 11069 = 4120) (hB : B % 11069 = 3557) (hC : C % 11069 = 4328) (hD : D % 11069 = 9084) (hE : E % 11069 = 2307) : (A * B * C * D * E) % 11069 = 6860 := by
  simp only [Nat.mul_mod, Nat.mod_mod, hE, hD, hC, hB, hA]

lemma pow_362880_mod : (2 ^ 362880) % 11069 = 6860 := by
  have : 2 ^ 362880 = (2 ^ 100000) ^ 3 * (2 ^ 10000) ^ 6 * (2 ^ 1000) ^ 2 * (2 ^ 100) ^ 8 * (2 ^ 10) ^ 8 := by ring
  rw [this]
  exact product_mod _ _ _ _ _ term5_mod term4_mod term3_mod term2_mod term1_mod

lemma pow_10_sq_mod : (2 ^ 10) % 122522761 = 1024 := by decide

lemma pow_100_sq_mod : (2 ^ 100) % 122522761 = 1207817 := by
  have : 2 ^ 100 = (2 ^ 10) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_10_sq_mod]

lemma pow_1000_sq_mod : (2 ^ 1000) % 122522761 = 53109447 := by
  have : 2 ^ 1000 = (2 ^ 100) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_100_sq_mod]

lemma pow_10000_sq_mod : (2 ^ 10000) % 122522761 = 5009773 := by
  have : 2 ^ 10000 = (2 ^ 1000) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_1000_sq_mod]

lemma pow_100000_sq_mod : (2 ^ 100000) % 122522761 = 76111593 := by
  have : 2 ^ 100000 = (2 ^ 10000) ^ 10 := by ring
  rw [this, Nat.pow_mod, pow_10000_sq_mod]

lemma term1_sq_mod : ((2 ^ 10) ^ 8) % 122522761 = 88377203 := by
  rw [Nat.pow_mod, pow_10_sq_mod]

lemma term2_sq_mod : ((2 ^ 100) ^ 8) % 122522761 = 52287971 := by
  rw [Nat.pow_mod, pow_100_sq_mod]

lemma term3_sq_mod : ((2 ^ 1000) ^ 2) % 122522761 = 94046552 := by
  rw [Nat.pow_mod, pow_1000_sq_mod]

lemma term4_sq_mod : ((2 ^ 10000) ^ 6) % 122522761 = 56732182 := by
  rw [Nat.pow_mod, pow_10000_sq_mod]

lemma term5_sq_mod : ((2 ^ 100000) ^ 3) % 122522761 = 60496205 := by
  rw [Nat.pow_mod, pow_100000_sq_mod]

lemma product_sq_mod (A B C D E : ℕ) (hA : A % 122522761 = 60496205) (hB : B % 122522761 = 56732182) (hC : C % 122522761 = 94046552) (hD : D % 122522761 = 52287971) (hE : E % 122522761 = 88377203) : (A * B * C * D * E) % 122522761 = 76338684 := by
  simp only [Nat.mul_mod, Nat.mod_mod, hE, hD, hC, hB, hA]

lemma pow_362880_sq_mod : (2 ^ 362880) % 122522761 = 76338684 := by
  have : 2 ^ 362880 = (2 ^ 100000) ^ 3 * (2 ^ 10000) ^ 6 * (2 ^ 1000) ^ 2 * (2 ^ 100) ^ 8 * (2 ^ 10) ^ 8 := by ring
  rw [this]
  exact product_sq_mod _ _ _ _ _ term5_sq_mod term4_sq_mod term3_sq_mod term2_sq_mod term1_sq_mod

lemma sum_10_mod : Finset.sum (Finset.range 8) (fun i => (i+3).factorial ^ (10 - i - 2).factorial) % 11069 = 4208 := by decide

lemma sum_10_sq_mod : Finset.sum (Finset.range 8) (fun i => (i+3).factorial ^ (10 - i - 2).factorial) % 122522761 = 100953488 := by decide

lemma pow_le_pow_of_le {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) (hb : b > 0) : a ^ c ≤ b ^ d := by
  calc a ^ c ≤ b ^ c := Nat.pow_le_pow_left hab c
       _     ≤ b ^ d := Nat.pow_le_pow_right hb hcd

lemma sum_le (n : ℕ) : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) ≤ (n + 9) * (n + 11).factorial ^ (n + 9).factorial := by
  have h_all : ∀ i ∈ Finset.range (n + 9), (i + 3).factorial ^ (n + 9 - i).factorial ≤ (n + 11).factorial ^ (n + 9).factorial := by
    intro i hi
    have hi_lt : i < n + 9 := Finset.mem_range.mp hi
    have h1 : i + 3 ≤ n + 11 := by omega
    have h2 : n + 9 - i ≤ n + 9 := by omega
    have h1_fac := Nat.factorial_le h1
    have h2_fac := Nat.factorial_le h2
    have h_fac_pos : (n + 11).factorial > 0 := Nat.factorial_pos _
    exact pow_le_pow_of_le h1_fac h2_fac h_fac_pos
  have h_sum_le' : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) ≤ Finset.sum (Finset.range (n + 9)) (fun _ => (n + 11).factorial ^ (n + 9).factorial) := by
    apply Finset.sum_le_sum
    exact h_all
  have h_const : Finset.sum (Finset.range (n + 9)) (fun _ => (n + 11).factorial ^ (n + 9).factorial) = (n + 9) * (n + 11).factorial ^ (n + 9).factorial := by
    rw [Finset.sum_const]
    simp only [Finset.card_range, smul_eq_mul]
  omega

lemma pow_succ_ge (x e : ℕ) (he : e ≥ 1) : (x + 1) ^ e ≥ x ^ e + e * x ^ (e - 1) := by
  induction e with
  | zero => omega
  | succ e ih =>
    by_cases h_zero : e = 0
    · subst h_zero; simp
    · have he_ge : e ≥ 1 := by omega
      have ih' := ih he_ge
      have h_mul : (x + 1) ^ (e + 1) = (x + 1) ^ e * (x + 1) := by ring
      rw [h_mul]
      have h_eq : (x ^ e + e * x ^ (e - 1)) * (x + 1) = x ^ (e + 1) + (e + 1) * x ^ e + e * x ^ (e - 1) := by
        have h_pow1 : x ^ (e + 1) = x ^ e * x := rfl
        have h_pow2 : x ^ (e - 1) * x = x ^ e := by
          have : e = e - 1 + 1 := by omega
          conv_rhs => rw [this]
          rw [pow_succ]
        rw [h_pow1, ← h_pow2]
        ring
      calc
        (x + 1) ^ e * (x + 1) ≥ (x ^ e + e * x ^ (e - 1)) * (x + 1) := Nat.mul_le_mul_right _ ih'
        _ = x ^ (e + 1) + (e + 1) * x ^ e + e * x ^ (e - 1) := h_eq
        _ ≥ x ^ (e + 1) + (e + 1) * x ^ e := by omega

lemma b_ge_pow_div (n b e : ℕ) (hb : 1 < b) (h_eq : b ^ e > 2 ^ (n + 10).factorial) :
    b ≥ 2 ^ ((n + 10).factorial / e) + 1 := by
  have h_le : 2 ^ (((n + 10).factorial / e) * e) ≤ 2 ^ (n + 10).factorial := by
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.div_mul_le_self
  have h_lt : (2 ^ ((n + 10).factorial / e)) ^ e < b ^ e := by
    rw [← pow_mul]
    calc
      2 ^ (((n + 10).factorial / e) * e) ≤ 2 ^ (n + 10).factorial := h_le
      _ < b ^ e := h_eq
  have h_base : 2 ^ ((n + 10).factorial / e) < b := by
    cases e with
    | zero =>
      simp at h_lt
    | succ e =>
      have h_ne : e + 1 ≠ 0 := by omega
      rwa [Nat.pow_lt_pow_iff_left h_ne] at h_lt
  omega

lemma factorial_le_pow_two_mul (M : ℕ) : M.factorial ≤ 2 ^ (M * (M - 1) / 2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    by_cases hM : M = 0
    · subst hM; simp
    · have h_le_pow : M + 1 ≤ 2 ^ M := Nat.lt_pow_self (by decide)
      have h_mul : (M + 1).factorial = (M + 1) * M.factorial := rfl
      rw [h_mul]
      have h_le : (M + 1) * M.factorial ≤ 2 ^ M * 2 ^ (M * (M - 1) / 2) := Nat.mul_le_mul h_le_pow ih
      rw [← pow_add] at h_le
      apply h_le.trans
      apply Nat.pow_le_pow_right (by decide)
      have h_eq : M + M * (M - 1) / 2 = (M + 1) * M / 2 := by
        have h_dvd1 : 2 ∣ M * (M - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self M)
        have h_dvd2 : 2 ∣ (M + 1) * M := by
          have : (M + 1) * M = M * (M + 1) := by ring
          rw [this]
          exact even_iff_two_dvd.mp (Nat.even_mul_succ_self M)
        apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
        rw [Nat.add_mul, Nat.div_mul_cancel h_dvd1, Nat.div_mul_cancel h_dvd2]
        have h_alg : (M + 1) * M = M * 2 + M * (M - 1) := by
          have h_sub : M * (M - 1) = M * M - M := by
            have h_sub' := Nat.mul_sub_left_distrib M M 1
            rw [mul_one] at h_sub'
            exact h_sub'
          rw [h_sub]
          have h_mul2 : M * 2 = M + M := by ring
          rw [h_mul2]
          have h_id : (M + 1) * M = M * M + M := by ring
          rw [h_id]
          have : M ≤ M * M := Nat.le_mul_self M
          omega
        rw [← h_alg]
      rw [h_eq]
      have : M + 1 - 1 = M := by omega
      rw [this]

lemma helper_ineq (n : ℕ) : (n + 11) * (n + 10) * (n + 9) ≤ 2 ^ (2 * n + 17) := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      (n + 1 + 11) * (n + 1 + 10) * (n + 1 + 9) = (n + 12) * ((n + 11) * (n + 10)) := by ring
      _ ≤ (4 * (n + 9)) * ((n + 11) * (n + 10)) := by
        apply Nat.mul_le_mul_right
        omega
      _ = 4 * ((n + 11) * (n + 10) * (n + 9)) := by ring
      _ ≤ 4 * 2 ^ (2 * n + 17) := Nat.mul_le_mul_left 4 ih
      _ = 2 ^ (2 * (n + 1) + 17) := by
        have h_eq : 2 * (n + 1) + 17 = 2 * n + 17 + 2 := by omega
        rw [h_eq, pow_add]
        ring

lemma fact_le_pow_of_n (n : ℕ) : (n + 11).factorial ≤ 2 ^ ((n + 10) * (n + 9) / 2) := by
  have h_fac : (n + 11).factorial = (n + 11) * (n + 10) * (n + 9) * (n + 8).factorial := by
    have h1 : (n + 11).factorial = (n + 11) * (n + 10).factorial := rfl
    have h2 : (n + 10).factorial = (n + 10) * (n + 9).factorial := rfl
    have h3 : (n + 9).factorial = (n + 9) * (n + 8).factorial := rfl
    rw [h1, h2, h3]
    ring
  rw [h_fac]
  have h_le := factorial_le_pow_two_mul (n + 8)
  have h_ineq := helper_ineq n
  have h_mul_le : (n + 11) * (n + 10) * (n + 9) * (n + 8).factorial ≤ 2 ^ (2 * n + 17) * 2 ^ ((n + 8) * (n + 7) / 2) :=
    Nat.mul_le_mul h_ineq h_le
  apply h_mul_le.trans
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have h_dvd1 : 2 ∣ (n + 8) * (n + 7) := by
    have : (n + 8) * (n + 7) = (n + 7) * (n + 7 + 1) := by ring
    rw [this]
    exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (n + 7))
  have h_dvd2 : 2 ∣ (n + 10) * (n + 9) := by
    have : (n + 10) * (n + 9) = (n + 9) * (n + 9 + 1) := by ring
    rw [this]
    exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (n + 9))
  apply Nat.le_of_mul_le_mul_right _ (by decide : 0 < 2)
  rw [Nat.add_mul, Nat.div_mul_cancel h_dvd1, Nat.div_mul_cancel h_dvd2]
  ring_nf
  omega

lemma sum_le_better (n : ℕ) :
    Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) ≤
    6 ^ (n + 9).factorial + (n + 8) * (n + 11).factorial ^ (n + 8).factorial := by
  rw [Finset.sum_range_succ']
  have h0 : (0 + 3).factorial ^ (n + 9 - 0).factorial = 6 ^ (n + 9).factorial := by
    simp
    rfl
  rw [h0]
  have h_all : ∀ k ∈ Finset.range (n + 8), (k + 1 + 3).factorial ^ (n + 9 - (k + 1)).factorial ≤ (n + 11).factorial ^ (n + 8).factorial := by
    intro k hk
    have hk_lt : k < n + 8 := Finset.mem_range.mp hk
    have h1 : k + 4 ≤ n + 11 := by omega
    have h2 : n + 8 - k ≤ n + 8 := by omega
    have h1_fac := Nat.factorial_le h1
    have h2_fac := Nat.factorial_le h2
    have h_fac_pos : (n + 11).factorial > 0 := Nat.factorial_pos _
    have h_eq_term : (k + 1 + 3).factorial ^ (n + 9 - (k + 1)).factorial = (k + 4).factorial ^ (n + 8 - k).factorial := by
      have : k + 1 + 3 = k + 4 := by omega
      rw [this]
      have : n + 9 - (k + 1) = n + 8 - k := by omega
      rw [this]
    rw [h_eq_term]
    exact pow_le_pow_of_le h1_fac h2_fac h_fac_pos
  have h_sum_le' : Finset.sum (Finset.range (n + 8)) (fun k => (k + 1 + 3).factorial ^ (n + 9 - (k + 1)).factorial) ≤
                   Finset.sum (Finset.range (n + 8)) (fun _ => (n + 11).factorial ^ (n + 8).factorial) := by
    apply Finset.sum_le_sum
    exact h_all
  have h_const : Finset.sum (Finset.range (n + 8)) (fun _ => (n + 11).factorial ^ (n + 8).factorial) =
                 (n + 8) * (n + 11).factorial ^ (n + 8).factorial := by
    rw [Finset.sum_const]
    simp only [Finset.card_range, smul_eq_mul]
  omega

lemma helper_exponent (n e : ℕ) (he : e ≥ 3) :
    (n + 10).factorial - (n + 10).factorial / e ≥ (n + 10).factorial / 2 + (n + 8).factorial := by
  have h_div_e : (n + 10).factorial / e ≤ (n + 10).factorial / 3 := Nat.div_le_div_left he (by decide)
  have h_sub_le : (n + 10).factorial - (n + 10).factorial / e ≥ (n + 10).factorial - (n + 10).factorial / 3 := by omega
  have h_fac : (n + 10).factorial = (n + 10) * (n + 9) * (n + 8).factorial := by
    have h1 : (n + 10).factorial = (n + 10) * (n + 9).factorial := rfl
    have h2 : (n + 9).factorial = (n + 9) * (n + 8).factorial := rfl
    rw [h1, h2, mul_assoc]
  have h_sum_le : (n + 10).factorial / 2 + (n + 8).factorial + (n + 10).factorial / 3 ≤ (n + 10).factorial := by
    clear h_div_e h_sub_le
    rw [h_fac]
    clear h_fac
    have h_bound : (n + 10) * (n + 9) ≥ 90 := by
      have h1 : n + 10 ≥ 10 := by omega
      have h2 : n + 9 ≥ 9 := by omega
      exact Nat.mul_le_mul h1 h2
    have h_X_pos : (n + 8).factorial ≥ 1 := Nat.factorial_pos _
    generalize h_C : (n + 10) * (n + 9) = C
    generalize h_X : (n + 8).factorial = X
    rw [h_C] at h_bound
    rw [h_X] at h_X_pos
    generalize h_Z : C * X = Z
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 6)
    have h_div2 : 2 * (Z / 2) ≤ Z := Nat.mul_div_le _ _
    have h_div3 : 3 * (Z / 3) ≤ Z := Nat.mul_div_le _ _
    have h_6X : 6 * X ≤ Z := by
      rw [← h_Z]
      calc
        6 * X ≤ 90 * X := Nat.mul_le_mul_right X (by omega : 6 ≤ 90)
        _     ≤ C * X   := Nat.mul_le_mul_right X h_bound
    have h_alg : 6 * (Z / 2 + X + Z / 3) = 3 * (2 * (Z / 2)) + 6 * X + 2 * (3 * (Z / 3)) := by ring
    calc
      6 * (Z / 2 + X + Z / 3) = 3 * (2 * (Z / 2)) + 6 * X + 2 * (3 * (Z / 3)) := h_alg
      _ ≤ 3 * Z + 6 * X + 2 * Z := by omega
      _ ≤ 3 * Z + Z + 2 * Z := by omega
      _ = 6 * Z := by ring
  have h_trans : (n + 10).factorial / 2 + (n + 8).factorial ≤ (n + 10).factorial - (n + 10).factorial / 3 := by omega
  clear h_fac h_sum_le
  omega

lemma helper_term1 (n : ℕ) : 6 ^ (n + 9).factorial < 2 ^ ((n + 10).factorial / 2) := by
  have h_le : 10 * (n + 9).factorial ≤ (n + 10).factorial := by
    have h_fac : (n + 10).factorial = (n + 10) * (n + 9).factorial := rfl
    rw [h_fac]
    apply Nat.mul_le_mul_right
    omega
  have h_le2 : 5 * (n + 9).factorial ≤ (n + 10).factorial / 2 := by
    have h_div : (10 * (n + 9).factorial) / 2 ≤ (n + 10).factorial / 2 := Nat.div_le_div_right h_le
    have h_simp : (10 * (n + 9).factorial) / 2 = 5 * (n + 9).factorial := by
      have : 10 * (n + 9).factorial = 5 * (n + 9).factorial * 2 := by ring
      rw [this, Nat.mul_div_cancel _ (by decide : 2 > 0)]
    rwa [h_simp] at h_div
  have h_pow : (2 ^ 5) ^ (n + 9).factorial ≤ 2 ^ ((n + 10).factorial / 2) := by
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    exact h_le2
  have h_lt : 6 ^ (n + 9).factorial < (2 ^ 5) ^ (n + 9).factorial := by
    have h_pos : (n + 9).factorial ≠ 0 := Nat.factorial_ne_zero _
    apply Nat.pow_lt_pow_left (by decide) h_pos
  exact h_lt.trans_le h_pow

lemma one_le_pow (x k : ℕ) (hx : x ≥ 1) : x ^ k ≥ 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    calc
      x ^ k * x ≥ x ^ k * 1 := Nat.mul_le_mul_left (x ^ k) hx
      _ ≥ 1 * 1 := Nat.mul_le_mul_right 1 ih
      _ = 1 := by ring

lemma self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    have h_ge1 : 2 ^ k ≥ 1 := one_le_pow 2 k (by decide)
    omega

lemma q_even_of_two_pow_mod_three (q : ℕ) (h : 2 ^ q % 3 = 1) : q % 2 = 0 := by
  have h_mod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · exact h0
  · obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    rw [hk] at h
    have h_pow : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, mul_comm]
      congr 1
      have : 2 ^ 2 = 4 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_mod_four : 4 % 3 = 1 := rfl
    have h_pow_mod : 4 ^ k % 3 = 1 := by
      have : 4 ^ k % 3 = (4 % 3) ^ k % 3 := Nat.pow_mod 4 k 3
      rw [h_mod_four] at this
      simp only [Nat.one_pow] at this
      exact this
    have h_red : (2 * 4 ^ k) % 3 = 2 := by
      rw [Nat.mul_mod, h_pow_mod]
    rw [h_red] at h
    contradiction

lemma four_pow_mod_five (k : ℕ) : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
  induction k with
  | zero => left; rfl
  | succ j ih =>
    have h_pow2 : 4 ^ (j + 1) = 4 ^ j * 4 := by ring
    rw [h_pow2, Nat.mul_mod]
    rcases ih with h_ih | h_ih
    · rw [h_ih]; right; rfl
    · rw [h_ih]; left; rfl

lemma q_odd_of_two_pow_mod_five (q : ℕ) (h : 2 ^ q % 5 = 3) : q % 2 = 1 := by
  have h_mod : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases h_mod with h0 | h1
  · obtain ⟨k, hk⟩ : ∃ k, q = 2 * k := ⟨q / 2, by omega⟩
    rw [hk] at h
    have h_pow : 2 ^ (2 * k) = 4 ^ k := by
      have : 2 ^ 2 = 4 := rfl
      rw [pow_mul, this]
    rw [h_pow] at h
    have h_cases := four_pow_mod_five k
    rcases h_cases with hc | hc
    · rw [hc] at h; contradiction
    · rw [hc] at h; contradiction
  · exact h1

lemma mod_16_pow (B p : ℕ) (hp : p % 2 = 1) (hB : B % 16 = 9) : B ^ p % 16 = 9 := by
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  rw [hk]
  have h_sq : B ^ 2 % 16 = 1 := by
    obtain ⟨d, hd⟩ : ∃ d, B = 16 * d + 9 := ⟨B / 16, by omega⟩
    rw [hd]
    have : (16 * d + 9) ^ 2 = 16 * (16 * d ^ 2 + 18 * d + 5) + 1 := by ring
    rw [this]
    have h_add : 16 * (16 * d ^ 2 + 18 * d + 5) + 1 = 1 + 16 * (16 * d ^ 2 + 18 * d + 5) := by ring
    rw [h_add]
    rw [Nat.add_mul_mod_self_left]
  have h_pow : B ^ (2 * k + 1) = (B ^ 2) ^ k * B := by
    rw [pow_succ, pow_mul]
  rw [h_pow]
  have h_pow2 : (B ^ 2) ^ k % 16 = 1 := by
    have : (B ^ 2) ^ k % 16 = ((B ^ 2) % 16) ^ k % 16 := Nat.pow_mod (B ^ 2) k 16
    rw [h_sq] at this
    simp only [Nat.one_pow] at this
    exact this
  rw [Nat.mul_mod, h_pow2, hB]


lemma chinese_remainder_helper (r : ℕ) (h3 : r % 3 = 2) (h5 : r % 5 = 4) (h16 : r % 16 = 1) (h_lt : r < 480) (h_ne : r ≠ 449) : r % 32 = 17 := by
  obtain ⟨k, hk⟩ : ∃ k, r = 16 * k + 1 := ⟨r / 16, by omega⟩
  have h_k_lt : k < 30 := by omega
  revert h_k_lt h3 h5 h16
  rcases k with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k
  all_goals (try rw [hk])
  all_goals (try decide)
  all_goals (try intro h_k_lt h3 h5 h16)
  all_goals (try exfalso)
  all_goals (try omega)

lemma chinese_remainder_X (X : ℕ) (h3 : X % 3 = 2) (h5 : X % 5 = 4) (h16 : X % 16 = 1) (h_ne : X % 480 ≠ 449) : X % 32 = 17 := by
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
  have h32_r : X % 480 % 32 = 17 := chinese_remainder_helper (X % 480) h3_r h5_r h16_r h_lt h_ne
  have : X % 32 = X % 480 % 32 := by
    conv_lhs => rw [h_eq]
    rw [Nat.add_mod]
    have h_mul : (480 * (X / 480)) % 32 = 0 := by
      rw [Nat.mul_mod]
      have : 480 % 32 = 0 := rfl
      rw [this, zero_mul]
      rfl
    rw [h_mul, zero_add, Nat.mod_mod]
  rw [this]
  exact h32_r


theorem oeis_a113258_conjecture_0.disproof :
    ¬ ∃ (n : ℕ), 4 < n ∧ ∃ (b e : ℕ), 1 < b ∧ 1 < e ∧ a n = b ^ e := by
  intro ⟨n, hn, b, e, hb, he, h_eq⟩
  rcases n with _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · omega
  · omega
  · omega
  · omega
  · -- n = 5
    have hp : Nat.Prime 23 := by decide
    have hd : 23 ∣ a 5 := by decide
    have hnd : ¬ 23 ^ 2 ∣ a 5 := by decide
    exact not_power_of_prime_div_not_sq_div 23 hp hd hnd b e hb he h_eq.symm
  · -- n = 6
    have hp : Nat.Prime 661 := by decide
    have hd : 661 ∣ a 6 := by decide
    have hnd : ¬ 661 ^ 2 ∣ a 6 := by decide
    exact not_power_of_prime_div_not_sq_div 661 hp hd hnd b e hb he h_eq.symm
  · -- n ≥ 7
    rcases n with _ | _ | _ | n
    · -- n = 7
      have hp : Nat.Prime 13 := by decide
      have hd : 13 ∣ a 7 := by decide
      have hnd : ¬ 13 ^ 2 ∣ a 7 := by decide
      exact not_power_of_prime_div_not_sq_div 13 hp hd hnd b e hb he h_eq.symm
    · -- n = 8
      have hp : Nat.Prime 733 := by decide
      have hd : 733 ∣ a 8 := by decide
      have hnd : ¬ 733 ^ 2 ∣ a 8 := by decide
      exact not_power_of_prime_div_not_sq_div 733 hp hd hnd b e hb he h_eq.symm
    · -- n = 9
      have hp : Nat.Prime 113 := by decide
      have hd : 113 ∣ a 9 := by decide
      have hnd : ¬ 113 ^ 2 ∣ a 9 := by decide
      exact not_power_of_prime_div_not_sq_div 113 hp hd hnd b e hb he h_eq.symm
    · -- n ≥ 10
      rcases n with _ | n
      · -- n = 10
        have hp : Nat.Prime 11069 := by norm_num
        have h_split : a 10 = 1 + 2 ^ 362880 + Finset.sum (Finset.range 8) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (10 - i - 2))) := by
          have h_split' := a_split 10 (by decide)
          rw [h_split']
          rfl
        have hd : 11069 ∣ a 10 := by
          rw [h_split]
          apply Nat.dvd_of_mod_eq_zero
          rw [Nat.add_mod (1 + 2 ^ 362880)]
          rw [Nat.add_mod 1 (2 ^ 362880)]
          rw [pow_362880_mod, sum_10_mod]
        have hnd : ¬ 11069 ^ 2 ∣ a 10 := by
          change ¬ 122522761 ∣ a 10
          rw [h_split]
          intro h_div
          have h_mod := Nat.mod_eq_zero_of_dvd h_div
          rw [Nat.add_mod (1 + 2 ^ 362880)] at h_mod
          rw [Nat.add_mod 1 (2 ^ 362880)] at h_mod
          rw [pow_362880_sq_mod, sum_10_sq_mod] at h_mod
          revert h_mod
          decide
        exact not_power_of_prime_div_not_sq_div 11069 hp hd hnd b e hb he h_eq.symm
      · -- n ≥ 11
        have hb3 : (b ^ e) % 3 = 2 := by
          have h_mod := a_mod_three (n + 11) (by omega)
          rw [h_eq] at h_mod
          exact h_mod
        have hb5 : (b ^ e) % 5 = 4 := by
          have h_mod := a_mod_five (n + 11) (by omega)
          rw [h_eq] at h_mod
          exact h_mod
        have hb8 : (b ^ e) % 8 = 1 := by
          have h_mod := a_mod_eight (n + 11) (by omega)
          rw [h_eq] at h_mod
          exact h_mod
        have he_odd : e % 2 = 1 := odd_of_pow_mod_three_eq_two b e hb3
        have h_b_ge_89 : b ≥ 89 := b_ge_89 b e hb he_odd hb3 hb5 hb8
        let p := e.minFac
        have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
        have hp_dvd_e : p ∣ e := Nat.minFac_dvd e
        have hp_odd : p % 2 = 1 := by
          have : e % 2 = 1 := he_odd
          obtain ⟨k, hk⟩ := hp_dvd_e
          rw [hk] at this
          rw [Nat.mul_mod] at this
          have h_mod : p % 2 = 0 ∨ p % 2 = 1 := by omega
          rcases h_mod with h_zero | h_one
          · rw [h_zero] at this
            simp at this
          · exact h_one
        have hp_ge_3 : p ≥ 3 := by
          have : p ≥ 2 := hp_prime.two_le
          omega
        have h_div : e = p * (e / p) := (Nat.mul_div_cancel' hp_dvd_e).symm
        have h_B_eq : b ^ e = (b ^ (e / p)) ^ p := by
          nth_rewrite 1 [h_div]
          have : p * (e / p) = (e / p) * p := Nat.mul_comm p (e / p)
          rw [this]
          rw [pow_mul]
        have hep_pos : e / p > 0 := by
          by_contra h_zero
          have h_zero' : e / p = 0 := Nat.le_zero.mp (by omega)
          have h_div_zero : e = 0 := by
            rw [h_div, h_zero', Nat.mul_zero]
          omega
        have h_B_ge : (b ^ (e / p)) ≥ 89 := by
          have : e / p = 1 + (e / p - 1) := by omega
          rw [this, pow_add]
          have h_pow1 : (b ^ 1) = b := by ring
          rw [h_pow1]
          calc
            b * b ^ (e / p - 1) ≥ 89 * 1 := Nat.mul_le_mul h_b_ge_89 (one_le_pow b (e / p - 1) (by omega))
            _ = 89 := by ring
        have h_split_a : a (n + 11) = 1 + 2 ^ (n + 10).factorial + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) := by
          have h_split' := a_split (n + 11) (by omega)
          rw [h_split']
          have h_one_pow : 1 ^ (n + 11).factorial = 1 := Nat.one_pow _
          rw [h_one_pow]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          congr 2
          omega
        have h_a_gt : a (n + 11) > 2 ^ (n + 10).factorial := by
          rw [h_split_a]
          omega
        have h_fac_ge : (n + 8).factorial ≥ n + 10 := by
          have h1 : (n + 8).factorial = (n + 8) * (n + 7).factorial := rfl
          have h2 : (n + 7).factorial ≥ 2 := by
            have : n + 7 ≥ 2 := by omega
            have h3 := Nat.factorial_le this
            have h4 : Nat.factorial 2 = 2 := rfl
            rw [h4] at h3
            exact h3
          rw [h1]
          calc
            (n + 8) * (n + 7).factorial ≥ (n + 8) * 2 := Nat.mul_le_mul_left _ h2
            _ = 2 * n + 16 := by ring
            _ ≥ n + 10 := by omega
        have h_pow_ge_fac : 2 ^ (n + 8).factorial ≥ n + 10 := by
          calc
            2 ^ (n + 8).factorial ≥ 2 ^ (n + 10) := Nat.pow_le_pow_right (by decide) h_fac_ge
            _ ≥ n + 10 := self_le_two_pow (n + 10)
        have h_fac_le := fact_le_pow_of_n n
        have h_fac_pow_le : (n + 11).factorial ^ (n + 8).factorial ≤ (2 ^ ((n + 10) * (n + 9) / 2)) ^ (n + 8).factorial := Nat.pow_le_pow_left h_fac_le (n + 8).factorial
        have h_fac_pow_le2 : (n + 11).factorial ^ (n + 8).factorial ≤ 2 ^ ((n + 10).factorial / 2) := by
          rw [← pow_mul] at h_fac_pow_le
          apply h_fac_pow_le.trans
          apply Nat.pow_le_pow_right (by decide)
          have h_dvd : 2 ∣ (n + 10) * (n + 9) := by
            have : (n + 10) * (n + 9) = (n + 9) * (n + 9 + 1) := by ring
            rw [this]
            exact even_iff_two_dvd.mp (Nat.even_mul_succ_self (n + 9))
          have h_alg : ((n + 10) * (n + 9) / 2) * (n + 8).factorial = (n + 10).factorial / 2 := by
            have : ((n + 10) * (n + 9) / 2) * (n + 8).factorial = ((n + 10) * (n + 9) * (n + 8).factorial) / 2 := by
              rw [Nat.mul_comm]
              rw [← Nat.mul_div_assoc (n + 8).factorial h_dvd]
              rw [Nat.mul_comm (n + 8).factorial]
            rw [this]
            congr 1
            have : (n + 8).factorial * ((n + 10) * (n + 9)) = (n + 10).factorial := by
              have h1 : (n + 10).factorial = (n + 10) * (n + 9).factorial := rfl
              have h2 : (n + 9).factorial = (n + 9) * (n + 8).factorial := rfl
              rw [h1, h2]
              ring
            rw [← this]
            ring
          rw [h_alg]
        have h_term2_le : (n + 8) * (n + 11).factorial ^ (n + 8).factorial ≤ (n + 8) * 2 ^ ((n + 10).factorial / 2) := Nat.mul_le_mul_left _ h_fac_pow_le2
        have h_term1_lt := helper_term1 n
        have h_sum_le := sum_le_better n
        have h_sum_lt : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) < (n + 9) * 2 ^ ((n + 10).factorial / 2) := by
          calc
            Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial)
              ≤ 6 ^ (n + 9).factorial + (n + 8) * (n + 11).factorial ^ (n + 8).factorial := h_sum_le
            _ < 2 ^ ((n + 10).factorial / 2) + (n + 8) * (n + 11).factorial ^ (n + 8).factorial := Nat.add_lt_add_right h_term1_lt _
            _ ≤ 2 ^ ((n + 10).factorial / 2) + (n + 8) * 2 ^ ((n + 10).factorial / 2) := Nat.add_le_add_left h_term2_le _
            _ = (n + 9) * 2 ^ ((n + 10).factorial / 2) := by ring
        by_cases hp_le : p ≤ n + 10
        · have hp_dvd_fac : p ∣ (n + 10).factorial := hp_prime.dvd_factorial.mpr hp_le
          let q := (n + 10).factorial / p
          have h_pq : (n + 10).factorial = p * q := by
            rw [Nat.mul_comm]
            exact (Nat.div_mul_cancel hp_dvd_fac).symm
          by_cases h_cases : (b ^ (e / p)) ≤ 2 ^ q
          · have h_pow_le : (b ^ (e / p)) ^ p ≤ (2 ^ q) ^ p := Nat.pow_le_pow_left h_cases p
            have h_RHS : (2 ^ q) ^ p = 2 ^ (n + 10).factorial := by
              rw [← pow_mul, Nat.mul_comm, ← h_pq]
            rw [h_RHS] at h_pow_le
            rw [← h_B_eq] at h_pow_le
            rw [← h_eq] at h_pow_le
            exact (Nat.not_le.mpr h_a_gt) h_pow_le
          · have h_q_eq : q = (n + 10).factorial / p := by
              rw [h_pq]
              rw [Nat.mul_comm p q]
              rw [Nat.mul_div_cancel _ (by omega : p > 0)]
            have h_sub_eq : q * (p - 1) = (n + 10).factorial - (n + 10).factorial / p := by
              have h_alg : q * (p - 1) = p * q - q := by
                have : q * (p - 1) + q = q * p := by
                  induction q with
                  | zero => ring
                  | succ q ih =>
                    rw [Nat.succ_mul, Nat.succ_mul]
                    omega
                rw [Nat.mul_comm p q]
                omega
              rw [h_alg, ← h_pq, h_q_eq]
            have h_exp_ge : q * (p - 1) ≥ (n + 10).factorial / 2 + (n + 8).factorial := by
              rw [h_sub_eq]
              exact helper_exponent n p hp_ge_3
            have h_pow_succ : (2 ^ q + 1) ^ p ≥ (2 ^ q) ^ p + p * (2 ^ q) ^ (p - 1) := by
              apply pow_succ_ge
              omega
            have h_pow_succ2 : (2 ^ q + 1) ^ p ≥ 2 ^ (n + 10).factorial + p * 2 ^ (q * (p - 1)) := by
              have h_eq1 : (2 ^ q) ^ p = 2 ^ (n + 10).factorial := by
                rw [← pow_mul, Nat.mul_comm, h_pq]
              have h_eq2 : (2 ^ q) ^ (p - 1) = 2 ^ (q * (p - 1)) := by
                rw [← pow_mul]
              rw [h_eq1, h_eq2] at h_pow_succ
              exact h_pow_succ
            have h_LHS_ge : p * 2 ^ (q * (p - 1)) ≥ (3 * n + 30) * 2 ^ ((n + 10).factorial / 2) := by
              have h_pow_add : 2 ^ (q * (p - 1)) ≥ 2 ^ ((n + 10).factorial / 2) * 2 ^ (n + 8).factorial := by
                calc
                  2 ^ (q * (p - 1)) ≥ 2 ^ ((n + 10).factorial / 2 + (n + 8).factorial) := Nat.pow_le_pow_right (by decide) h_exp_ge
                  _ = 2 ^ ((n + 10).factorial / 2) * 2 ^ (n + 8).factorial := pow_add _ _ _
              have h_mul_le : p * 2 ^ (q * (p - 1)) ≥ p * (2 ^ ((n + 10).factorial / 2) * 2 ^ (n + 8).factorial) := Nat.mul_le_mul_left _ h_pow_add
              calc
                p * 2 ^ (q * (p - 1)) ≥ p * (2 ^ ((n + 10).factorial / 2) * 2 ^ (n + 8).factorial) := h_mul_le
                _ = (p * 2 ^ (n + 8).factorial) * 2 ^ ((n + 10).factorial / 2) := by ring
                _ ≥ (3 * (n + 10)) * 2 ^ ((n + 10).factorial / 2) := by
                  apply Nat.mul_le_mul_right
                  exact Nat.mul_le_mul hp_ge_3 h_pow_ge_fac
                _ = (3 * n + 30) * 2 ^ ((n + 10).factorial / 2) := by ring
            have h_LHS_gt_RHS : p * 2 ^ (q * (p - 1)) > 1 + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) := by
              have h_pow_pos : 2 ^ ((n + 10).factorial / 2) ≥ 1 := one_le_pow 2 ((n + 10).factorial / 2) (by decide)
              calc
                p * 2 ^ (q * (p - 1)) ≥ (3 * n + 30) * 2 ^ ((n + 10).factorial / 2) := h_LHS_ge
                _ = (n + 10) * 2 ^ ((n + 10).factorial / 2) + (2 * n + 20) * 2 ^ ((n + 10).factorial / 2) := by ring
                _ ≥ (n + 10) * 2 ^ ((n + 10).factorial / 2) + 20 * 1 := Nat.add_le_add_left (Nat.mul_le_mul (by omega) h_pow_pos) _
                _ = (n + 9) * 2 ^ ((n + 10).factorial / 2) + 2 ^ ((n + 10).factorial / 2) + 20 := by ring
                _ > (n + 9) * 2 ^ ((n + 10).factorial / 2) + 1 := by omega
                _ > Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) + 1 := Nat.add_lt_add_right h_sum_lt _
                _ = 1 + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) := by ring
            have h_B_pow_gt : (b ^ (e / p)) ^ p > a (n + 11) := by
              calc
                (b ^ (e / p)) ^ p ≥ (2 ^ q + 1) ^ p := Nat.pow_le_pow_left (by omega) p
                _ ≥ 2 ^ (n + 10).factorial + p * 2 ^ (q * (p - 1)) := h_pow_succ2
                _ > 2 ^ (n + 10).factorial + (1 + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial)) := Nat.add_lt_add_left h_LHS_gt_RHS _
                _ = 1 + 2 ^ (n + 10).factorial + Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) := by ring
                _ = a (n + 11) := h_split_a.symm
            rw [← h_B_eq] at h_B_pow_gt
            rw [h_eq] at h_B_pow_gt
            omega
        · have hp_gt : p ≥ n + 11 := by omega
          have hp_ndiv : ¬ p ∣ (n + 10).factorial := by
            rw [hp_prime.dvd_factorial]
            omega
          let q := (n + 10).factorial / p
          have h_pq_le : p * q ≤ (n + 10).factorial := Nat.mul_div_le (n + 10).factorial p
          have h_pq_ne : p * q ≠ (n + 10).factorial := by
            intro h_eq_fact
            have : p ∣ (n + 10).factorial := ⟨q, h_eq_fact.symm⟩
            exact hp_ndiv this
          have h_pq_lt : p * q < (n + 10).factorial := by omega
          have h_pq_sub_le : p * q + 1 ≤ (n + 10).factorial := by omega
          have h_B_gt_pow : (b ^ (e / p)) ^ p > 2 * (2 ^ q) ^ p := by
            calc
              (b ^ (e / p)) ^ p = a (n + 11) := by
                rw [← h_B_eq]
                exact h_eq.symm
              _ > 2 ^ (n + 10).factorial := h_a_gt
              _ ≥ 2 ^ (p * q + 1) := Nat.pow_le_pow_right (by decide) h_pq_sub_le
              _ = 2 * (2 ^ q) ^ p := by
                rw [pow_add, pow_one, ← pow_mul]
                ring
          have h_B_ge_q : (b ^ (e / p)) ≥ 2 ^ q + 1 := by
            by_contra h_cases
            have h_cases' : (b ^ (e / p)) ≤ 2 ^ q := by omega
            have h_pow_le : (b ^ (e / p)) ^ p ≤ (2 ^ q) ^ p := Nat.pow_le_pow_left h_cases' p
            have h_le_trans : (b ^ (e / p)) ^ p ≤ 2 * (2 ^ q) ^ p := by
              calc
                (b ^ (e / p)) ^ p ≤ (2 ^ q) ^ p := h_pow_le
                _ ≤ 2 * (2 ^ q) ^ p := by omega
            omega
          by_cases h_B_eq_q1 : (b ^ (e / p)) = 2 ^ q + 1
          · have h_B_mod3 : (b ^ (e / p)) % 3 = 2 := by
              have hb3_B : ((b ^ (e / p)) ^ p) % 3 = 2 := by
                rw [← h_B_eq]
                exact hb3
              exact b_mod_three_eq_two (b ^ (e / p)) p (by omega) hb3_B
            have h_B_mod5 : (b ^ (e / p)) % 5 = 4 := by
              have hb5_B : ((b ^ (e / p)) ^ p) % 5 = 4 := by
                rw [← h_B_eq]
                exact hb5
              exact b_mod_five_eq_four (b ^ (e / p)) p (by omega) hb5_B
            rw [h_B_eq_q1] at h_B_mod3
            rw [h_B_eq_q1] at h_B_mod5
            have h_q_mod3 : (2 ^ q) % 3 = 1 := by
              have : (2 ^ q + 1) % 3 = 2 := h_B_mod3
              omega
            have h_q_mod5 : (2 ^ q) % 5 = 3 := by
              have : (2 ^ q + 1) % 5 = 4 := h_B_mod5
              omega
            have h_q_even := q_even_of_two_pow_mod_three q h_q_mod3
            have h_q_odd := q_odd_of_two_pow_mod_five q h_q_mod5
            have h_contra : 0 = 1 := by
              rw [← h_q_even, h_q_odd]
            revert h_contra
            decide
          · -- b ^ (e / p) ≥ 2 ^ q + 2
            have h_B_ge_q2 : b ^ (e / p) ≥ 2 ^ q + 2 := by omega
            have h_B_mod3 : b ^ (e / p) % 3 = 2 := by
              have hb3_B : ((b ^ (e / p)) ^ p) % 3 = 2 := by
                rw [← h_B_eq]
                exact hb3
              exact b_mod_three_eq_two (b ^ (e / p)) p hp_odd hb3_B
            have h_B_mod5 : b ^ (e / p) % 5 = 4 := by
              have hb5_B : ((b ^ (e / p)) ^ p) % 5 = 4 := by
                rw [← h_B_eq]
                exact hb5
              exact b_mod_five_eq_four (b ^ (e / p)) p hp_odd hb5_B
            have h_B_mod8 : b ^ (e / p) % 8 = 1 := by
              have hb8_B : ((b ^ (e / p)) ^ p) % 8 = 1 := by
                rw [← h_B_eq]
                exact hb8
              exact b_mod_eight_eq_one (b ^ (e / p)) p hp_odd hb8_B
            have h_a_mod16 : a (n + 11) % 16 = 1 := by
              rw [h_split_a]
              have h_two : 2 ^ (n + 10).factorial % 16 = 0 := by
                have h_ge : (n + 10).factorial ≥ 4 := by
                  have : n + 10 ≥ 4 := by omega
                  have h_fac := Nat.factorial_le this
                  have h_fac24 : Nat.factorial 4 = 24 := rfl
                  rw [h_fac24] at h_fac
                  omega
                have h_pow : 2 ^ (n + 10).factorial = 16 * 2 ^ ((n + 10).factorial - 4) := by
                  have : (n + 10).factorial = 4 + ((n + 10).factorial - 4) := by omega
                  conv_lhs => rw [this]
                  rw [pow_add]
                  rfl
                rw [h_pow]
                simp only [Nat.mul_mod_right]
              have h_sum : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) % 16 = 0 := by
                apply Nat.mod_eq_zero_of_dvd
                apply Finset.dvd_sum
                intro i hi
                have hi_lt : i < n + 9 := Finset.mem_range.mp hi
                by_cases h_cases : i < n + 7
                · have h_even : 2 ∣ (i + 3).factorial := Nat.dvd_factorial (by omega) (by omega)
                  obtain ⟨k, hk⟩ := h_even
                  rw [hk, mul_pow]
                  have hm : (n + 9 - i).factorial ≥ 4 := by
                    have : n + 9 - i ≥ 3 := by omega
                    have h_sub := Nat.factorial_le this
                    have h_fac6 : Nat.factorial 3 = 6 := rfl
                    rw [h_fac6] at h_sub
                    omega
                  have h_div : 16 ∣ 2 ^ (n + 9 - i).factorial := by
                    have : (n + 9 - i).factorial = 4 + ((n + 9 - i).factorial - 4) := by omega
                    rw [this, pow_add]
                    exact dvd_mul_right 16 _
                  exact dvd_mul_of_dvd_left h_div _
                · have hi_eq : i = n + 7 ∨ i = n + 8 := by omega
                  rcases hi_eq with rfl | rfl
                  · have h_sub : n + 9 - (n + 7) = 2 := by omega
                    have h_sub_fact : (n + 9 - (n + 7)).factorial = 2 := by rw [h_sub]; rfl
                    rw [h_sub_fact]
                    simp only [pow_two]
                    have h_sub2 : n + 7 + 3 = n + 10 := by omega
                    have h_dvd : 4 ∣ (n + 10).factorial := Nat.dvd_factorial (by omega) (by omega)
                    obtain ⟨k, hk⟩ := h_dvd
                    rw [h_sub2, hk]
                    have : (4 * k) * (4 * k) = 16 * (k * k) := by ring
                    rw [this]
                    exact dvd_mul_right 16 _
                  · have h_sub : n + 9 - (n + 8) = 1 := by omega
                    have h_sub_fact : (n + 9 - (n + 8)).factorial = 1 := by rw [h_sub]; rfl
                    rw [h_sub_fact]
                    simp only [pow_one]
                    have h_sub3 : n + 8 + 3 = n + 11 := by omega
                    have h_term_eq : (n + 8 + 3).factorial = (n + 11).factorial := by rw [h_sub3]
                    rw [h_term_eq]
                    have h_dvd5 : 16 ∣ Nat.factorial 6 := by decide
                    have h_dvdn : Nat.factorial 6 ∣ (n + 11).factorial := Nat.factorial_dvd_factorial (by omega)
                    exact dvd_trans h_dvd5 h_dvdn
              rw [Nat.add_mod, h_sum]
              simp only [add_zero, Nat.mod_mod]
              rw [Nat.add_mod 1 (2 ^ (n + 10).factorial)]
              rw [h_two]
            have h_B_mod16_cases : b ^ (e / p) % 16 = 1 ∨ b ^ (e / p) % 16 = 9 := by
              have : b ^ (e / p) % 8 = 1 := h_B_mod8
              omega
            rcases h_B_mod16_cases with hB16_1 | hB16_9
            · have h_B_mod32 : b ^ (e / p) % 32 = 17 := chinese_remainder_X (b ^ (e / p)) h_B_mod3 h_B_mod5 hB16_1
              have h_a_mod32 : a (n + 11) % 32 = 1 := by
                rw [h_split_a]
                have h_two : 2 ^ (n + 10).factorial % 32 = 0 := by
                  have h_ge : (n + 10).factorial ≥ 5 := by
                    have : n + 10 ≥ 5 := by omega
                    have h_fac := Nat.factorial_le this
                    have h_fac120 : Nat.factorial 5 = 120 := rfl
                    rw [h_fac120] at h_fac
                    omega
                  have h_pow : 2 ^ (n + 10).factorial = 32 * 2 ^ ((n + 10).factorial - 5) := by
                    have : (n + 10).factorial = 5 + ((n + 10).factorial - 5) := by omega
                    conv_lhs => rw [this]
                    rw [pow_add]
                    rfl
                  rw [h_pow]
                  simp only [Nat.mul_mod_right]
                have h_sum : Finset.sum (Finset.range (n + 9)) (fun i => (i + 3).factorial ^ (n + 9 - i).factorial) % 32 = 0 := by
                  apply Nat.mod_eq_zero_of_dvd
                  apply Finset.dvd_sum
                  intro i hi
                  have hi_lt : i < n + 9 := Finset.mem_range.mp hi
                  by_cases h_cases : i < n + 7
                  · have h_even : 2 ∣ (i + 3).factorial := Nat.dvd_factorial (by omega) (by omega)
                    obtain ⟨k, hk⟩ := h_even
                    rw [hk, mul_pow]
                    have hm : (n + 9 - i).factorial ≥ 5 := by
                      have : n + 9 - i ≥ 3 := by omega
                      have h_sub := Nat.factorial_le this
                      have h_fac6 : Nat.factorial 3 = 6 := rfl
                      rw [h_fac6] at h_sub
                      omega
                    have h_div : 32 ∣ 2 ^ (n + 9 - i).factorial := by
                      have : (n + 9 - i).factorial = 5 + ((n + 9 - i).factorial - 5) := by omega
                      rw [this, pow_add]
                      exact dvd_mul_right 32 _
                    exact dvd_mul_of_dvd_left h_div _
                  · have hi_eq : i = n + 7 ∨ i = n + 8 := by omega
                    rcases hi_eq with rfl | rfl
                    · have h_sub : n + 9 - (n + 7) = 2 := by omega
                      have h_sub_fact : (n + 9 - (n + 7)).factorial = 2 := by rw [h_sub]; rfl
                      rw [h_sub_fact]
                      simp only [pow_two]
                      have h_sub2 : n + 7 + 3 = n + 10 := by omega
                      have h_dvd : 8 ∣ (n + 10).factorial := Nat.dvd_factorial (by omega) (by omega)
                      obtain ⟨k, hk⟩ := h_dvd
                      rw [h_sub2, hk]
                      have : (8 * k) * (8 * k) = 32 * (2 * k * k) := by ring
                      rw [this]
                      exact dvd_mul_right 32 _
                    · have h_sub : n + 9 - (n + 8) = 1 := by omega
                      have h_sub_fact : (n + 9 - (n + 8)).factorial = 1 := by rw [h_sub]; rfl
                      rw [h_sub_fact]
                      simp only [pow_one]
                      have h_sub3 : n + 8 + 3 = n + 11 := by omega
                      have h_term_eq : (n + 8 + 3).factorial = (n + 11).factorial := by rw [h_sub3]
                      rw [h_term_eq]
                      have h_dvd5 : 32 ∣ Nat.factorial 8 := by decide
                      have h_dvdn : Nat.factorial 8 ∣ (n + 11).factorial := Nat.factorial_dvd_factorial (by omega)
                      exact dvd_trans h_dvd5 h_dvdn
                rw [Nat.add_mod, h_sum]
                simp only [add_zero, Nat.mod_mod]
                rw [Nat.add_mod 1 (2 ^ (n + 10).factorial)]
                rw [h_two]
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
            · have h_mod_pow := mod_16_pow (b ^ (e / p)) p hp_odd hB16_9
              have h_B_pow_eq : (b ^ (e / p)) ^ p = a (n + 11) := by
                rw [← h_B_eq]
                exact h_eq.symm
              rw [h_B_pow_eq] at h_mod_pow
              rw [h_a_mod16] at h_mod_pow
              revert h_mod_pow
              decide


