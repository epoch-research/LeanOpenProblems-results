import FormalConjectures.Util.ProblemImports
open Function

/--
A212844: $a(n) = 2^{n+2} \bmod n$.
Since the OEIS sequence starts at $n=1$, the Lean function $a(n)$ returns the $(n+1)$-th term of the sequence.
The $(n+1)$-th term is calculated by substituting $n+1$ into $2^{n+2} \bmod n$.
-/
def a : ℕ → ℕ
| 0     => 0
| (n+1) => (2 ^ ((n + 1) + 2)) % (n + 1)

lemma even_mod {x y : ℕ} (hx : Even x) (hy : Even y) : Even (x % y) := by
  rw [Nat.even_iff] at hx ⊢
  have h2 : 2 ∣ y := by
    rcases hy with ⟨k, rfl⟩
    have : k + k = 2 * k := by omega
    rw [this]
    exact dvd_mul_right 2 k
  rw [Nat.mod_mod_of_dvd x h2]
  exact hx

lemma a_even_of_even (n : ℕ) (hn : Even n) : Even (a n) := by
  cases n with
  | zero =>
    simp [a]
  | succ n =>
    have h_a_def : a (n + 1) = (2 ^ (n + 3)) % (n + 1) := rfl
    rw [h_a_def]
    apply even_mod
    · have : n + 3 = (n + 2) + 1 := by omega
      rw [this, Nat.pow_succ]
      use 2 ^ (n + 2)
      ring
    · exact hn

lemma odd_of_a_eq_69 (n : ℕ) (h : a n = 69) : Odd n := by
  have h_not_even_n : ¬ Even n := by
    intro hen
    have he_a := a_even_of_even n hen
    rw [h] at he_a
    have h_not_even : ¬ Even 69 := by decide
    exact h_not_even he_a
  cases Nat.even_or_odd n with
  | inl h_even => exact (h_not_even_n h_even).elim
  | inr h_odd => exact h_odd

lemma gt_69_of_a_eq_69 (n : ℕ) (h : a n = 69) : n > 69 := by
  cases n with
  | zero =>
    simp [a] at h
  | succ n =>
    have h_a_def : a (n + 1) = (2 ^ (n + 3)) % (n + 1) := rfl
    rw [h_a_def] at h
    have h_lt : (2 ^ (n + 3)) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    omega

lemma not_dvd_prime_pow (p : ℕ) (hp : p > 1) (hc : Nat.Coprime p 2) (k : ℕ) : ¬ (p ∣ 2 ^ k) := by
  have h_coprime : Nat.Coprime p (2 ^ k) := Nat.Coprime.pow_right k hc
  intro h_dvd
  have h_gcd := Nat.Coprime.gcd_eq_one h_coprime
  rw [Nat.gcd_eq_left h_dvd] at h_gcd
  omega

lemma pow_mod_prime_of_a_eq_69 {n p : ℕ} (h : a n = 69) (hp : p ∣ n) : (2 ^ (n + 2)) % p = 69 % p := by
  have h_gt : n > 69 := gt_69_of_a_eq_69 n h
  cases n with
  | zero => omega
  | succ m =>
    have h_a_def : a (m + 1) = (2 ^ (m + 3)) % (m + 1) := rfl
    have h_eq : m + 3 = (m + 1) + 2 := by omega
    rw [h_a_def] at h
    have h_mod := (Nat.mod_mod_of_dvd (2 ^ (m + 3)) hp).symm
    rw [h_mod, h]

lemma p_ne_3_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (3 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_3 : 69 % 3 = 0 := by decide
  rw [h_69_3] at h_mod
  have h_dvd : 3 ∣ 2 ^ (n + 2) := Nat.dvd_of_mod_eq_zero h_mod
  exact not_dvd_prime_pow 3 (by decide) (by decide) (n + 2) h_dvd

lemma p_ne_23_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (23 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_23 : 69 % 23 = 0 := by decide
  rw [h_69_23] at h_mod
  have h_dvd : 23 ∣ 2 ^ (n + 2) := Nat.dvd_of_mod_eq_zero h_mod
  exact not_dvd_prime_pow 23 (by decide) (by decide) (n + 2) h_dvd

lemma even_of_even_mod_four {k : ℕ} (h : Even (k % 4)) : Even k := by
  have h_eq : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  rw [h_eq]
  rcases h with ⟨m, hm⟩
  use 2 * (k / 4) + m
  omega

lemma pow_two_mod_five_cases (k : ℕ) :
  (2 ^ k % 5 = 1 ∧ k % 4 = 0) ∨
  (2 ^ k % 5 = 2 ∧ k % 4 = 1) ∨
  (2 ^ k % 5 = 4 ∧ k % 4 = 2) ∨
  (2 ^ k % 5 = 3 ∧ k % 4 = 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h_mod : (2 ^ k * 2) % 5 = ((2 ^ k % 5) * 2) % 5 := Nat.mul_mod (2 ^ k) 2 5
    rw [h_mod]
    have h_lt : k % 4 < 4 := Nat.mod_lt k (by decide)
    rcases ih with ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
    · right; left; exact ⟨by rw [ih1], by omega⟩
    · right; right; left; exact ⟨by rw [ih1], by omega⟩
    · right; right; right; exact ⟨by rw [ih1], by omega⟩
    · left; exact ⟨by rw [ih1], by omega⟩

lemma even_of_pow_two_mod_five_eq_four (k : ℕ) (h : 2 ^ k % 5 = 4) : Even k := by
  have h_cases := pow_two_mod_five_cases k
  rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · have : Even (k % 4) := by use 1
    exact even_of_even_mod_four this
  · rw [h1] at h; omega

lemma p_ne_5_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (5 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_5 : 69 % 5 = 4 := by decide
  rw [h_69_5] at h_mod
  have h_even := even_of_pow_two_mod_five_eq_four (n + 2) h_mod
  have h_odd := odd_of_a_eq_69 n h
  have h_odd2 : Odd (n + 2) := by
    rcases h_odd with ⟨k, rfl⟩
    use k + 1
    omega
  rcases h_even with ⟨a, ha⟩
  rcases h_odd2 with ⟨b, hb⟩
  have : a + a = 2 * b + 1 := by omega
  omega


lemma pow_two_mod_seven_cases (k : ℕ) :
  2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h_mod : (2 ^ k * 2) % 7 = ((2 ^ k % 7) * 2) % 7 := Nat.mul_mod _ _ _
    rw [h_mod]
    rcases ih with h1 | h1 | h1
    · rw [h1]; decide
    · rw [h1]; decide
    · rw [h1]; decide

lemma pow_two_mod_seven_ne_six (k : ℕ) : 2 ^ k % 7 ≠ 6 := by
  have h := pow_two_mod_seven_cases k
  rcases h with h1 | h1 | h1 <;> omega

lemma p_ne_7_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (7 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_7 : 69 % 7 = 6 := by decide
  rw [h_69_7] at h_mod
  have h_ne := pow_two_mod_seven_ne_six (n + 2)
  exact h_ne h_mod

lemma pow_two_mod_eleven_cases (k : ℕ) :
  (2 ^ k % 11 = 1 ∧ k % 10 = 0) ∨
  (2 ^ k % 11 = 2 ∧ k % 10 = 1) ∨
  (2 ^ k % 11 = 4 ∧ k % 10 = 2) ∨
  (2 ^ k % 11 = 8 ∧ k % 10 = 3) ∨
  (2 ^ k % 11 = 5 ∧ k % 10 = 4) ∨
  (2 ^ k % 11 = 10 ∧ k % 10 = 5) ∨
  (2 ^ k % 11 = 9 ∧ k % 10 = 6) ∨
  (2 ^ k % 11 = 7 ∧ k % 10 = 7) ∨
  (2 ^ k % 11 = 3 ∧ k % 10 = 8) ∨
  (2 ^ k % 11 = 6 ∧ k % 10 = 9) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h_mod : (2 ^ k * 2) % 11 = ((2 ^ k % 11) * 2) % 11 := Nat.mul_mod _ _ _
    rw [h_mod]
    have h_lt : k % 10 < 10 := Nat.mod_lt _ (by decide)
    rcases ih with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
    · right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; right; exact ⟨by rw [h1], by omega⟩
    · left; exact ⟨by rw [h1], by omega⟩

lemma even_of_even_mod_ten {k : ℕ} (h : k % 10 = 8) : Even k := by
  have h_eq : k = 10 * (k / 10) + k % 10 := (Nat.div_add_mod k 10).symm
  rw [h_eq, h]
  use 5 * (k / 10) + 4
  omega

lemma even_of_pow_two_mod_eleven_eq_three (k : ℕ) (h : 2 ^ k % 11 = 3) : Even k := by
  have h_cases := pow_two_mod_eleven_cases k
  rcases h_cases with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · exact even_of_even_mod_ten h2
  · rw [h1] at h; omega

lemma p_ne_11_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (11 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_11 : 69 % 11 = 3 := by decide
  rw [h_69_11] at h_mod
  have h_even := even_of_pow_two_mod_eleven_eq_three (n + 2) h_mod
  have h_odd := odd_of_a_eq_69 n h
  have h_odd2 : Odd (n + 2) := by
    rcases h_odd with ⟨k, rfl⟩
    use k + 1
    omega
  rcases h_even with ⟨a, ha⟩
  rcases h_odd2 with ⟨b, hb⟩
  have : a + a = 2 * b + 1 := by omega
  omega

lemma pow_two_mod_thirteen_cases (k : ℕ) :
  (2 ^ k % 13 = 1 ∧ k % 12 = 0) ∨
  (2 ^ k % 13 = 2 ∧ k % 12 = 1) ∨
  (2 ^ k % 13 = 4 ∧ k % 12 = 2) ∨
  (2 ^ k % 13 = 8 ∧ k % 12 = 3) ∨
  (2 ^ k % 13 = 3 ∧ k % 12 = 4) ∨
  (2 ^ k % 13 = 6 ∧ k % 12 = 5) ∨
  (2 ^ k % 13 = 12 ∧ k % 12 = 6) ∨
  (2 ^ k % 13 = 11 ∧ k % 12 = 7) ∨
  (2 ^ k % 13 = 9 ∧ k % 12 = 8) ∨
  (2 ^ k % 13 = 5 ∧ k % 12 = 9) ∨
  (2 ^ k % 13 = 10 ∧ k % 12 = 10) ∨
  (2 ^ k % 13 = 7 ∧ k % 12 = 11) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h_mod : (2 ^ k * 2) % 13 = ((2 ^ k % 13) * 2) % 13 := Nat.mul_mod _ _ _
    rw [h_mod]
    have h_lt : k % 12 < 12 := Nat.mod_lt _ (by decide)
    rcases ih with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
    · right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; right; right; right; right; exact ⟨by rw [h1], by omega⟩
    · left; exact ⟨by rw [h1], by omega⟩

lemma even_of_even_mod_twelve {k : ℕ} (h : k % 12 = 2) : Even k := by
  have h_eq : k = 12 * (k / 12) + k % 12 := (Nat.div_add_mod k 12).symm
  rw [h_eq, h]
  use 6 * (k / 12) + 1
  omega

lemma even_of_pow_two_mod_thirteen_eq_four (k : ℕ) (h : 2 ^ k % 13 = 4) : Even k := by
  have h_cases := pow_two_mod_thirteen_cases k
  rcases h_cases with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · exact even_of_even_mod_twelve h2
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega

lemma p_ne_13_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (13 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_13 : 69 % 13 = 4 := by decide
  rw [h_69_13] at h_mod
  have h_even := even_of_pow_two_mod_thirteen_eq_four (n + 2) h_mod
  have h_odd := odd_of_a_eq_69 n h
  have h_odd2 : Odd (n + 2) := by
    rcases h_odd with ⟨k, rfl⟩
    use k + 1
    omega
  rcases h_even with ⟨a, ha⟩
  rcases h_odd2 with ⟨b, hb⟩
  have : a + a = 2 * b + 1 := by omega
  omega

lemma pow_two_mod_seventeen_cases (k : ℕ) :
  (2 ^ k % 17 = 1 ∧ k % 8 = 0) ∨
  (2 ^ k % 17 = 2 ∧ k % 8 = 1) ∨
  (2 ^ k % 17 = 4 ∧ k % 8 = 2) ∨
  (2 ^ k % 17 = 8 ∧ k % 8 = 3) ∨
  (2 ^ k % 17 = 16 ∧ k % 8 = 4) ∨
  (2 ^ k % 17 = 15 ∧ k % 8 = 5) ∨
  (2 ^ k % 17 = 13 ∧ k % 8 = 6) ∨
  (2 ^ k % 17 = 9 ∧ k % 8 = 7) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h_mod : (2 ^ k * 2) % 17 = ((2 ^ k % 17) * 2) % 17 := Nat.mul_mod _ _ _
    rw [h_mod]
    have h_lt : k % 8 < 8 := Nat.mod_lt _ (by decide)
    rcases ih with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
    · right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; left; exact ⟨by rw [h1], by omega⟩
    · right; right; right; right; right; right; right; exact ⟨by rw [h1], by omega⟩
    · left; exact ⟨by rw [h1], by omega⟩

lemma even_of_even_mod_eight {k : ℕ} (h : k % 8 = 0) : Even k := by
  have h_eq : k = 8 * (k / 8) + k % 8 := (Nat.div_add_mod k 8).symm
  rw [h_eq, h]
  use 4 * (k / 8)
  omega

lemma even_of_pow_two_mod_seventeen_eq_one (k : ℕ) (h : 2 ^ k % 17 = 1) : Even k := by
  have h_cases := pow_two_mod_seventeen_cases k
  rcases h_cases with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
  · exact even_of_even_mod_eight h2
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega
  · rw [h1] at h; omega

lemma p_ne_17_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (17 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_69_17 : 69 % 17 = 1 := by decide
  rw [h_69_17] at h_mod
  have h_even := even_of_pow_two_mod_seventeen_eq_one (n + 2) h_mod
  have h_odd := odd_of_a_eq_69 n h
  have h_odd2 : Odd (n + 2) := by
    rcases h_odd with ⟨k, rfl⟩
    use k + 1
    omega
  rcases h_even with ⟨a, ha⟩
  rcases h_odd2 with ⟨b, hb⟩
  have : a + a = 2 * b + 1 := by omega
  omega


lemma pow_mod_step (a p B q r : ℕ) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (B * q + r) ≡ a ^ r [MOD p] := by
  rw [Nat.pow_add, Nat.pow_mul]
  have h1 : (a ^ B) ^ q ≡ 1 ^ q [MOD p] := Nat.ModEq.pow q hB
  simp only [one_pow] at h1
  have h2 : (a ^ B) ^ q * a ^ r ≡ 1 * a ^ r [MOD p] := Nat.ModEq.mul h1 Nat.ModEq.rfl
  rw [one_mul] at h2
  exact h2

lemma pow_mod_rem (a p A B : ℕ) (hA : a ^ A ≡ 1 [MOD p]) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (A % B) ≡ 1 [MOD p] := by
  have h_eq : A = B * (A / B) + A % B := (Nat.div_add_mod A B).symm
  have h_step := pow_mod_step a p B (A / B) (A % B) hB
  rw [← h_eq] at h_step
  exact h_step.symm.trans hA

theorem pow_mod_gcd (a p A B : ℕ) (hA : a ^ A ≡ 1 [MOD p]) (hB : a ^ B ≡ 1 [MOD p]) :
    a ^ (Nat.gcd A B) ≡ 1 [MOD p] := by
  by_cases hA_zero : A = 0
  · subst hA_zero
    rw [Nat.gcd_zero_left]
    exact hB
  · rw [Nat.gcd_rec]
    have h_rem := pow_mod_rem a p B A hB hA
    exact pow_mod_gcd a p (B % A) A h_rem hA
termination_by A
decreasing_by exact Nat.mod_lt B (Nat.pos_of_ne_zero hA_zero)

lemma gcd_g_n_eq_one {g n p : ℕ} (hp : p.Prime) (hg : g ∣ p - 1)
    (h_smallest : ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q) : Nat.gcd g n = 1 := by
  by_contra hc
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hc
  have hq_g : q ∣ g := hq_dvd.trans (Nat.gcd_dvd_left g n)
  have hq_n : q ∣ n := hq_dvd.trans (Nat.gcd_dvd_right g n)
  have hq_p1 : q ∣ p - 1 := hq_g.trans hg
  have h_p1_pos : p - 1 > 0 := by
    have : p ≥ 2 := hp.two_le
    omega
  have hq_le_p1 : q ≤ p - 1 := Nat.le_of_dvd h_p1_pos hq_p1
  have hq_lt_p : q < p := by omega
  have hq_ge_p : p ≤ q := h_smallest q hq_prime hq_n
  omega

lemma pow_mod_flt (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    2 ^ k ≡ 2 ^ (k % (p - 1)) [MOD p] := by
  have h_coprime : Nat.Coprime 2 p := by
    have h1 : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
      have hp_ge : p ≥ 2 := hp.two_le
      omega
    exact h1.symm
  have h_flt := Nat.ModEq.pow_card_sub_one_eq_one hp h_coprime
  have h_eq : k = (p - 1) * (k / (p - 1)) + k % (p - 1) := (Nat.div_add_mod k (p - 1)).symm
  have h_step := pow_mod_step 2 p (p - 1) (k / (p - 1)) (k % (p - 1)) h_flt
  rw [← h_eq] at h_step
  exact h_step

lemma mod_19_cases (k : ℕ) (h : 2 ^ k % 19 = 69 % 19) : k % 18 = 15 := by
  have h_flt := pow_mod_flt 19 k (by decide) (by decide)
  rw [Nat.ModEq] at h_flt
  rw [h_flt] at h
  have h_lt : k % 18 < 18 := Nat.mod_lt _ (by decide)
  generalize k % 18 = r at h_lt h
  revert r h_lt h
  decide


set_option exponentiation.threshold 1000


lemma pow_mod_361 (x : ℕ) (hx : x % 18 = 13) : 2 ^ (361 * x + 2) % 361 = 145 := by
  have h_eq : 361 * x + 2 = 342 * (19 * (x / 18) + 13) + 249 := by
    have : x = 18 * (x / 18) + 13 := by
      have := Nat.div_add_mod x 18
      omega
    omega
  rw [h_eq]
  have hB : 2 ^ 342 ≡ 1 [MOD 361] := by
    change 2 ^ 342 % 361 = 1 % 361
    decide
  have h_step := pow_mod_step 2 361 342 (19 * (x / 18) + 13) 249 hB
  rw [Nat.ModEq] at h_step
  have h_249 : 2 ^ 249 % 361 = 145 := by decide
  rw [h_249] at h_step
  exact h_step


lemma p_ne_19_of_a_eq_69 {n : ℕ} (h : a n = 69) : ¬ (19 ∣ n) := by
  intro hp
  have h_mod := pow_mod_prime_of_a_eq_69 h hp
  have h_cases := mod_19_cases (n + 2) h_mod
  have hn_mod : n % 18 = 13 := by omega
  rcases hp with ⟨m, rfl⟩
  have hm_mod : m % 18 = 13 := by omega
  by_cases h_19_m : 19 ∣ m
  · rcases h_19_m with ⟨y, rfl⟩
    have hy_mod : y % 18 = 13 := by omega
    have h_pow := pow_mod_361 y hy_mod
    have h_dvd : 361 ∣ 19 * (19 * y) := by
      use y
      ring
    have h_mod361 := pow_mod_prime_of_a_eq_69 h h_dvd
    have h_eq361 : 19 * (19 * y) = 361 * y := by ring
    rw [h_eq361] at h_mod361
    have h_69 : 69 % 361 = 69 := by decide
    rw [h_69] at h_mod361
    rw [h_pow] at h_mod361
    contradiction
  · sorry

lemma not_a_eq_69_of_prime {n : ℕ} (hp : n.Prime) (hn : n ≥ 3700) : a n ≠ 69 := by
  intro h
  have h_gt : n > 69 := by omega
  have h_coprime : Nat.Coprime n 2 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    have : n ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have h_coprime2 : Nat.Coprime 2 n := h_coprime.symm
  have h_flt := Nat.ModEq.pow_card_sub_one_eq_one hp h_coprime2
  cases n with
  | zero => omega
  | succ m =>
    have h_flt_mod : 2 ^ m % (m + 1) = 1 := by
      have h_one_mod : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      have h_flt_succ : 2 ^ m % (m + 1) = 1 % (m + 1) := h_flt
      rw [h_one_mod] at h_flt_succ
      exact h_flt_succ
    have h_a_def : a (m + 1) = (2 ^ (m + 3)) % (m + 1) := rfl
    rw [h_a_def] at h
    have h_pow_eq : (2 ^ (m + 3) : ℕ) = 2 ^ m * 8 := by
      have h_pow_identity : (2 ^ (m + 3) : ℕ) = 2 ^ m * 2 ^ 3 := Nat.pow_add 2 m 3
      rw [h_pow_identity]
      ring
    rw [h_pow_eq] at h
    have h_mod_mul : (2 ^ m * 8) % (m + 1) = ((2 ^ m % (m + 1)) * (8 % (m + 1))) % (m + 1) := Nat.mul_mod (2 ^ m) 8 (m + 1)
    have h_8_mod_succ : 8 % (m + 1) = 8 := Nat.mod_eq_of_lt (by omega)
    rw [h_8_mod_succ] at h_mod_mul
    rw [h_mod_mul] at h
    rw [h_flt_mod] at h
    have h_8_mod : 8 % (m + 1) = 8 := Nat.mod_eq_of_lt (by omega)
    rw [one_mul] at h
    rw [h_8_mod] at h
    omega

def check_range_bin_fuel (fuel start len : ℕ) : Bool :=
  match fuel with
  | 0 => len == 0
  | f + 1 =>
    if len = 0 then true
    else if len = 1 then (a start != 69)
    else
      let half := len / 2
      check_range_bin_fuel f start half && check_range_bin_fuel f (start + half) (len - half)

lemma check_range_bin_fuel_correct (fuel start len : ℕ) (h_fuel : len ≤ 2 ^ fuel)
    (h : check_range_bin_fuel fuel start len = true) :
    ∀ i < len, a (start + i) ≠ 69 := by
  induction fuel generalizing start len with
  | zero =>
    unfold check_range_bin_fuel at h
    have : len = 0 := by
      cases len with
      | zero => rfl
      | succ n => simp at h
    subst this
    intro i hi
    omega
  | succ f ih =>
    by_cases h_len0 : len = 0
    · subst h_len0
      intro i hi
      omega
    · by_cases h_len1 : len = 1
      · subst h_len1
        intro i hi
        have : i = 0 := by omega
        subst this
        rw [Nat.add_zero]
        unfold check_range_bin_fuel at h
        simp [h_len0] at h
        intro hc
        rw [hc] at h
        contradiction
      · unfold check_range_bin_fuel at h
        simp [h_len0, h_len1] at h
        rcases h with ⟨h1, h2⟩
        have h_pow : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
        rw [h_pow] at h_fuel
        have h_eq_div : len = 2 * (len / 2) + len % 2 := (Nat.div_add_mod len 2).symm
        have h_mod_lt : len % 2 < 2 := Nat.mod_lt _ (by decide)
        have h_sub : len - len / 2 = len / 2 + len % 2 := by omega
        have h_half_lt : len / 2 ≤ 2 ^ f := by omega
        have h_rem_lt : len - len / 2 ≤ 2 ^ f := by omega
        intro i hi
        by_cases h_half : i < len / 2
        · exact ih start (len / 2) h_half_lt h1 i h_half
        · have h_rec := ih (start + len / 2) (len - len / 2) h_rem_lt h2 (i - len / 2) (by omega)
          have : start + len / 2 + (i - len / 2) = start + i := by omega
          rw [this] at h_rec
          exact h_rec

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000
theorem a_not_69_lt_100489 : ∀ n < 100489, a n ≠ 69 := by
  intro n hn
  have h_check : check_range_bin_fuel 20 0 100489 = true := by decide
  have h_corr := check_range_bin_fuel_correct 20 0 100489 (by decide) h_check n hn
  rw [Nat.zero_add] at h_corr
  exact h_corr

lemma minFac_sq_le_of_not_prime {n : ℕ} (h_comp : ¬ n.Prime) (h_gt1 : n > 1) :
    n.minFac * n.minFac ≤ n := by
  have h_dvd : n.minFac ∣ n := Nat.minFac_dvd n
  have h_eq : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' h_dvd).symm
  have h_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have h_div_gt1 : n / n.minFac > 1 := by
    by_contra hc
    have hc_le : n / n.minFac ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc_le with h0 | h1
    · have h_zero : n = 0 := by
        rw [h_eq, h0, mul_zero]
      omega
    · have h_eq_minfac : n = n.minFac := by
        calc n = n.minFac * (n / n.minFac) := h_eq
             _ = n.minFac * 1 := by rw [h1]
             _ = n.minFac := mul_one n.minFac
      rw [h_eq_minfac] at h_comp
      exact h_comp h_prime
  have h_minfac_le : n.minFac ≤ n / n.minFac := by
    have h_div_dvd : n / n.minFac ∣ n := Nat.div_dvd_of_dvd h_dvd
    apply Nat.minFac_le_of_dvd (by omega) h_div_dvd
  have : n.minFac * n.minFac ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul_left n.minFac h_minfac_le
  rw [← h_eq] at this
  exact this

theorem a_not_69 (n : ℕ) : a n ≠ 69 := by
  have : n < 100489 ∨ n ≥ 100489 := by omega
  rcases this with h_lt | h_ge
  · exact a_not_69_lt_100489 n h_lt
  · intro hn_69
    by_cases hp : n.Prime
    · exact not_a_eq_69_of_prime hp (by omega) hn_69
    · -- composite n ≥ 100489
      sorry

theorem oeis_212844_conjecture_0_proof.disproof : ¬ (Surjective a = True) := by
  intro h
  have h2 : Surjective a := by
    rw [h]
    exact True.intro
  rcases h2 69 with ⟨n, hn⟩
  exact a_not_69 n hn


