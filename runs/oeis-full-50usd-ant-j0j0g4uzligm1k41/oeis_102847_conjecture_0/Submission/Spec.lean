import FormalConjectures.Util.ProblemImports

/--
A102847: $a(0)=1$, $a(n) = a(n-1)^2 + 2$.
-/
def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

/-
oeis_102847_conjecture_0: Prime for a(1)=3, a(2)=11, a(4)=15131; semiprime for a(3) = 123 = 3 * 41, a(5) = 228947163 = 3 * 76315721.
a(6), added by Jonathan Vos Post, has 4 prime factors. a(7) = 41 * 811^2 * 106693969 * 317171188688357726699 * 8272236925540996054440172449761.
When is the next prime in the sequence?

Formalization: Does there exist a prime term after a(4)?
-/

/-! ### Supporting lemmas -/

lemma a_ge_one : ∀ n, 1 ≤ a n := by
  intro n
  induction n with
  | zero => simp [a]
  | succ k ih => simp only [a]; nlinarith [ih]

lemma a_succ (n : ℕ) : a (n + 1) = (a n) ^ 2 + 2 := rfl

lemma a_succ_gt (n : ℕ) : a n < a (n + 1) := by
  simp only [a]; nlinarith [a_ge_one n]

lemma a_mono : Monotone a :=
  monotone_nat_of_le_succ (fun n => (a_succ_gt n).le)

lemma a5_val : a 5 = 228947163 := by norm_num [a]

lemma a_ge_5_gt_3 {n : ℕ} (hn : 5 ≤ n) : 3 < a n := by
  have : a 5 ≤ a n := a_mono hn
  rw [a5_val] at this; omega

/-- If `x ≡ 2 (mod 3)` then `x^2 + 2 ≡ 0 (mod 3)`. -/
lemma step_2_to_0 (x : ℕ) (hx : x % 3 = 2) : (x ^ 2 + 2) % 3 = 0 := by
  have h := Nat.pow_mod x 2 3; rw [hx] at h; omega

/-- If `x ≡ 0 (mod 3)` then `x^2 + 2 ≡ 2 (mod 3)`. -/
lemma step_0_to_2 (x : ℕ) (hx : x % 3 = 0) : (x ^ 2 + 2) % 3 = 2 := by
  have h := Nat.pow_mod x 2 3; rw [hx] at h; omega

/-- The residues of `a` modulo `3`: odd-index terms are `≡ 0`, even-index terms `≡ 2`. -/
lemma a_mod3 : ∀ k, a (2 * k + 1) % 3 = 0 ∧ a (2 * k + 2) % 3 = 2 := by
  intro k
  induction k with
  | zero => constructor <;> norm_num [a]
  | succ m ih =>
    obtain ⟨_, h2⟩ := ih
    have h3 : a (2 * m + 3) % 3 = 0 := by
      have e2 : 2 * m + 3 = (2 * m + 2) + 1 := by ring
      rw [e2, a_succ]; exact step_2_to_0 _ h2
    refine ⟨?_, ?_⟩
    · have e : 2 * (m + 1) + 1 = (2 * m + 2) + 1 := by ring
      rw [e, a_succ]; exact step_2_to_0 _ h2
    · have e : 2 * (m + 1) + 2 = (2 * m + 3) + 1 := by ring
      rw [e, a_succ]; exact step_0_to_2 _ h3

/-- For odd `n ≥ 5`, `3 ∣ a n` and `a n > 3`, so `a n` is composite. -/
lemma odd_not_prime {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) : ¬ Nat.Prime (a n) := by
  intro hp
  obtain ⟨k, hk⟩ := ho
  have h3 : a n % 3 = 0 := by
    have := (a_mod3 k).1; rwa [← hk] at this
  have hdvd : 3 ∣ a n := Nat.dvd_of_mod_eq_zero h3
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h | h
  · norm_num at h
  · have : 3 < a n := a_ge_5_gt_3 hn; omega

/- ### Covering congruences for the even-index case

The map `x ↦ x² + 2` is eventually periodic modulo each prime `p`.  For the
primes `19`, `41`, `43` the orbit of `1` reaches `0` and then cycles, which
yields the congruences below.  They cover every even `n` outside the residues
`{2, 10, 20, 22} (mod 30)`. -/

/-- One step of the recurrence, taken modulo `p`. -/
lemma step_mod (p x r : ℕ) (h : x % p = r) : (x ^ 2 + 2) % p = (r ^ 2 + 2) % p := by
  have hx2 : x ^ 2 % p = r ^ 2 % p := by rw [Nat.pow_mod, h]
  rw [Nat.add_mod, hx2, ← Nat.add_mod]

/-- `19 ∣ a n` whenever `n ≡ 0 (mod 3)` and `n ≥ 6`.  The orbit modulo `19`
cycles `0, 2, 6` from index `6` on. -/
lemma cover19 (m : ℕ) : a (6 + 3 * m) % 19 = 0 := by
  suffices key : ∀ k, a (6 + 3 * k) % 19 = 0 ∧ a (7 + 3 * k) % 19 = 2 ∧
      a (8 + 3 * k) % 19 = 6 from (key m).1
  intro k
  induction k with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> norm_num [a]
  | succ j ih =>
    obtain ⟨_, _, h2⟩ := ih
    have e0 : 6 + 3 * (j + 1) = (8 + 3 * j) + 1 := by ring
    have g0 : a (6 + 3 * (j + 1)) % 19 = 0 := by
      rw [e0, a_succ, step_mod 19 _ 6 h2]; decide
    have e1 : 7 + 3 * (j + 1) = (6 + 3 * (j + 1)) + 1 := by ring
    have g1 : a (7 + 3 * (j + 1)) % 19 = 2 := by
      rw [e1, a_succ, step_mod 19 _ 0 g0]; decide
    have e2 : 8 + 3 * (j + 1) = (7 + 3 * (j + 1)) + 1 := by ring
    have g2 : a (8 + 3 * (j + 1)) % 19 = 6 := by
      rw [e2, a_succ, step_mod 19 _ 2 g1]; decide
    exact ⟨g0, g1, g2⟩

/-- `41 ∣ a n` whenever `n ≡ 3 (mod 5)` and `n ≥ 3`.  The orbit modulo `41`
cycles `0, 2, 6, 38, 11` from index `3` on. -/
lemma cover41 (m : ℕ) : a (3 + 5 * m) % 41 = 0 := by
  suffices key : ∀ k, a (3 + 5 * k) % 41 = 0 ∧ a (4 + 5 * k) % 41 = 2 ∧
      a (5 + 5 * k) % 41 = 6 ∧ a (6 + 5 * k) % 41 = 38 ∧ a (7 + 5 * k) % 41 = 11 from
    (key m).1
  intro k
  induction k with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [a]
  | succ j ih =>
    obtain ⟨_, _, _, _, h4⟩ := ih
    have e0 : 3 + 5 * (j + 1) = (7 + 5 * j) + 1 := by ring
    have g0 : a (3 + 5 * (j + 1)) % 41 = 0 := by rw [e0, a_succ, step_mod 41 _ 11 h4]; decide
    have e1 : 4 + 5 * (j + 1) = (3 + 5 * (j + 1)) + 1 := by ring
    have g1 : a (4 + 5 * (j + 1)) % 41 = 2 := by rw [e1, a_succ, step_mod 41 _ 0 g0]; decide
    have e2 : 5 + 5 * (j + 1) = (4 + 5 * (j + 1)) + 1 := by ring
    have g2 : a (5 + 5 * (j + 1)) % 41 = 6 := by rw [e2, a_succ, step_mod 41 _ 2 g1]; decide
    have e3 : 6 + 5 * (j + 1) = (5 + 5 * (j + 1)) + 1 := by ring
    have g3 : a (6 + 5 * (j + 1)) % 41 = 38 := by rw [e3, a_succ, step_mod 41 _ 6 g2]; decide
    have e4 : 7 + 5 * (j + 1) = (6 + 5 * (j + 1)) + 1 := by ring
    have g4 : a (7 + 5 * (j + 1)) % 41 = 11 := by rw [e4, a_succ, step_mod 41 _ 38 g3]; decide
    exact ⟨g0, g1, g2, g3, g4⟩

/-- `43 ∣ a n` whenever `n ≡ 1 (mod 5)` and `n ≥ 6`.  The orbit modulo `43`
cycles `0, 2, 6, 38, 27` from index `6` on. -/
lemma cover43 (m : ℕ) : a (6 + 5 * m) % 43 = 0 := by
  suffices key : ∀ k, a (6 + 5 * k) % 43 = 0 ∧ a (7 + 5 * k) % 43 = 2 ∧
      a (8 + 5 * k) % 43 = 6 ∧ a (9 + 5 * k) % 43 = 38 ∧ a (10 + 5 * k) % 43 = 27 from
    (key m).1
  intro k
  induction k with
  | zero => refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [a]
  | succ j ih =>
    obtain ⟨_, _, _, _, h4⟩ := ih
    have e0 : 6 + 5 * (j + 1) = (10 + 5 * j) + 1 := by ring
    have g0 : a (6 + 5 * (j + 1)) % 43 = 0 := by rw [e0, a_succ, step_mod 43 _ 27 h4]; decide
    have e1 : 7 + 5 * (j + 1) = (6 + 5 * (j + 1)) + 1 := by ring
    have g1 : a (7 + 5 * (j + 1)) % 43 = 2 := by rw [e1, a_succ, step_mod 43 _ 0 g0]; decide
    have e2 : 8 + 5 * (j + 1) = (7 + 5 * (j + 1)) + 1 := by ring
    have g2 : a (8 + 5 * (j + 1)) % 43 = 6 := by rw [e2, a_succ, step_mod 43 _ 2 g1]; decide
    have e3 : 9 + 5 * (j + 1) = (8 + 5 * (j + 1)) + 1 := by ring
    have g3 : a (9 + 5 * (j + 1)) % 43 = 38 := by rw [e3, a_succ, step_mod 43 _ 6 g2]; decide
    have e4 : 10 + 5 * (j + 1) = (9 + 5 * (j + 1)) + 1 := by ring
    have g4 : a (10 + 5 * (j + 1)) % 43 = 27 := by rw [e4, a_succ, step_mod 43 _ 38 g3]; decide
    exact ⟨g0, g1, g2, g3, g4⟩

/-- A divisor `p` with `3 < p < a n` makes `a n` composite. -/
lemma not_prime_of_cover {n p : ℕ} (hp3 : 3 < p) (hpn : p < a n)
    (hdvd : p ∣ a n) : ¬ Nat.Prime (a n) := by
  intro hpr
  rcases (Nat.Prime.eq_one_or_self_of_dvd hpr p hdvd) with h | h <;> omega

theorem oeis_102847_conjecture_0.disproof :
    ¬ ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  rintro ⟨n, hn, hp⟩
  rcases Nat.even_or_odd n with he | ho
  · -- EVEN-INDEX CASE.  `n` is even and `n ≥ 6`.
    obtain ⟨t, ht⟩ := he
    have hbig : 228947163 ≤ a n := by
      have h := a_mono (show 5 ≤ n by omega); rwa [a5_val] at h
    by_cases h3 : n % 3 = 0
    · -- `n ≡ 0 (mod 3)`, `n ≥ 6`: `19 ∣ a n`.
      obtain ⟨m, hm⟩ : ∃ m, n = 6 + 3 * m := ⟨(n - 6) / 3, by omega⟩
      have hdvd : 19 ∣ a n := by rw [hm]; exact Nat.dvd_of_mod_eq_zero (cover19 m)
      exact (not_prime_of_cover (by norm_num) (by omega) hdvd) hp
    · by_cases h5a : n % 5 = 3
      · -- `n ≡ 3 (mod 5)`: `41 ∣ a n`.
        obtain ⟨m, hm⟩ : ∃ m, n = 3 + 5 * m := ⟨(n - 3) / 5, by omega⟩
        have hdvd : 41 ∣ a n := by rw [hm]; exact Nat.dvd_of_mod_eq_zero (cover41 m)
        exact (not_prime_of_cover (by norm_num) (by omega) hdvd) hp
      · by_cases h5b : n % 5 = 1
        · -- `n ≡ 1 (mod 5)`, `n ≥ 6`: `43 ∣ a n`.
          obtain ⟨m, hm⟩ : ∃ m, n = 6 + 5 * m := ⟨(n - 6) / 5, by omega⟩
          have hdvd : 43 ∣ a n := by rw [hm]; exact Nat.dvd_of_mod_eq_zero (cover43 m)
          exact (not_prime_of_cover (by norm_num) (by omega) hdvd) hp
        · -- Remaining residues `n ≡ 2, 10, 20, 22 (mod 30)` (and `n ≡ 4 mod 5`).
          -- These are the genuinely open Bunyakovsky-type cases.
          sorry
  · -- ODD-INDEX CASE: 3 ∣ a n and a n > 3, hence a n is composite.
    exact odd_not_prime (by omega) ho hp
