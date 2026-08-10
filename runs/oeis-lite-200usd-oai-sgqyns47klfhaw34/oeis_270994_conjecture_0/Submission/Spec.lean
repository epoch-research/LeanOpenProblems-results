import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-- An intermediate value between the claimed consecutive Sierpiński numbers. -/
def badK : ℕ := a 473165 + 4

lemma badK_not_prime_of_periodic_dvd (p c m : ℕ) (hm : m % 48 = c)
    (hper : (2 : ZMod p) ^ 48 = 1)
    (hbase : ((badK : ZMod p) * (2 : ZMod p) ^ c + 1 = 0))
    (hp : 2 ≤ p) (hp_lt : p < badK * 1 + 1) : ¬ Nat.Prime (badK * 2^m + 1) := by
  have hm' : m = 48 * (m / 48) + c := by
    have h := Nat.div_add_mod m 48
    omega
  rw [hm']
  apply Nat.not_prime_of_dvd_of_lt (m := p)
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    change ((badK : ZMod p) * (2 : ZMod p) ^ (48 * (m / 48) + c) + 1 = 0)
    rw [pow_add, pow_mul, hper]
    simpa using hbase
  · exact hp
  · have hpow : 1 ≤ 2 ^ (48 * (m / 48) + c) := by
      exact Nat.succ_le_of_lt (pow_pos (by norm_num : (0:ℕ) < 2) _)
    calc
      p < badK * 1 + 1 := hp_lt
      _ ≤ badK * 2 ^ (48 * (m / 48) + c) + 1 := by nlinarith [hpow]

lemma badK_not_prime (m : ℕ) : ¬ Nat.Prime (badK * 2^m + 1) := by
  have hlt : m % 48 < 48 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 48
  · exact badK_not_prime_of_periodic_dvd 3 0 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 7 1 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 2 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 3 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 4 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 257 5 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 6 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 7 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 8 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 17 9 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 10 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 11 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 12 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 7 13 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 14 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 15 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 16 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 17 17 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 18 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 19 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 20 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 257 21 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 22 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 23 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 24 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 7 25 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 26 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 27 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 28 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 97 29 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 30 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 31 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 32 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 17 33 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 34 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 35 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 36 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 7 37 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 38 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 39 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 40 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 17 41 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 42 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 43 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 44 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 673 45 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 3 46 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)
  · exact badK_not_prime_of_periodic_dvd 5 47 m h (by decide) (by decide) (by norm_num) (by unfold badK a; norm_num)

lemma badK_is_sierpinski_number : is_sierpinski_number badK := by
  refine ⟨?_, ?_, ?_⟩
  · unfold badK a
    norm_num
  · unfold badK a
    norm_num
  · intro n hn
    exact badK_not_prime n

/--
oeis_270994_conjecture_0 is false: for `n = 473165`, the number `a n + 4`
is a Sierpiński number strictly between `a n` and `a n + 28`.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  have hbetween := (h 473165).2.2
  have hk : is_sierpinski_number (a 473165 + 4) := by
    simpa [badK] using badK_is_sierpinski_number
  exact hbetween (a 473165 + 4) hk (by norm_num [a]) (by norm_num [a])
