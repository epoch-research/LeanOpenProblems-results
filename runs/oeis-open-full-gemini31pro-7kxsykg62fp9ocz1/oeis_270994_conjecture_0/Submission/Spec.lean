import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/--
oeis_270994_conjecture_0: Are a(n) and a(n) + 28 always consecutive Sierpiński numbers?

This conjecture asserts that for all $n$, $a(n)$ and $a(n)+28$ are Sierpiński numbers,
and there are no Sierpiński numbers strictly between them.
-/
theorem oeis_270994_conjecture_0 : ∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False) := by
  sorry

lemma zmod_pow_48 (p : ℕ) [Fact (p > 1)] (hp : (2 : ZMod p)^48 = 1) (m : ℕ) :
    (2 : ZMod p)^m = (2 : ZMod p)^(m % 48) := by
  have h : m = 48 * (m / 48) + m % 48 := (Nat.div_add_mod m 48).symm
  nth_rw 1 [h]
  rw [pow_add, pow_mul, hp, one_pow, one_mul]

def k_val : ℕ := 5292270077783

lemma is_composite (p : ℕ) [Fact (p > 1)] (hp_pow : (2 : ZMod p)^48 = 1)
    (m r : ℕ) (hr : m % 48 = r)
    (h_div : (k_val : ZMod p) * (2 : ZMod p)^r + 1 = 0) :
    p ∣ k_val * 2^m + 1 := by
  have : ((k_val * 2^m + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [zmod_pow_48 p hp_pow m, hr, h_div]
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp this

lemma not_prime_from_dvd (p m : ℕ) (h_dvd : p ∣ k_val * 2^m + 1)
    (hp1 : p > 1) (hp2 : p < k_val) : ¬ Nat.Prime (k_val * 2^m + 1) := by
  intro h_prime
  have := Nat.Prime.eq_one_or_self_of_dvd h_prime _ h_dvd
  rcases this with h1 | h2
  · linarith
  · have ht : 2^m ≥ 1 := Nat.one_le_two_pow
    nlinarith

set_option linter.unusedVariables false
lemma k_val_not_prime (m : ℕ) (hm : m > 0) : ¬ Nat.Prime (k_val * 2^m + 1) := by
  have h_cases : m % 48 < 48 := Nat.mod_lt m (by decide)
  generalize h_mod : m % 48 = r at h_cases
  interval_cases r
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 0 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (7 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 7
    · exact is_composite 7 (by decide) m 1 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 2 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 3 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 4 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (257 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 257
    · exact is_composite 257 (by decide) m 5 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 6 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 7 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 8 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (17 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 17
    · exact is_composite 17 (by decide) m 9 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 10 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 11 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 12 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (7 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 7
    · exact is_composite 7 (by decide) m 13 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 14 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 15 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 16 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (17 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 17
    · exact is_composite 17 (by decide) m 17 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 18 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 19 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 20 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (257 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 257
    · exact is_composite 257 (by decide) m 21 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 22 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 23 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 24 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (7 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 7
    · exact is_composite 7 (by decide) m 25 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 26 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 27 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 28 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (97 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 97
    · exact is_composite 97 (by decide) m 29 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 30 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 31 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 32 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (17 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 17
    · exact is_composite 17 (by decide) m 33 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 34 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 35 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 36 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (7 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 7
    · exact is_composite 7 (by decide) m 37 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 38 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 39 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 40 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (17 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 17
    · exact is_composite 17 (by decide) m 41 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 42 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 43 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 44 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (673 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 673
    · exact is_composite 673 (by decide) m 45 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (3 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 3
    · exact is_composite 3 (by decide) m 46 h_mod (by decide)
    · decide
    · decide
  · have h_fact : Fact (5 > 1) := ⟨by decide⟩
    apply not_prime_from_dvd 5
    · exact is_composite 5 (by decide) m 47 h_mod (by decide)
    · decide
    · decide

theorem oeis_270994_conjecture_0.disproof : ¬ (type_of% @oeis_270994_conjecture_0) := by
  intro h
  have hn := h 473165
  rcases hn with ⟨_, _, h3⟩
  apply h3 (a 473165 + 4)
  · unfold is_sierpinski_number
    refine ⟨by decide, by decide, ?_⟩
    intro m hm
    exact k_val_not_prime m hm
  · decide
  · decide
