import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-- Helper: if `2^48 = 1` in `ZMod p`, the covering congruence holds, `p > 1` and
    `p < k*2^m+1`, then `k*2^m+1` is not prime. -/
theorem not_prime_of (p k m : ℕ) (hp2 : (2:ZMod p)^48 = 1)
    (hcov : ((k : ZMod p)) * (2:ZMod p)^(m % 48) + 1 = 0)
    (hp1 : 1 < p) (hpk : p < k*2^m+1) : ¬ (k*2^m+1).Prime := by
  intro hpr
  haveI : NeZero p := ⟨by omega⟩
  have hdvd : p ∣ (k*2^m+1) := by
    have h0 : ((k*2^m+1 : ℕ) : ZMod p) = 0 := by
      push_cast
      have hper : (2:ZMod p)^m = (2:ZMod p)^(m%48) := by
        conv_lhs => rw [← Nat.div_add_mod m 48]
        rw [pow_add, pow_mul, hp2, one_pow, one_mul]
      rw [hper]; exact hcov
    exact (ZMod.natCast_eq_zero_iff _ p).mp h0
  rcases (hpr.eq_one_or_self_of_dvd p hdvd) with h | h
  · omega
  · omega

/-- The number `5292270077783 = a(473165) + 4` is a Sierpiński number, certified by the
    covering set `{3,5,7,13,17,241,97,257,673}` (period 48). -/
theorem sierp_witness : is_sierpinski_number 5292270077783 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro m hm
  have hNlb : 673 < 5292270077783 * 2^m + 1 := by
    have h2 : 2 ≤ 2^m := by
      calc (2:ℕ) = 2^1 := (pow_one 2).symm
        _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
    nlinarith
  have hcase : m % 48 = 0 ∨ m % 48 = 1 ∨ m % 48 = 2 ∨ m % 48 = 3 ∨ m % 48 = 4 ∨ m % 48 = 5 ∨ m % 48 = 6 ∨ m % 48 = 7 ∨ m % 48 = 8 ∨ m % 48 = 9 ∨ m % 48 = 10 ∨ m % 48 = 11 ∨ m % 48 = 12 ∨ m % 48 = 13 ∨ m % 48 = 14 ∨ m % 48 = 15 ∨ m % 48 = 16 ∨ m % 48 = 17 ∨ m % 48 = 18 ∨ m % 48 = 19 ∨ m % 48 = 20 ∨ m % 48 = 21 ∨ m % 48 = 22 ∨ m % 48 = 23 ∨ m % 48 = 24 ∨ m % 48 = 25 ∨ m % 48 = 26 ∨ m % 48 = 27 ∨ m % 48 = 28 ∨ m % 48 = 29 ∨ m % 48 = 30 ∨ m % 48 = 31 ∨ m % 48 = 32 ∨ m % 48 = 33 ∨ m % 48 = 34 ∨ m % 48 = 35 ∨ m % 48 = 36 ∨ m % 48 = 37 ∨ m % 48 = 38 ∨ m % 48 = 39 ∨ m % 48 = 40 ∨ m % 48 = 41 ∨ m % 48 = 42 ∨ m % 48 = 43 ∨ m % 48 = 44 ∨ m % 48 = 45 ∨ m % 48 = 46 ∨ m % 48 = 47 := by omega
  rcases hcase with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    first
    | exact not_prime_of 3 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 5 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 7 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 17 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 97 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 257 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)
    | exact not_prime_of 673 _ m (by decide) (by rw [h]; decide) (by norm_num) (by omega)

/--
Disproof of oeis_270994_conjecture_0.

The endpoints `a(n)` and `a(n)+28` are indeed Sierpiński numbers (covering set
`{3,5,7,13,17,241}`, period 24), but they are **not** always consecutive Sierpiński
numbers: for `n = 473165`, the intermediate value `a(473165)+4 = 5292270077783`
is itself a Sierpiński number (covering set `{3,5,7,13,17,241,97,257,673}`, period 48),
lying strictly between `a(473165)` and `a(473165)+28`.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
  is_sierpinski_number (a n) ∧
  is_sierpinski_number (a n + 28) ∧
  (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  obtain ⟨_, _, h3⟩ := h 473165
  have hk : a 473165 + 4 = 5292270077783 := by norm_num [a]
  apply h3 (a 473165 + 4) ?_ ?_ ?_
  · rw [hk]; exact sierp_witness
  · omega
  · omega
