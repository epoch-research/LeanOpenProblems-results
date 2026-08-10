import FormalConjectures.Util.ProblemImports

/--
A270994: $a(n) = 9454129 + 11184810 \cdot n$.
-/
def a (n : ℕ) : ℕ := 9454129 + 11184810 * n

/-- A natural number `k` is a Sierpiński number if it is odd, greater than 1,
    and for all positive natural numbers `n`, $k \cdot 2^n + 1$ is not a prime number. -/
def is_sierpinski_number (k : ℕ) : Prop :=
  k % 2 = 1 ∧ k > 1 ∧ ∀ n : ℕ, n > 0 → ¬ Nat.Prime (k * 2^n + 1)

/-- If `p ∣ s * 2 ^ e + 1`, `p ∣ 2 ^ m - 1` and `n ≡ e [MOD m]`,
then `p ∣ s * 2 ^ n + 1`. -/
private lemma dvd_of_mod_eq {p s m e : ℕ} (n : ℕ) (_hp : 2 ≤ p) (_hm : 0 < m)
    (hdvd : p ∣ s * 2 ^ e + 1) (hord : p ∣ 2 ^ m - 1) (hne : n % m = e) :
    p ∣ s * 2 ^ n + 1 := by
  haveI : NeZero p := ⟨by omega⟩
  have h2m : (2 : ZMod p) ^ m = 1 := by
    have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
    have h0 : ((2 ^ m - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hord
    have h2 : ((2 ^ m : ℕ) : ZMod p) - 1 = 0 := by
      rw [← Nat.cast_one (R := ZMod p), ← Nat.cast_sub h1, h0]
    push_cast at h2
    linear_combination h2
  have hn : n = m * (n / m) + e := by
    conv_lhs => rw [← Nat.div_add_mod n m, hne]
  have h2n : (2 : ZMod p) ^ n = (2 : ZMod p) ^ e := by
    rw [hn, pow_add, pow_mul, h2m, one_pow, one_mul]
  have he : ((s * 2 ^ e + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hgoal : ((s * 2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
    push_cast at he ⊢
    rw [h2n]
    exact he
  exact (ZMod.natCast_eq_zero_iff _ _).mp hgoal

/-- If a prime `p < s` satisfies the covering congruences, then `s * 2 ^ n + 1`
is not prime for `n ≡ e [MOD m]`. -/
private lemma not_prime_of_cover {p s m e : ℕ} (n : ℕ) (hp : 2 ≤ p) (hm : 0 < m)
    (hps : p < s) (hdvd : p ∣ s * 2 ^ e + 1) (hord : p ∣ 2 ^ m - 1)
    (hne : n % m = e) : ¬ Nat.Prime (s * 2 ^ n + 1) := by
  intro hprime
  have hd : p ∣ s * 2 ^ n + 1 := dvd_of_mod_eq n hp hm hdvd hord hne
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hlt : p < s * 2 ^ n + 1 := by nlinarith
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hd) with h | h <;> omega

/-- `1813934020268071832273` is a Sierpiński number: it is odd, greater than one,
and every `1813934020268071832273 * 2 ^ n + 1` is divisible by one of the primes
`3, 5, 17, 257, 65537, 97, 673, 193` according to a covering system modulo `96`. -/
private lemma sierpinski_witness : is_sierpinski_number 1813934020268071832273 := by
  refine ⟨by norm_num, by norm_num, fun n _ => ?_⟩
  have hcov : n % 2 = 0 ∨ n % 4 = 3 ∨ n % 8 = 1 ∨ n % 16 = 5 ∨ n % 32 = 29 ∨
      n % 48 = 45 ∨ n % 48 = 29 ∨ n % 96 = 13 := by omega
  rcases hcov with h | h | h | h | h | h | h | h
  · exact not_prime_of_cover (p := 3) (e := 0) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 5) (e := 3) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 17) (e := 1) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 257) (e := 5) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 65537) (e := 29) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 97) (e := 45) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 673) (e := 29) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h
  · exact not_prime_of_cover (p := 193) (e := 13) n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) h

/--
oeis_270994_conjecture_0 is false: for `n = 162178349052694`, the number
`a n + 4 = 1813934020268071832273` is a Sierpiński number lying strictly
between `a n` and `a n + 28`, so `a n` and `a n + 28` are not consecutive
Sierpiński numbers.
-/
theorem oeis_270994_conjecture_0.disproof : ¬ (∀ n : ℕ,
    is_sierpinski_number (a n) ∧
    is_sierpinski_number (a n + 28) ∧
    (∀ k : ℕ, is_sierpinski_number k → a n < k → k < a n + 28 → False)) := by
  intro h
  obtain ⟨-, -, h3⟩ := h 162178349052694
  exact h3 1813934020268071832273 sierpinski_witness (by norm_num [a]) (by norm_num [a])
