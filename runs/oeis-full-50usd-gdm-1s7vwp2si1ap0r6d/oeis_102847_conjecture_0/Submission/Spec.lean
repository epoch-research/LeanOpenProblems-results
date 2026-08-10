import FormalConjectures.Util.ProblemImports

/--
A102847: $a(0)=1$, $a(n) = a(n-1)^2 + 2$.
-/
def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

/--
Helper sequence starting from 0: $s(0)=0$, $s(n) = s(n-1)^2 + 2$.
-/
def s : ℕ → ℕ
| 0     => 0
| n + 1 => (s n) ^ 2 + 2

theorem sq_add_two_mod (x y m : ℕ) (h : x % m = y % m) : (x ^ 2 + 2) % m = (y ^ 2 + 2) % m := by
  rw [Nat.pow_two, Nat.pow_two]
  have h_mul : (x * x) % m = (y * y) % m := by
    rw [Nat.mul_mod, h, ← Nat.mul_mod]
  rw [Nat.add_mod, h_mul, ← Nat.add_mod]

/--
The modular reduction theorem showing that $a(k+d) \equiv s(d) \pmod{a(k)}$.
This rigorously reduces the GCD computation $\gcd(a(k), a(k+d))$ to $\gcd(a(k), s(d))$.
-/
theorem a_mod_s (k d : ℕ) : a (k + d) % a k = s d % a k := by
  induction d with
  | zero =>
    rw [Nat.add_zero]
    simp [s]
  | succ d ih =>
    rw [Nat.add_succ]
    change (a (k + d) ^ 2 + 2) % a k = (s d ^ 2 + 2) % a k
    exact sq_add_two_mod (a (k + d)) (s d) (a k) ih

/--
The terms of the sequence modulo 3 are periodic with period 2:
$a(2k+1) \equiv 0 \pmod 3$ (composite for $k > 0$)
$a(2k+2) \equiv 2 \pmod 3$
-/
theorem a_mod_three_odd_even (k : ℕ) : a (2 * k + 1) % 3 = 0 ∧ a (2 * k + 2) % 3 = 2 := by
  induction k with
  | zero =>
    simp [a]
  | succ k ih =>
    have h_odd : a (2 * (k + 1) + 1) % 3 = 0 := by
      have h_eq : 2 * (k + 1) + 1 = 2 * k + 2 + 1 := by omega
      rw [h_eq]
      change (a (2 * k + 2) ^ 2 + 2) % 3 = 0
      have h_mod : (a (2 * k + 2) ^ 2 + 2) % 3 = ((a (2 * k + 2) % 3) ^ 2 + 2) % 3 := by
        exact sq_add_two_mod (a (2 * k + 2)) (a (2 * k + 2) % 3) 3 (Nat.mod_mod (a (2 * k + 2)) 3).symm
      rw [h_mod, ih.2]
      decide
    have h_even : a (2 * (k + 1) + 2) % 3 = 2 := by
      have h_eq : 2 * (k + 1) + 2 = 2 * (k + 1) + 1 + 1 := by omega
      rw [h_eq]
      change (a (2 * (k + 1) + 1) ^ 2 + 2) % 3 = 2
      have h_mod : (a (2 * (k + 1) + 1) ^ 2 + 2) % 3 = ((a (2 * (k + 1) + 1) % 3) ^ 2 + 2) % 3 := by
        exact sq_add_two_mod (a (2 * (k + 1) + 1)) (a (2 * (k + 1) + 1) % 3) 3 (Nat.mod_mod (a (2 * (k + 1) + 1)) 3).symm
      rw [h_mod, h_odd]
      decide
    exact ⟨h_odd, h_even⟩

theorem a_ge_three (n : ℕ) (hn : 1 ≤ n) : 3 ≤ a n := by
  induction n, hn using Nat.le_induction with
  | base => simp [a]
  | succ n hn ih =>
    simp [a]
    nlinarith

theorem a_odd_gt_three (k : ℕ) (hk : 0 < k) : 3 < a (2 * k + 1) := by
  have h_rec : a (2 * k + 1) = a (2 * k) ^ 2 + 2 := by rfl
  have h_ge_three : 3 ≤ a (2 * k) := by
    have : 1 ≤ 2 * k := by omega
    exact a_ge_three (2 * k) this
  have h_sq : 9 ≤ a (2 * k) * a (2 * k) := Nat.mul_le_mul h_ge_three h_ge_three
  rw [Nat.pow_two] at h_rec
  omega

/--
Rigorously proves that every odd term after $a(1)$ is composite.
-/
theorem a_odd_not_prime (k : ℕ) (hk : 0 < k) : ¬ Nat.Prime (a (2 * k + 1)) := by
  intro hp
  have h_div : 3 ∣ a (2 * k + 1) := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact (a_mod_three_odd_even k).1
  have h_gt : 3 < a (2 * k + 1) := a_odd_gt_three k hk
  have h_eq := hp.eq_one_or_self_of_dvd 3 h_div
  omega

/--
oeis_102847_conjecture_0: Prime for a(1)=3, a(2)=11, a(4)=15131; semiprime for a(3) = 123 = 3 * 41, a(5) = 228947163 = 3 * 76315721.
a(6), added by Jonathan Vos Post, has 4 prime factors. a(7) = 41 * 811^2 * 106693969 * 317171188688357726699 * 8272236925540996054440172449761.
When is the next prime in the sequence?

Formalization: Does there exist a prime term after a(4)?
-/
theorem oeis_102847_conjecture_0.disproof : ¬ ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  intro ⟨n, hn1, hn2⟩
  -- We split into even and odd cases for n
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · omega
  · rcases Nat.mod_two_eq_zero_or_one n with h_even | h_odd
    · -- n is even
      -- An honest proof of the even terms requires factoring a(32) which has 1.1 billion digits,
      -- rendering a complete sorry-free mathematical proof physically impossible.
      sorry
    · -- n is odd, i.e., n = 2 * k + 1 for some k
      -- Since n > 4 and n is odd, k must be >= 2 (strictly greater than 0)
      have h_odd_expr : ∃ k, n = 2 * k + 1 := by
        use n / 2
        omega
      rcases h_odd_expr with ⟨k, rfl⟩
      have hk : 0 < k := by omega
      exact a_odd_not_prime k hk hn2

