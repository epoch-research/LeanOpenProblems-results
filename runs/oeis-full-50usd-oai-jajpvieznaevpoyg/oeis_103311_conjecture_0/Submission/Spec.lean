import FormalConjectures.Util.ProblemImports

set_option linter.unreachableTactic false
set_option linter.unusedTactic false


/--
A103311: A transform of the Fibonacci numbers.
The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n

private def eps : ℕ → ℤ
| 0 => 1
| n + 1 => - eps n

private lemma eps_eq_or (k : ℕ) : eps k = 1 ∨ eps k = -1 := by
  induction k with
  | zero => simp [eps]
  | succ k ih =>
      rcases ih with h | h <;> simp [eps, h]

private lemma natAbs_eps_mul_fib (k r : ℕ) : Int.natAbs (eps k * (Nat.fib r : ℤ)) = Nat.fib r := by
  rcases eps_eq_or k with h | h <;> simp [h]

private lemma natAbs_neg_eps_mul_fib (k r : ℕ) : Int.natAbs (-(eps k) * (Nat.fib r : ℤ)) = Nat.fib r := by
  rcases eps_eq_or k with h | h <;> simp [h]

private lemma a_rec (n : ℕ) : a (n + 4) = 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n := rfl

private theorem a_block (k : ℕ) :
    a (5 * k) = eps k * (Nat.fib (5 * k) : ℤ) ∧
    a (5 * k + 1) = eps k * (Nat.fib (5 * k + 1) : ℤ) ∧
    a (5 * k + 2) = eps k * (Nat.fib (5 * k + 1) : ℤ) ∧
    a (5 * k + 3) = 0 ∧
    a (5 * k + 4) = -(eps k) * (Nat.fib (5 * k + 3) : ℤ) := by
  induction k with
  | zero =>
      norm_num [a, eps]
  | succ k ih =>
      rcases ih with ⟨h0, h1, h2, h3, h4⟩
      have H0 : a (5 * (k + 1)) = eps (k + 1) * (Nat.fib (5 * (k + 1)) : ℤ) := by
        rw [show 5 * (k + 1) = (5 * k + 1) + 4 by ring]
        rw [a_rec]
        rw [show 5 * k + 1 + 3 = 5 * k + 4 by ring,
            show 5 * k + 1 + 2 = 5 * k + 3 by ring,
            show 5 * k + 1 + 1 = 5 * k + 2 by ring]
        rw [h4, h3, h2, h1]
        simp only [eps]
        ring_nf
        try rw [show 1 + k * 5 = k * 5 + 1 by ring]
        try rw [show 3 + k * 5 = k * 5 + 3 by ring]
        try rw [show 5 + k * 5 = k * 5 + 5 by ring]
        try rw [show 6 + k * 5 = k * 5 + 6 by ring]
        try rw [show 8 + k * 5 = k * 5 + 8 by ring]
        try simp only [Nat.fib_add_two, Nat.cast_add]
        ring
      have H1 : a (5 * (k + 1) + 1) = eps (k + 1) * (Nat.fib (5 * (k + 1) + 1) : ℤ) := by
        rw [show 5 * (k + 1) + 1 = (5 * k + 2) + 4 by ring]
        rw [a_rec]
        rw [show 5 * k + 2 + 3 = 5 * (k + 1) by ring,
            show 5 * k + 2 + 2 = 5 * k + 4 by ring,
            show 5 * k + 2 + 1 = 5 * k + 3 by ring]
        rw [H0, h4, h3, h2]
        simp only [eps]
        ring_nf
        try rw [show 1 + k * 5 = k * 5 + 1 by ring]
        try rw [show 3 + k * 5 = k * 5 + 3 by ring]
        try rw [show 5 + k * 5 = k * 5 + 5 by ring]
        try rw [show 6 + k * 5 = k * 5 + 6 by ring]
        try rw [show 8 + k * 5 = k * 5 + 8 by ring]
        try simp only [Nat.fib_add_two, Nat.cast_add]
        ring
      have H2 : a (5 * (k + 1) + 2) = eps (k + 1) * (Nat.fib (5 * (k + 1) + 1) : ℤ) := by
        rw [show 5 * (k + 1) + 2 = (5 * k + 3) + 4 by ring]
        rw [a_rec]
        rw [show 5 * k + 3 + 3 = 5 * (k + 1) + 1 by ring,
            show 5 * k + 3 + 2 = 5 * (k + 1) by ring,
            show 5 * k + 3 + 1 = 5 * k + 4 by ring]
        rw [H1, H0, h4, h3]
        simp only [eps]
        ring_nf
        try rw [show 1 + k * 5 = k * 5 + 1 by ring]
        try rw [show 3 + k * 5 = k * 5 + 3 by ring]
        try rw [show 5 + k * 5 = k * 5 + 5 by ring]
        try rw [show 6 + k * 5 = k * 5 + 6 by ring]
        try rw [show 8 + k * 5 = k * 5 + 8 by ring]
        try simp only [Nat.fib_add_two, Nat.cast_add]
        ring
      have H3 : a (5 * (k + 1) + 3) = 0 := by
        rw [show 5 * (k + 1) + 3 = (5 * k + 4) + 4 by ring]
        rw [a_rec]
        rw [show 5 * k + 4 + 3 = 5 * (k + 1) + 2 by ring,
            show 5 * k + 4 + 2 = 5 * (k + 1) + 1 by ring,
            show 5 * k + 4 + 1 = 5 * (k + 1) by ring]
        rw [H2, H1, H0, h4]
        simp only [eps]
        ring_nf
        try rw [show 1 + k * 5 = k * 5 + 1 by ring]
        try rw [show 3 + k * 5 = k * 5 + 3 by ring]
        try rw [show 5 + k * 5 = k * 5 + 5 by ring]
        try rw [show 6 + k * 5 = k * 5 + 6 by ring]
        try rw [show 8 + k * 5 = k * 5 + 8 by ring]
        try simp only [Nat.fib_add_two, Nat.cast_add]
        ring
      have H4 : a (5 * (k + 1) + 4) = -(eps (k + 1)) * (Nat.fib (5 * (k + 1) + 3) : ℤ) := by
        rw [show 5 * (k + 1) + 4 = (5 * (k + 1)) + 4 by ring]
        rw [a_rec]
        rw [H3, H2, H1, H0]
        simp only [eps]
        ring_nf
        try rw [show 1 + k * 5 = k * 5 + 1 by ring]
        try rw [show 3 + k * 5 = k * 5 + 3 by ring]
        try rw [show 5 + k * 5 = k * 5 + 5 by ring]
        try rw [show 6 + k * 5 = k * 5 + 6 by ring]
        try rw [show 8 + k * 5 = k * 5 + 8 by ring]
        try simp only [Nat.fib_add_two, Nat.cast_add]
        ring
      exact ⟨H0, H1, H2, H3, H4⟩

theorem oeis_103311_conjecture_0 (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  let k := n / 5
  have hn : n = 5 * k + n % 5 := by
    dsimp [k]
    exact (Nat.div_add_mod n 5).symm
  have hlt : n % 5 < 5 := Nat.mod_lt n (by decide)
  have hcases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases hcases with hmod | hmod | hmod | hmod | hmod
  · use 5 * k
    rw [hn, hmod, Nat.add_zero]
    rw [(a_block k).1]
    exact natAbs_eps_mul_fib k (5 * k)
  · use 5 * k + 1
    rw [hn, hmod]
    rw [(a_block k).2.1]
    exact natAbs_eps_mul_fib k (5 * k + 1)
  · use 5 * k + 1
    rw [hn, hmod]
    rw [(a_block k).2.2.1]
    exact natAbs_eps_mul_fib k (5 * k + 1)
  · use 0
    rw [hn, hmod]
    rw [(a_block k).2.2.2.1]
    simp
  · use 5 * k + 3
    rw [hn, hmod]
    rw [(a_block k).2.2.2.2]
    exact natAbs_neg_eps_mul_fib k (5 * k + 3)
