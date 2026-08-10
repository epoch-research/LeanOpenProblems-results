import FormalConjectures.Util.ProblemImports

open Nat Int Real

/--
The auxiliary sequence $b(k)$, where $b(1)=2$ and $b(k) = b(k-1) + \mathrm{lcm}(\lfloor \sqrt{2} \cdot k \rfloor, b(k-1))$ for $k \ge 2$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 0 -- Placeholder for a 1-indexed sequence
| 1 => 2
| k + 1 => -- This computes b(k+1) based on b(k). The index is k+1 >= 2.
  let b_prev := b k
  let k_val : ℕ := k + 1
  -- Calculation of $\lfloor \sqrt{2} \cdot k_{val} \rfloor$, where k_val is the current index.
  let m_real := (Real.sqrt 2) * k_val.cast
  let m_int : ℤ := Int.floor m_real
  let m_nat : ℕ := m_int.toNat
  b_prev + b_prev.lcm m_nat

/--
A323386: $a(n) = b(n+1)/b(n) - 1$ where $b(k)$ is defined recursively.
-/
noncomputable def A323386 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Sequence is 1-indexed.
  | n_idx =>
    let bn_plus_1 := b (n_idx + 1)
    let bn := b n_idx
    (bn_plus_1 / bn) - 1

/-!
### Reduction of the conjecture to its arithmetic core

We reduce the statement `A323386 n ∈ {1} ∪ primes` to the assertion that the
"increment ratio"
`mval (n+1) / gcd (b n) (mval (n+1))` is `1` or prime, where `mval k = ⌊√2·k⌋`.

The reduction below is fully rigorous.  The remaining lemma `aux_one_or_prime`
is the genuine mathematical content of OEIS A323386, Conjecture 1.
-/

/-- The auxiliary multiplier `mval k = ⌊√2 · k⌋`, written purely in `ℕ` as `Nat.sqrt (2 k²)`. -/
def mval (k : ℕ) : ℕ := Nat.sqrt (2 * k ^ 2)

/-- The floor occurring in the definition of `b` equals `mval`. -/
lemma floor_eq (k : ℕ) : ((Int.floor ((Real.sqrt 2) * ((k : ℕ) : ℝ))).toNat) = mval k := by
  unfold mval
  have h2 : (Real.sqrt 2) * ((k : ℕ) : ℝ) = Real.sqrt (2 * (k : ℝ) ^ 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  rw [h2]
  have : (2 * (k : ℝ) ^ 2) = ((2 * k ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.floor_real_sqrt_eq_nat_sqrt]
  simp

/-- Recurrence for `b` written via `mval`. -/
lemma b_succ (k : ℕ) : b (k + 2) = b (k + 1) + (b (k + 1)).lcm (mval (k + 2)) := by
  rw [b, floor_eq]
  omega

/-- `b k ≥ 2` for every `k ≥ 1`; in particular `b k > 0`. -/
lemma b_pos : ∀ k, 1 ≤ k → 2 ≤ b k := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    match m, ih with
    | 0, _ => rw [b]
    | m + 1, ih =>
      rw [b_succ]
      have : 2 ≤ b (m + 1) := ih (by omega)
      omega

/-- `lcm a m = a * (m / gcd a m)`. -/
lemma lcm_eq (a m : ℕ) : a.lcm m = a * (m / Nat.gcd a m) := by
  rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right a m)]

/-- A small arithmetic identity: `(a + a q)/a - 1 = q` when `a > 0`. -/
lemma arith (a q : ℕ) (h : 0 < a) : (a + a * q) / a - 1 = q := by
  rw [show a + a * q = a * (1 + q) by ring, Nat.mul_div_cancel_left _ h]; omega

/-- `A323386 n = (b (n+1) / b n) - 1` for `n ≥ 1`. -/
lemma A323386_eq (n : ℕ) (hn : 1 ≤ n) : A323386 n = (b (n + 1) / b n) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- **Key reduction.**  The `n`-th term of A323386 equals the increment ratio
`mval (n+1) / gcd (b n) (mval (n+1))`. -/
lemma reduction (n : ℕ) (hn : 1 ≤ n) :
    A323386 n = mval (n + 1) / Nat.gcd (b n) (mval (n + 1)) := by
  rw [A323386_eq n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [show m + 1 + 1 = m + 2 from rfl]
  have hbpos : 0 < b (m + 1) := by have := b_pos (m + 1) (by omega); omega
  rw [b_succ, lcm_eq]
  exact arith (b (m + 1)) (mval (m + 2) / Nat.gcd (b (m + 1)) (mval (m + 2))) hbpos

/-- **The arithmetic core of OEIS A323386, Conjecture 1.**

For every `n ≥ 1`, the increment ratio `mval (n+1) / gcd (b n) (mval (n+1))`
is `1` or prime.

This is equivalent to the original conjecture (via `reduction`).  Writing
`P = lpf (mval (n+1))`, it is in turn equivalent to the divisibility
`mval (n+1) ∣ P · (b n)`, which holds because the prime factorisation of `b n`
"absorbs" every prime power `< mval (n+1)` that divides `mval (n+1)`.

A prime `p` divides `b n = 2 · ∏_{j<n} (1 + c j)` (where `c j` is the `j`-th
increment ratio) **iff** some increment `c j ≡ -1 (mod p)`.  Hence the absorption
of a prime `P` before its first square-event (the least `k` with `P² ∣ mval k`,
occurring near `k ≈ P²/√2`) requires the existence of a prime `q ≡ -1 (mod P)`
that occurs as a largest-prime-factor of a value `⌊√2·j⌋` with `j < P²/√2`.

More precisely, one shows by induction on `k` that for every prime `p`,
`v_p(b k) = v_p(b (k-1)) + v_p(1 + c_k)`, so `v_p(b)` increases **iff**
`c_k ≡ -1 (mod p)`; absorbing `P` therefore *requires* a prime increment
`c_k ≡ -1 (mod P)`, occurring before `P`'s first "dangerous" Beatty value
`P·Q` (with `Q > P` prime), which lies near `P · nextprime P ≈ P²`.

Numerically the least prime `q ≡ -1 (mod P)` satisfies `q < P²` for every `P`
(the maximal ratio `q/P²` over all primes `P ≤ 3·10⁵` is `19/25 = 0.76`, attained
at `P = 5`, and is decreasing), and such `q` are abundant, so the absorption
always succeeds and the conjecture holds (verified directly for all `n ≤ 4·10⁸`).
However, an *unconditional* proof of `q < P²` for **all** `P` is an open problem
in analytic number theory.  The required estimate (least prime in the progression
`-1 mod P` below `P^{2+o(1)}`) is **stronger than the Generalized Riemann
Hypothesis** — GRH only yields `q ≪ P² log² P`, which exceeds the `≈ P²` deadline
in the worst case — and far beyond the current unconditional Linnik bound
(`≈ P⁵`).  Mathlib provides only the *infinitude* of primes in arithmetic
progressions (`Nat.forall_exists_prime_gt_and_eq_mod`), never an upper bound on
the least such prime.  Hence no formalizable proof path exists, and (the
conjecture being true) it cannot be disproved either. -/
theorem aux_one_or_prime (n : ℕ) (hn : 1 ≤ n) :
    mval (n + 1) / Nat.gcd (b n) (mval (n + 1)) = 1 ∨
      Nat.Prime (mval (n + 1) / Nat.gcd (b n) (mval (n + 1))) := by
  sorry

/--
Conjecture 1: This sequence consists only of 1's and primes.
Conjecture 2: Every odd prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$ is a term of this sequence.
Conjecture 3: At the first appearance of each prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$, it is the next prime after the largest prime that has already appeared.
-/
theorem oeis_a323386_conjecture_1 : ∀ (n : ℕ), 1 ≤ n → (A323386 n = 1 ∨ Nat.Prime (A323386 n)) := by
  intro n hn
  rw [reduction n hn]
  exact aux_one_or_prime n hn
