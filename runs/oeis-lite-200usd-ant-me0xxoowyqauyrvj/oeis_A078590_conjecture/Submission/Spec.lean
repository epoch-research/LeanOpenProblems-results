import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
private noncomputable def a_val : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 =>
  let a_n_minus_2 : ℕ := a_val n
  let a_n_minus_1 : ℕ := a_val (n + 1)

  -- The division is Nat.div, which is integer division.
  -- The terms are positive, so we do not fear division by zero.
  (2 ^ a_n_minus_1 + 1) / a_n_minus_2

end A078590

open A078590

/--
A078590: $a(1)=1$, $a(2)=1$, $a(n)=(2^{a(n-1)} + 1)/a(n-2)$.
Are all terms integers?
-/
noncomputable def A078590 (n : ℕ) : ℕ :=
  if n ≥ 1 then
    a_val (n - 1)
  else
    0

/--
oeis_78590_conjecture_0: Are all terms integers?
This is framed as a divisibility conjecture, ensuring that the division in the definition is exact at every step.
Specifically, for $n \ge 3$, $a(n-2)$ divides $2^{a(n-1)} + 1$.
-/
theorem oeis_A078590_conjecture.disproof :
    ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  -- A general (symbolic) periodicity lemma: if `a ^ d ≡ 1 [MOD n]`, then the exponent
  -- of `a` may be reduced modulo `d`.  Proving it with `q` a *variable* means the kernel
  -- never has to evaluate any astronomically large power.
  have periodic : ∀ (n a d q r : ℕ), a ^ d ≡ 1 [MOD n] → a ^ (d * q + r) ≡ a ^ r [MOD n] := by
    intro n a d q r h
    calc a ^ (d * q + r) = (a ^ d) ^ q * a ^ r := by rw [pow_add, pow_mul]
      _ ≡ 1 ^ q * a ^ r [MOD n] := (h.pow q).mul_right _
      _ = a ^ r := by rw [one_pow, one_mul]
  intro h
  -- Apply the conjecture at `n = 7`.
  have h7 := h 7 (by norm_num)
  -- Evaluate the two relevant terms of the sequence:
  --   A078590 5 = a_val 4 = 171,
  --   A078590 6 = a_val 5 = (2 ^ 171 + 1) / 9 = 332…761.
  have e5 : A078590 (7 - 2) = 171 := by decide
  have e6 : A078590 (7 - 1) = 332572817028187686275682948600327513806149983112761 := by decide
  rw [e5, e6] at h7
  -- Now `h7 : 171 ∣ 2 ^ N + 1` with `N = 332…761`.
  -- Since `N = 18 * q + 3` and `2 ^ 18 ≡ 1 [MOD 171]`, we get `2 ^ N ≡ 2 ^ 3 = 8 [MOD 171]`,
  -- hence `2 ^ N + 1 ≡ 9 [MOD 171]`, which is not `0`.
  have hN : (332572817028187686275682948600327513806149983112761 : ℕ)
      = 18 * 18476267612677093681982386033351528544786110172931 + 3 := by norm_num
  have key : (2 : ℕ) ^ 332572817028187686275682948600327513806149983112761 ≡ 8 [MOD 171] := by
    rw [hN]
    exact periodic 171 2 18 18476267612677093681982386033351528544786110172931 3 (by decide)
  have key2 := key.add_right 1
  have hz : (2 : ℕ) ^ 332572817028187686275682948600327513806149983112761 + 1 ≡ 0 [MOD 171] :=
    (Nat.modEq_zero_iff_dvd).mpr h7
  exact absurd (key2.symm.trans hz) (by decide)
