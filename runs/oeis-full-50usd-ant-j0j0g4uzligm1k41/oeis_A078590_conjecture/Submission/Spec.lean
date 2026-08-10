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
    ¬ ∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1) := by
  intro h
  -- Instantiate the conjecture at `n = 7`.
  have h7 := h 7 (by norm_num)
  -- Compute the relevant terms of the sequence.
  -- A078590 5 = a_val 4 = 171 and
  -- A078590 6 = a_val 5 = (2^171 + 1)/9 = N (a concrete 51-digit number).
  have e5 : A078590 (7 - 2) = 171 := by decide
  have e6 : A078590 (7 - 1)
      = 332572817028187686275682948600327513806149983112761 := by decide
  rw [e5, e6] at h7
  -- Now `h7 : 171 ∣ 2 ^ N + 1`, which we show is false.
  set N : ℕ := 332572817028187686275682948600327513806149983112761 with hN
  set q : ℕ := 18476267612677093681982386033351528544786110172931 with hq
  -- The multiplicative order of 2 modulo 171 divides 18, and N ≡ 3 (mod 18),
  -- so 2^N ≡ 2^3 = 8 (mod 171), hence 2^N + 1 ≡ 9 (mod 171) ≠ 0.
  have hbase : (2 : ℕ) ^ 18 ≡ 1 [MOD 171] := by decide
  have hNq : N = 18 * q + 3 := by norm_num [hN, hq]
  have hpow : (2 : ℕ) ^ N = ((2 : ℕ) ^ 18) ^ q * 2 ^ 3 := by
    rw [hNq, pow_add, pow_mul]
  have hstep : ((2 : ℕ) ^ 18) ^ q ≡ 1 ^ q [MOD 171] := hbase.pow q
  rw [one_pow] at hstep
  have hmod : (2 : ℕ) ^ N ≡ 8 [MOD 171] := by
    calc (2 : ℕ) ^ N = ((2 : ℕ) ^ 18) ^ q * 2 ^ 3 := hpow
      _ ≡ 1 * 2 ^ 3 [MOD 171] := hstep.mul_right _
      _ = 8 := by norm_num
  have hres : ((2 : ℕ) ^ N + 1) % 171 = 9 := by
    have := hmod.add_right 1
    simpa using this
  rw [Nat.dvd_iff_mod_eq_zero, hres] at h7
  exact absurd h7 (by norm_num)

