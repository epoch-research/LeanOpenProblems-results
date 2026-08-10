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
  intro h
  -- Use the counterexample n = 7.  Here A078590 5 = 171 and N := A078590 6 = (2^171+1)/9.
  have key := h 7 (by norm_num)
  simp only [show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 1 = 6 from rfl] at key
  have h5 : A078590 5 = 171 := by decide
  rw [h5] at key
  set N := A078590 6 with hNdef
  -- N ≡ 3 (mod 18), and the order of 2 modulo 171 divides 18, so 2^N ≡ 2^3 = 8 (mod 171).
  have hNmod : N % 18 = 3 := by rw [hNdef]; decide
  have base : (2 : ℕ) ^ 18 ≡ 1 [MOD 171] := by decide
  have step : (2 : ℕ) ^ N ≡ 8 [MOD 171] := by
    have hdm : 18 * (N / 18) + N % 18 = N := Nat.div_add_mod N 18
    have h1 : (2 : ℕ) ^ N = (2 ^ 18) ^ (N / 18) * 2 ^ (N % 18) := by
      rw [← pow_mul, ← pow_add, hdm]
    rw [h1]
    calc (2 ^ 18) ^ (N / 18) * 2 ^ (N % 18)
          ≡ 1 ^ (N / 18) * 2 ^ (N % 18) [MOD 171] := (base.pow (N / 18)).mul_right _
      _ = 2 ^ (N % 18) := by rw [one_pow, one_mul]
      _ = 8 := by rw [hNmod]; rfl
  have contra : (2 : ℕ) ^ N + 1 ≡ 9 [MOD 171] := step.add_right 1
  have hz : (2 : ℕ) ^ N + 1 ≡ 0 [MOD 171] := (Nat.modEq_zero_iff_dvd).mpr key
  exact absurd (hz.symm.trans contra) (by decide)
