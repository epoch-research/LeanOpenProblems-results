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
  -- The conjecture fails at `n = 7`.
  -- We have `A078590 5 = 171 = 9 * 19` and `A078590 6 = N := (2 ^ 171 + 1) / 9`.
  -- By the lifting-the-exponent lemma, `ν₃(2 ^ 171 + 1) = 1 + ν₃(171) = 3`, so `ν₃(N) = 1`,
  -- hence `N ≡ 3 [MOD 9]`; concretely `N ≡ 3 [MOD 18]`.
  -- Since the order of `2` modulo `19` is `18` and `2 ^ 9 ≡ -1 [MOD 19]`, we get
  -- `2 ^ N + 1 ≡ 2 ^ 3 + 1 = 9 [MOD 19]`, so `19 ∤ 2 ^ N + 1`, whence `171 ∤ 2 ^ N + 1`.
  have h7 := h 7 (by norm_num)
  have hA5 : A078590 5 = 171 := by
    simp only [A078590, show (5:ℕ) ≥ 1 by norm_num, if_true]
    simp [a_val]
  have hA6 : A078590 6 = 332572817028187686275682948600327513806149983112761 := by
    simp only [A078590, show (6:ℕ) ≥ 1 by norm_num, if_true]
    simp [a_val]
  rw [show (7:ℕ) - 2 = 5 from rfl, show (7:ℕ) - 1 = 6 from rfl, hA5, hA6] at h7
  -- h7 : 171 ∣ 2 ^ N + 1 with N = 332572817028187686275682948600327513806149983112761
  have h19 : (19:ℕ) ∣ 2 ^ 332572817028187686275682948600327513806149983112761 + 1 :=
    dvd_trans (by norm_num) h7
  have hz : ((2 ^ 332572817028187686275682948600327513806149983112761 + 1 : ℕ) : ZMod 19) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h19
  push_cast at hz
  rw [show (332572817028187686275682948600327513806149983112761 : ℕ)
      = 18 * 18476267612677093681982386033351528544786110172931 + 3 from by norm_num,
    pow_add, pow_mul, show ((2:ZMod 19)) ^ 18 = 1 from by decide, one_pow, one_mul] at hz
  exact absurd hz (by decide)
