import FormalConjectures.Util.ProblemImports

namespace A078590

/--
Helper definition for A078590, indexed from 0.
a_val 0 corresponds to A078590(1).
a_val 1 corresponds to A078590(2).
a_val (n+2) corresponds to A078590(n+3).
The definition uses standard natural number division, relying on the conjecture that the division is exact.
-/
noncomputable def a_val : ℕ → ℕ
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
theorem oeis_A078590_conjecture : ∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1) := by sorry

theorem oeis_A078590_conjecture.disproof : ¬ (type_of% @oeis_A078590_conjecture) := by
  intro h
  have h5 : A078590 5 = 171 := by
    norm_num [A078590, a_val]
  have h6 : A078590 6 = 332572817028187686275682948600327513806149983112761 := by
    norm_num [A078590, a_val]
  have hd := h 7 (by norm_num)
  norm_num only [Nat.reduceSub] at hd
  rw [h5, h6] at hd
  have hd19 : 19 ∣ 2 ^ 332572817028187686275682948600327513806149983112761 + 1 :=
    dvd_trans (by norm_num : 19 ∣ 171) hd
  have hp : (2 : ZMod 19) ^ 332572817028187686275682948600327513806149983112761 = 8 := by
    have he : 332572817028187686275682948600327513806149983112761 =
        18 * 18476267612677093681982386033351528544786110172931 + 3 := by norm_num
    rw [he, pow_add, pow_mul]
    rw [show (2 : ZMod 19) ^ 18 = 1 by decide, one_pow, one_mul]
    decide
  have hz := (ZMod.natCast_eq_zero_iff _ 19).mpr hd19
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hz
  rw [hp] at hz
  exact (by decide : (8 : ZMod 19) + 1 ≠ 0) hz
