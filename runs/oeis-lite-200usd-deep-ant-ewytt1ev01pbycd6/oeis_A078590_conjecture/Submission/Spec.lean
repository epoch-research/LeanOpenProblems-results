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
-- The 6th term of the sequence, `A078590 6 = a_val 5 = (2 ^ 171 + 1) / 9`,
-- written as an explicit numeral.
private def A078590_6 : ℕ := 332572817028187686275682948600327513806149983112761

/-- If `a ^ d = 1` in a monoid, then `a ^ n` only depends on `n % d`. -/
private lemma pow_reduce {M : Type*} [Monoid M] (a : M) (d : ℕ) (ha : a ^ d = 1) (n : ℕ) :
    a ^ n = a ^ (n % d) := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul, ha, one_pow, one_mul]

/-- The key counterexample fact: `171 = A078590 5` does **not** divide
`2 ^ (A078590 6) + 1`. Indeed `19 ∣ 171`, the order of `2` mod `19` is `18`,
and `A078590_6 % 18 = 3`, so `2 ^ (A078590 6) + 1 ≡ 2 ^ 3 + 1 = 9 ≢ 0 (mod 19)`. -/
private lemma A078590_key : ¬ ((171 : ℕ) ∣ 2 ^ A078590_6 + 1) := by
  intro hd
  have h19 : (19 : ℕ) ∣ 2 ^ A078590_6 + 1 := dvd_trans (by norm_num) hd
  have hz : ((2 ^ A078590_6 + 1 : ℕ) : ZMod 19) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h19
  push_cast at hz
  rw [pow_reduce (2 : ZMod 19) 18 (by decide) A078590_6] at hz
  rw [show A078590_6 % 18 = 3 by decide] at hz
  revert hz
  decide

/--
The conjecture that all terms of A078590 are integers is **false**: the division
is not exact at `A078590 7 = (2 ^ A078590 6 + 1) / A078590 5`.
Concretely, `A078590 5 = 171` does not divide `2 ^ A078590 6 + 1`, so the
divisibility statement fails at `n = 7`.
-/
theorem oeis_A078590_conjecture.disproof :
    ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  have h7 := h 7 (by norm_num)
  have e5 : A078590 5 = 171 := by rfl
  have e6 : A078590 6 = A078590_6 := by
    set_option maxRecDepth 10000 in rfl
  rw [show (7 : ℕ) - 2 = 5 from rfl, show (7 : ℕ) - 1 = 6 from rfl, e5, e6] at h7
  exact A078590_key h7
