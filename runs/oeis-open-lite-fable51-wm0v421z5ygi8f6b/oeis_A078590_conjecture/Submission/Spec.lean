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

/-- `2 ^ (18 q + 3) + 1 ≡ 9 (mod 171)`, since `2 ^ 18 ≡ 1 (mod 171)`. -/
theorem A078590.key (q : ℕ) : (2 ^ (18 * q + 3) + 1) % 171 = 9 := by
  rw [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem A078590.key2 (q : ℕ) : ¬ 171 ∣ (2 ^ (18 * q + 3) + 1) := by
  have := A078590.key q
  omega

theorem A078590.key3 (m : ℕ) (hm : m % 18 = 3) : ¬ 171 ∣ (2 ^ m + 1) := by
  have : m = 18 * (m / 18) + 3 := by omega
  rw [this]; exact A078590.key2 _

theorem A078590.a5 : a_val 5 = (2 ^ 171 + 1) / 9 := by simp [a_val]

/--
Disproof: the terms are `1, 1, 3, 9, 171, (2^171+1)/9, ...`, and `a(5) = 171 = 9 * 19` does
not divide `2^{a(6)} + 1`: the order of `2` modulo `171` is `18`, `a(6) ≡ 3 (mod 18)`,
hence `2^{a(6)} + 1 ≡ 2^3 + 1 = 9 (mod 171)`.
-/
theorem oeis_A078590_conjecture.disproof : ¬ (type_of% @oeis_A078590_conjecture) := by
  intro h
  have h7 := h 7 (by norm_num)
  generalize hm : A078590 (7-1) = m at h7
  have e1 : A078590 (7-2) = 171 := by simp [A078590, a_val]
  rw [e1] at h7
  have hmod : m % 18 = 3 := by
    rw [← hm, show A078590 (7-1) = a_val 5 from rfl, A078590.a5]; norm_num
  exact A078590.key3 m hmod h7
