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

theorem a078590_5_eq : A078590 5 = 171 := by rfl
theorem a078590_6_eq : A078590 6 = (2^171 + 1) / 9 := by rfl

theorem mod_18 : A078590 6 % 18 = 3 := by
  rw [a078590_6_eq]
  decide

lemma pow_mod (k : ℕ) : (2 : ZMod 19) ^ (18 * k + 3) = 8 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : 18 * (k + 1) + 3 = 18 * k + 3 + 18 := by omega
    rw [h, pow_add, ih]
    have h2 : (2 : ZMod 19) ^ 18 = 1 := by decide
    rw [h2, mul_one]

lemma val_mod_19 : (2 : ZMod 19) ^ A078590 6 = 8 := by
  have h1 : A078590 6 = 18 * (A078590 6 / 18) + (A078590 6 % 18) := by exact Eq.symm (Nat.div_add_mod (A078590 6) 18)
  rw [mod_18] at h1
  nth_rw 1 [h1]
  exact pow_mod (A078590 6 / 18)

lemma val_add_one_mod_19 : ((2 ^ A078590 6 + 1 : ℕ) : ZMod 19) = 9 := by
  push_cast
  rw [val_mod_19]
  rfl

lemma no_div_19 : ¬ 19 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  have h2 : ((2 ^ A078590 6 + 1 : ℕ) : ZMod 19) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (2 ^ A078590 6 + 1) 19).mpr h
  rw [val_add_one_mod_19] at h2
  revert h2
  decide

lemma no_div_171 : ¬ 171 ∣ 2 ^ A078590 6 + 1 := by
  intro h
  have h19 : 19 ∣ 171 := by decide
  have h2 : 19 ∣ 2 ^ A078590 6 + 1 := dvd_trans h19 h
  exact no_div_19 h2

theorem oeis_A078590_conjecture.disproof : ¬ (type_of% @oeis_A078590_conjecture) := by
  intro h
  have h7 := h 7 (by decide)
  have h5 : A078590 (7 - 2) = 171 := by rfl
  have h6 : A078590 (7 - 1) = A078590 6 := by rfl
  rw [h5, h6] at h7
  exact no_div_171 h7
