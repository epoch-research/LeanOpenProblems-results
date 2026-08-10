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
private theorem pow_mod_step (k : ℕ) : 2 ^ (108 * k + 57) % 171 = 8 := by
  induction k with
  | zero =>
    rfl
  | succ p ih =>
    have h1 : 108 * (p + 1) + 57 = (108 * p + 57) + 108 := by omega
    rw [h1]
    rw [Nat.pow_add]
    rw [Nat.mul_mod]
    rw [ih]

private theorem t2 : 2 ^ A078590 6 % 171 = 8 := by
  have h_eq : A078590 6 = 108 * (A078590 6 / 108) + 57 := by
    have h_mod2 : A078590 6 % 108 = 57 := rfl
    omega
  rw [h_eq]
  exact pow_mod_step (A078590 6 / 108)

private theorem t3 : (2 ^ A078590 6 + 1) % 171 = 9 := by
  have h_add := Nat.add_mod (2 ^ A078590 6) 1 171
  rw [t2] at h_add
  exact h_add

theorem oeis_A078590_conjecture.disproof : ¬ (∀ (n : ℕ), 3 ≤ n → A078590 (n-2) ∣ (2 ^ A078590 (n-1) + 1)) := by
  intro h
  have h7 : 3 ≤ 7 := by omega
  specialize h 7 h7
  have h_eq1 : 7 - 2 = 5 := rfl
  have h_eq2 : 7 - 1 = 6 := rfl
  rw [h_eq1, h_eq2] at h
  have h_5 : A078590 5 = 171 := rfl
  rw [h_5] at h
  have h_mod := Nat.mod_eq_zero_of_dvd h
  have h_contra : (0 : ℕ) = 9 := h_mod.symm.trans t3
  have h_not : (0 : ℕ) ≠ 9 := by decide
  exact h_not h_contra
