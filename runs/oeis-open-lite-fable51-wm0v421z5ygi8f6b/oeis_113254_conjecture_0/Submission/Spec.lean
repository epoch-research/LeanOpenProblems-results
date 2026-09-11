import FormalConjectures.Util.ProblemImports

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

namespace A113254

/-- `w = -1 + √-15`, an algebraic integer of norm 16 with `w² + 2w + 16 = 0`.
The characteristic polynomial of the recurrence is `(x - 8) (x + 8) (x² + 4x + 64)`, and
`x² + 4x + 64` has roots `2w` and `2 * star w`. -/
def w : ℤ√(-15) := ⟨-1, 1⟩

lemma w_sq : w ^ 2 = -2 * w - 16 := by
  ext <;> simp [w, pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul]

lemma w_pow_add_two (n : ℕ) : w ^ (n + 2) = -2 * w ^ (n + 1) - 16 * w ^ n := by
  have : w ^ (n + 2) = w ^ n * w ^ 2 := by ring
  rw [this, w_sq]; ring

lemma norm_w : Zsqrtd.norm w = 16 := by
  simp [Zsqrtd.norm_def, w]

lemma norm_w_pow (n : ℕ) : Zsqrtd.norm (w ^ n) = 16 ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, norm_w, pow_succ]

/-- Closed form: `a n = 2 * 8^n - 2 * (-8)^n + 2^n * Re(w^(n+1))`. -/
def f (n : ℕ) : ℤ := 2 * 8 ^ n - 2 * (-8) ^ n + 2 ^ n * (w ^ (n + 1)).re

lemma f_rec (n : ℕ) : f (n + 4) = -4 * f (n + 3) + 256 * f (n + 1) + 4096 * f n := by
  have h3 : w ^ (n + 3) = -2 * w ^ (n + 2) - 16 * w ^ (n + 1) := w_pow_add_two (n + 1)
  have h4 : w ^ (n + 4) = -12 * w ^ (n + 2) + 32 * w ^ (n + 1) := by
    rw [w_pow_add_two (n + 2), h3]; ring
  have h5 : w ^ (n + 5) = 56 * w ^ (n + 2) + 192 * w ^ (n + 1) := by
    rw [w_pow_add_two (n + 3), h4, h3]; ring
  simp only [f, show n + 4 + 1 = n + 5 from rfl, show n + 3 + 1 = n + 4 from rfl,
    show n + 1 + 1 = n + 2 from rfl]
  rw [h5, h4]
  simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_neg]
  simp
  ring

lemma a_eq_f (n : ℕ) : a n = f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [a, f, w]
    | 1 => simp [a, f, w, pow_two, Zsqrtd.re_mul]
    | 2 => simp [a, f, w, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    | 3 => simp [a, f, w, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul]
    | n + 4 =>
      rw [a, ih (n + 3) (by omega), ih (n + 1) (by omega), ih n (by omega), f_rec]

/-- `a (2n+1) = (2^(n+1) * Re(w^(n+1)))²`, using `Re(z²) = x² - 15y²` and `x² + 15y² = 16^(n+1)`. -/
theorem main (n : ℕ) : IsSquare (a (2 * n + 1)) := by
  rw [a_eq_f, f]
  refine ⟨2 ^ (n + 1) * (w ^ (n + 1)).re, ?_⟩
  have hnorm := norm_w_pow (n + 1)
  rw [Zsqrtd.norm_def] at hnorm
  have hsq : w ^ (2 * n + 1 + 1) = w ^ (n + 1) * w ^ (n + 1) := by ring
  rw [hsq, Zsqrtd.re_mul]
  rw [Odd.neg_pow ⟨n, rfl⟩, show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul]
  rw [show (16 : ℤ) = 2 ^ 4 by norm_num, ← pow_mul] at hnorm
  linear_combination (-(2 : ℤ) ^ (2 * n + 1)) * hnorm

end A113254

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  exact A113254.main

theorem oeis_113254_conjecture_0.disproof : ¬ (type_of% @oeis_113254_conjecture_0) := sorry
