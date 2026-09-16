import FormalConjectures.Util.ProblemImports

open Nat Function Set
open scoped Classical

/-- The step function for the Collatz sequence: $n/2$ if $n$ is even, $3n+1$ if $n$ is odd. -/
def collatz_step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2
  else 3 * n + 1

noncomputable def A006577_steps (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf {k : ℕ | (collatz_step^[k]) n = 1}

noncomputable def A153330 (n : ℕ) : ℤ :=
  if n = 0 then 0
  else (A006577_steps (n + 1) : ℤ) - (A006577_steps n : ℤ)

def A153330_indices (v : ℤ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ A153330 n = v}

theorem oeis_a153330_conjecture_2 :
    A153330_indices 1 = {1} ∧
    A153330_indices 6 = {2} ∧
    A153330_indices 16 = {8} ∧
    A153330_indices 3 = {4, 5} :=
by sorry

theorem oeis_a153330_conjecture_2.disproof : ¬ (type_of% @oeis_a153330_conjecture_2) :=
by sorry
