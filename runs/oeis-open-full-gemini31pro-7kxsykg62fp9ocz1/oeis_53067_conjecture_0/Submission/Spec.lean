import FormalConjectures.Util.ProblemImports
import FormalConjectures.Util.Answer

open Nat List

/-- The $n$-th triangular number, $T_n = \frac{n(n+1)}{2}$. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Concatenates two natural numbers $a$ and $b$ base 10. -/
def concatenate_nats (a b : ℕ) : ℕ :=
  a * (10 ^ (Nat.digits 10 b).length) + b

/--
A053067: $a(n)$ is the concatenation of next $n$ numbers (omit leading 0's).
Specifically, $a(n)$ is the concatenation of the integers from $\frac{(n-1)n}{2} + 1$ up to $\frac{n(n+1)}{2}$.
-/
def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let start_num : ℕ := triangular (n - 1) + 1
    let end_num : ℕ := triangular n
    let numbers_to_concat : List ℕ := List.Ico start_num (end_num + 1)
    numbers_to_concat.foldl concatenate_nats 0

theorem oeis_53067_conjecture_0 : ∀ n : ℕ, Nat.Prime (a n) ↔ n = 2 := by
  answer(sorry)

theorem a_eval_2 : a 2 = 23 := by 
  unfold a
  simp [triangular]
  change List.foldl concatenate_nats 0 [2, 3] = 23
  unfold List.foldl
  change concatenate_nats (concatenate_nats 0 2) 3 = 23
  unfold concatenate_nats
  have h1 : (Nat.digits 10 2) = [2] := by 
    rw [Nat.digits_def']
    · simp
    · decide
    · decide
  have h2 : (Nat.digits 10 3) = [3] := by 
    rw [Nat.digits_def']
    · simp
    · decide
    · decide
  rw [h1, h2]
  rfl

theorem a_2_prime : Nat.Prime (a 2) := by
  rw [a_eval_2]
  decide

theorem oeis_53067_conjecture_0.disproof : ¬ (type_of% @oeis_53067_conjecture_0) := by
  sorry
