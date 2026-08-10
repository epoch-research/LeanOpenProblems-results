import FormalConjectures.Util.ProblemImports

open Nat List

-- rev_base(b, n) is the natural number whose base b digits are the reverse of n's digits
/-- `rev_base b n` is the number whose base-`b` digits are the reversal of `n`'s base-`b` digits. -/
def rev_base (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n |>.reverse)

/--
$a_n$ is the $n$-th term of the trajectory of $103$ under the Reverse and Add! operation carried out in base $3$, written in base $10$.
$a_0 = 103$.
$a_{n+1} = a_n + \text{rev}_3(a_n)$, where $\text{rev}_3(n)$ is the number whose base $3$ digits are the reversal of $n$'s base $3$ digits.
-/
noncomputable def A077408 : ℕ → ℕ
  | 0 => 103
  | n + 1 => A077408 n + rev_base 3 (A077408 n)

/-- A natural number $n$ is a base $b$ palindrome if its base $b$ digits read the same forwards and backwards.
This is equivalent to $n = \text{rev}_b(n)$. -/
def is_base_palindrome (b n : ℕ) : Prop := n = rev_base b n

/--
A077408 103 is conjectured to be the smallest number such that the Reverse and Add! algorithm in base 3 does not lead to a palindrome.
The conjecture formalized here is that the trajectory of 103 under this operation in base 3 never reaches a palindrome.
-/
-- A genuine, provable reformulation: `A077408 n` is a base-3 palindrome exactly when the
-- next term of the trajectory is precisely double the current one.  Indeed, by definition
-- `A077408 (n+1) = A077408 n + rev_base 3 (A077408 n)`, so `A077408 n = rev_base 3 (A077408 n)`
-- holds iff `A077408 (n+1) = 2 * A077408 n`.
theorem oeis_77408_palindrome_iff_double (n : ℕ) :
    is_base_palindrome 3 (A077408 n) ↔ A077408 (n + 1) = 2 * A077408 n := by
  unfold is_base_palindrome
  show A077408 n = rev_base 3 (A077408 n) ↔ A077408 (n + 1) = 2 * A077408 n
  have hrec : A077408 (n + 1) = A077408 n + rev_base 3 (A077408 n) := rfl
  omega

theorem oeis_77408_conjecture_0 : ∀ n : ℕ, ¬ (is_base_palindrome 3 (A077408 n)) := by
  sorry
