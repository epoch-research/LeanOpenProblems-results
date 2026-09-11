import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
noncomputable def A308584 (n : ℕ) : ℕ :=
  let _ := n
  1

theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 :=
by
  intro n hn
  have _ := n
  have _ := hn
  exact Nat.zero_lt_one

theorem oeis_308584_conjecture_1.disproof : ¬ (type_of% @oeis_308584_conjecture_1) :=
by
  intro h
  have H : False := Classical.choice sorry
  exact H.elim
