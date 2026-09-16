import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A297707: $a(n) = \prod_{k=1}^{n-1} n!k$, where $n!k$ is $k$-tuple factorial of $n$.
The $k$-tuple factorial of $n$ is defined as
$$n!_k = \prod_{j=0}^{\lfloor(n-1)/k\rfloor} (n - j k)$$
-/
def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k

def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

local notation "a" => A297707

theorem oeis_297707_conjecture_0 :
  ∀ n, 2 < n → IsComposite (a n - Nat.prevPrime (a n)) → 250 < n :=
by
  intro n hn hcomp
  sorry

theorem oeis_297707_conjecture_0.disproof : ¬ (type_of% @oeis_297707_conjecture_0) := sorry
