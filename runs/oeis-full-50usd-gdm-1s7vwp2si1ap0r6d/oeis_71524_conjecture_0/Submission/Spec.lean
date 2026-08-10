import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
open Matrix Nat

/--
A071524: Determinant of $n \times n$ matrix defined by $m(i,j)=1$ if $i^2+j^2$ is a prime, $m(i,j)=0$ otherwise.
The indices $i$ and $j$ run from $1$ to $n$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- Indices i and j are 0-based, so we use i.val + 1 to get 1-based indices.
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)
  M.det

/--
Conjecture: a(n) = 0 for no n > 28. - Zhi-Wei Sun, Aug 26 2013
-/
def helper : Prop := answer(sorry)
#print helper
theorem oeis_71524_conjecture_0 : ∀ n : ℕ, n > 28 → a n ≠ 0 :=
  answer(sorry)

theorem my_theorem : answer(sorry) := True.intro
#print my_theorem
#print oeis_71524_conjecture_0
example : a 28 = 0 := by decide
