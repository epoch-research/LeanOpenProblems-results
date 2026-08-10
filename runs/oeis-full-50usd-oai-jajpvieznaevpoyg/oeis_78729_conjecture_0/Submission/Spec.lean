import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
The product $(k+1)(k+2)\cdots(k+n)$.
-/
def A078729_product (n k : ℕ) : ℕ :=
  (Finset.range n).prod (fun i ↦ k + i + 1)

/--
A078729: $a(n)$ is the least positive integer $k$ such that
$$(k+1)(k+2)\cdots(k+n) + 1$$
is prime, if such $k$ exists; otherwise, $a(n) = 0$.
-/
noncomputable def A078729 (n : ℕ) : ℕ :=
  sInf { k : ℕ | k > 0 ∧ (A078729_product n k + 1).Prime }

/--
Conjecture: $a(n) = 0$ if and only if $n=4$.
-/
theorem oeis_78729_conjecture_0 : ∀ n : ℕ, A078729 n = 0 ↔ n = 4 := by sorry
