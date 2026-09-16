import FormalConjectures.Util.ProblemImports

open Int Set Filter Topology Nat

/--
A182510: $a(0)=0, a(1)=1, a(n)=(a(n-1) \text{ XOR } n) - a(n-2)$, where $\text{XOR}$ is the bitwise exclusive-or operator.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => Int.xor (a (n + 1)) (n + 2 : ℤ) - a n

theorem oeis_a182510_conjecture_density :
  ∃ d_pos d_neg : ℝ,
    ({n : ℕ | a n > 0}).HasDensity d_pos ∧
    ({n : ℕ | a n < 0}).HasDensity d_neg ∧
    d_pos > d_neg :=
by sorry

theorem oeis_a182510_conjecture_density.disproof : ¬ (type_of% @oeis_a182510_conjecture_density) :=
by sorry
