import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A086766: $a(n)$ is the smallest $r$ where (concatenation of $n$, $r$ times with itself) $\cdot 10 + 1$ is a prime given by A087403(n), or $0$ if no such number exists.
The number resulting from concatenating $n$, $r$ times, is $n \cdot \sum_{i=0}^{r-1} (10^d)^i$, where $d$ is the number of digits of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ

    -- Concatenation as a geometric sum: $N_{n,r} = n \cdot \sum_{i=0}^{r-1} M^i$.
    let rep_cat_val (r : ℕ) : ℕ :=
      n * (Finset.range r).sum (fun i => M ^ i)

    let prime_candidate (r : ℕ) : ℕ := rep_cat_val r * 10 + 1

    -- The set of positive integers r for which the candidate is prime.
    let S : Set ℕ := {r : ℕ | 0 < r ∧ Nat.Prime (prime_candidate r)}

    -- `sInf S` returns the minimum element of $S$. For Set ℕ, sInf ∅ = 0.
    sInf S

/-- The smallest integer $m>1$ such that $a(10^m) \neq 0$. If no such $m$ exists, this value is $0$. -/
noncomputable def smallest_m_for_a10pow_nonzero : ℕ :=
  sInf {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0}

/--
Conjecture: What is the smallest integer m > 1 such that a(10^m) is nonzero?
Based on the OEIS notes, $a(10^m)=0$ for $m=2, 3, \dots, 275$, so the smallest such $m$ is greater than 275.
-/
theorem oeis_86766_conjecture_3 :
  smallest_m_for_a10pow_nonzero > 275 := by
  have h_ne : {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0}.Nonempty := by sorry
  have h_forall : ∀ m ∈ {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0}, m > 275 := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    by_contra h_le
    push_neg at h_le
    have h_zero : a (10 ^ m) = 0 := by sorry
    exact hm.2 h_zero
  have h_mem : smallest_m_for_a10pow_nonzero ∈ {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0} := Nat.sInf_mem h_ne
  exact h_forall smallest_m_for_a10pow_nonzero h_mem
