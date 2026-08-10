import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
A289827: $a(n)$ is the largest $m \le n$ such that $\pi(m + n) = \pi(m) + \pi(n)$, where $\pi$ is the prime counting function $\text{A000720}$ ($\pi(0) = 0$).
-/
noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

/--
A claim often attributed to Carl Pomerance, discussing the implications of a conjecture
by T. Ordowski (the boundedness of A289827).

The conjecture being discussed is the boundedness of $A289827(n)$, namely $A289827(n) \le 10$.
Pomerance wrote: "I believe if correct, your conjecture would disprove the Hardy-Littlewood
prime k-tuples conjecture, as shown by Hensley and Richards over 30 years ago. They showed
that prime k-tuples implies that there are pairs y < x with pi(x+y) >= pi(x) + pi(y) and
pi(y) arbitrarily large. Since pi(2x) < 2*pi(x), by increasing y in a y,x example, one would
come on a new pair y' < x with pi(x+y') = pi(x) + pi(y')."
-/
theorem A289827_conjecture_bounded_by_10 : ∀ (n : ℕ), A289827 n ≤ 10 := by sorry
