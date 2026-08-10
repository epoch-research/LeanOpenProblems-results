import FormalConjectures.Util.ProblemImports

open Nat

/--
A263206: Number of primes $p$ with $\text{prime}(p) \in (n^2, (n+2)^2)$, where $p$ is a prime index.
The term $\text{prime}(p)$ here refers to the $p$-th prime number.
Let $\pi(x) = \text{Nat.primeCounting } x$ be the prime counting function.
The indices $i$ such that $\text{prime}(i) \in (n^2, (n+2)^2)$ start at $L = \pi(n^2) + 1$
and end at $R = \pi((n+2)^2 - 1)$.
The sequence value $a(n)$ is the number of primes $p$ such that $L \le p \le R$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The least index $i$ (1-based) such that $\text{prime}(i) > n^2$ is $\pi(n^2) + 1$.
  let L : ℕ := (n^2).primeCounting + 1
  -- The greatest index $i$ (1-based) such that $\text{prime}(i) < (n+2)^2$ is $\pi((n+2)^2 - 1)$.
  let R : ℕ := ((n + 2)^2 - 1).primeCounting
  -- The number of primes $p$ such that $L \le p \le R$ is $\pi(R) - \pi(L-1)$.
  R.primeCounting - (L - 1).primeCounting

/-! ### Reduction of the conjecture to a prime-existence statement

`a n` unfolds to `π(π((n+2)^2-1)) - π(π(n^2))` (truncated subtraction), so `a n > 0` is
equivalent to the existence of a prime `p` with `π(n^2) < p ≤ π((n+2)^2-1)`.  The two lemmas
below establish the (forward) implication we need rigorously. -/

/-- If `p` is prime and `u < p`, then `π(u) < π(p)`. -/
theorem pc_lt_of_prime {u p : ℕ} (hp : p.Prime) (h : u < p) :
    u.primeCounting < p.primeCounting := by
  unfold Nat.primeCounting Nat.primeCounting'
  have hmono : Nat.count Nat.Prime (u + 1) ≤ Nat.count Nat.Prime p :=
    Nat.count_monotone _ (by omega)
  have hsucc : Nat.count Nat.Prime (p + 1) = Nat.count Nat.Prime p + 1 := by
    rw [Nat.count_succ, if_pos hp]
  omega

/-- The existence of a prime in the index interval `(π(n^2), π((n+2)^2-1)]` implies `a n > 0`. -/
theorem reduction (n : ℕ)
    (h : ∃ p, p.Prime ∧ (n ^ 2).primeCounting < p ∧ p ≤ ((n + 2) ^ 2 - 1).primeCounting) :
    a n > 0 := by
  obtain ⟨p, hp, h1, h2⟩ := h
  simp only [a, Nat.add_sub_cancel]
  have s1 : ((n ^ 2).primeCounting).primeCounting < p.primeCounting := pc_lt_of_prime hp h1
  have s2 : p.primeCounting ≤ (((n + 2) ^ 2 - 1).primeCounting).primeCounting :=
    Nat.monotone_primeCounting h2
  omega

/-- **Reverse reduction (machine-checked, axiom-clean).**  `a n > 0` implies that the interval
`(n^2, (n+2)^2)` contains a prime.  This proves that the conjecture is *at least as strong* as a
Legendre/Oppermann-type statement — a Landau problem, open since 1808.  (Depends only on
`propext, Classical.choice, Quot.sound`.) -/
theorem a_pos_implies_prime_between (n : ℕ) (h : a n > 0) :
    ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 2) ^ 2 := by
  simp only [a, Nat.add_sub_cancel] at h
  have hstep : (n ^ 2).primeCounting < ((n + 2) ^ 2 - 1).primeCounting := by
    by_contra hle
    push_neg at hle
    have : (((n + 2) ^ 2 - 1).primeCounting).primeCounting ≤ ((n ^ 2).primeCounting).primeCounting :=
      Nat.monotone_primeCounting hle
    omega
  have e1 : (n ^ 2).primeCounting = Nat.count Nat.Prime (n ^ 2 + 1) := rfl
  have h1 : (n + 2) ^ 2 - 1 + 1 = (n + 2) ^ 2 := by
    have : 0 < (n + 2) ^ 2 := by positivity
    omega
  have e2 : ((n + 2) ^ 2 - 1).primeCounting = Nat.count Nat.Prime ((n + 2) ^ 2) := by
    show Nat.count Nat.Prime ((n + 2) ^ 2 - 1 + 1) = Nat.count Nat.Prime ((n + 2) ^ 2)
    rw [h1]
  have hcount : Nat.count Nat.Prime (n ^ 2 + 1) < Nat.count Nat.Prime ((n + 2) ^ 2) := by
    rw [e1, e2] at hstep; exact hstep
  obtain ⟨x, hx, hxp⟩ := Nat.exists_of_count_lt_count hcount
  simp only [Set.mem_Ico] at hx
  exact ⟨x, hxp, by omega, by omega⟩

/-- **The irreducible open core.**  For every `n ≥ 1` there is a prime `p` with
`π(n^2) < p ≤ π((n+2)^2-1)`.

This is equivalent in strength to an open problem.  A necessary condition for it is that the
interval `(n^2, (n+2)^2)` (length `4n+4 = 4√x+4` at `x = n^2`) contain a prime — exactly the
`θ = 1/2` prime-gap barrier (Legendre/Oppermann), which is unproven unconditionally and even under
the Riemann Hypothesis.  Mathlib supplies only Bertrand's postulate, whose hypothesis
`2·π(n^2) ≤ π((n+2)^2-1)` fails for every `n ≥ 4`. -/
theorem index_interval_has_prime (n : ℕ) (hn : 0 < n) :
    ∃ p, p.Prime ∧ (n ^ 2).primeCounting < p ∧ p ≤ ((n + 2) ^ 2 - 1).primeCounting := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. In other words, for each n = 1,2,3,... the interval (n^2, (n+2)^2) contains a prime with prime subscript.
-/
theorem oeis_a263206_conjecture_0 (n : ℕ) : 0 < n → a n > 0 := by
  intro hn
  exact reduction n (index_interval_has_prime n hn)
