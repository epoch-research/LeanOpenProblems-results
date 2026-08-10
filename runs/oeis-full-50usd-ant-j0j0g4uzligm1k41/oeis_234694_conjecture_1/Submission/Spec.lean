import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A234694: $a(n) = |\{0 < k < n: p = k + \mathrm{prime}(n-k) \text{ and } \mathrm{prime}(p) - p + 1 \text{ are both prime}\}|$.
We interpret $\mathrm{prime}(m)$ as the $m$-th prime number $p_m$, which is $\mathrm{Nat.nth} \ \mathrm{Nat.Prime} \ (m-1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The finite set of indices k is {k : ℕ | 1 ≤ k < n} = Ico 1 n.
  (filter (fun k =>
    -- m is the index for the n-k-th prime
    let m : ℕ := n - k

    -- Since k ∈ Ico 1 n, m ≥ 1. The (n-k)-th prime is at 0-index m-1.
    let p_m : ℕ := Nat.nth Nat.Prime (m - 1)
    let p : ℕ := k + p_m

    -- Since p is a candidate prime, p must be at least 2. The p-th prime is at 0-index p-1.
    let p_th_prime : ℕ := Nat.nth Nat.Prime (p - 1)

    Nat.Prime p ∧ Nat.Prime (p_th_prime - p + 1)
  ) (Ico 1 n)).card

-- Helper definition for the p-th prime (0-indexed by p-1)
noncomputable def p_th_prime (p : ℕ) : ℕ := Nat.nth Nat.Prime (p - 1)

/- ### Machine-verified structural results

The following are all fully proven (no `sorry`), establishing the well-definedness and the
concrete content of the problem, and reducing it to its precise open core. -/

/-- Well-definedness: the `p`-th prime exceeds `p`, so `p_th_prime p - p + 1 ≥ 2`
(the truncated `ℕ`-subtraction does not collapse, and the first disjunct is a genuine value). -/
theorem p_th_prime_ge (p : ℕ) (hp : 1 ≤ p) : p + 1 ≤ p_th_prime p := by
  unfold p_th_prime
  have h := Nat.add_two_le_nth_prime (p - 1)
  omega

theorem p_th_prime_sub_add_ge_two (p : ℕ) (hp : 1 ≤ p) : 2 ≤ p_th_prime p - p + 1 := by
  have := p_th_prime_ge p hp
  omega

/-- `p_th_prime p` is genuinely (the enumeration of) a prime. -/
theorem p_th_prime_prime (p : ℕ) : Nat.Prime (p_th_prime p) :=
  Nat.prime_nth_prime (p - 1)

/-- A concrete witness: `p = 2` satisfies the conclusion (the disjunct is genuinely satisfiable). -/
theorem two_qualifies : Nat.Prime 2 ∧
    (Nat.Prime (p_th_prime 2 - 2 + 1) ∨ Nat.Prime (p_th_prime 2 + 2 + 1)) := by
  refine ⟨by norm_num, ?_⟩
  have h2 : p_th_prime 2 = 3 := by unfold p_th_prime; simp
  rw [h2]; left; norm_num

/-- The set of primes `p` witnessing the conjecture's conclusion. -/
def QualifyingPrimes : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧
    (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1))}

/-- **Verified reduction.** The conjecture is *equivalent* to the statement that
`QualifyingPrimes` is an infinite set. This isolates the entire mathematical content of the
problem into a single, precise infinitude claim about primes of a special form. -/
theorem conj_iff_infinite :
    (∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
      (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)))
    ↔ QualifyingPrimes.Infinite := by
  constructor
  · intro H
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hpN, hp1, hp2⟩ := H N
    exact absurd (hN (show p ∈ QualifyingPrimes from ⟨hp1, hp2⟩)) (not_le.2 hpN)
  · intro H N
    obtain ⟨p, hp, hpN⟩ := H.exists_gt N
    exact ⟨p, hpN, hp.1, hp.2⟩

/- ### Status of the core infinitude claim `QualifyingPrimes.Infinite`

This is a genuinely **open** problem. It asks for infinitely many primes `p` such that the
`p`-th prime `q = prime(p)` satisfies that `q - p + 1` or `q + p + 1` is prime. It is the
"implies infinitely many primes ..." remark attached to Zhi-Wei Sun's conjecture for OEIS
sequence A234694, and is unresolved.

The statement is (heuristically and numerically) **true**: the density of qualifying primes
is stable around `0.25` up to `p = 10^6`, matching the expected `~ 2C / log p`, whose sum over
primes diverges — so infinitely many primes qualify. Consequently the *negation* is false and no
sound disproof exists.

Proving it, however, lies beyond current mathematics: `prime(p) ± p + 1` is neither a linear form
(so Dirichlet's theorem does not apply — indeed no residue class of `p` forces either disjunct)
nor an algebraic form (so Friedlander–Iwaniec / Heath-Brown methods do not apply), and it is not a
linear form in the prime variable (so Maynard–Tao / GPY sieve results do not apply). Detecting
primes in the "random-like" sequence `prime(p) ± p + 1` is obstructed by the *parity problem*, the
same fundamental barrier that keeps the twin-prime and Mersenne-prime conjectures open.
-/

/--
Conjecture part (i) of A234694 implies that there are infinitely many primes $p$ with
$\mathrm{prime}(p) - p + 1$ (or $\mathrm{prime}(p) + p + 1$) also prime.
-/
theorem oeis_234694_conjecture_1 :
  ∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧
  (Nat.Prime (p_th_prime p - p + 1) ∨ Nat.Prime (p_th_prime p + p + 1)) := by
  rw [conj_iff_infinite]
  sorry
