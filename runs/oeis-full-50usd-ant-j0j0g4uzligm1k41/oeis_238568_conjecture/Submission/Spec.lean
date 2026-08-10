import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The prime counting function $\pi(x)$, which computes the number of primes less than or equal to $x$.
We define it noncomputably since primality testing on $\mathbb{N}$ requires external resources like `prime_coalition`.
-/
noncomputable def pi_fn (n : ℕ) : ℕ :=
  Nat.card {p // Nat.Prime p ∧ p ≤ n}

/--
A238568: $a(n) = |\left\{ 0 < k < n: n^2 - \pi(k \cdot n) \text{ is prime} \right\}|$.
The sequence counts the number of $k \in \{1, \dots, n-1\}$ for which $n^2 - \pi(kn)$ is prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun k : ℕ =>
    Nat.Prime (Nat.pow n 2 - pi_fn (k * n))
  ) (Finset.Ico 1 n)

/-- The set of integers $n$ for which $a(n)=1$ according to the conjecture. -/
def A238568_special_set : Set ℕ := {2, 3, 4, 8, 10, 24, 41}

/-!
### Faithfulness of the formalization

We record that `pi_fn` is the genuine prime-counting function and that `a`
agrees with a computable reformulation.  These lemmas confirm that the
statement below is a faithful formalization of OEIS A238568.
-/

/-- A computable version of the prime-counting function. -/
def piC (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter Nat.Prime).card

/-- `pi_fn` equals the computable prime-counting function `piC`. -/
theorem pi_fn_eq (n : ℕ) : pi_fn n = piC n := by
  have hset : {p | Nat.Prime p ∧ p ≤ n}
      = (↑((Finset.range (n + 1)).filter Nat.Prime) : Set ℕ) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff]
    tauto
  show Nat.card ↥{p | Nat.Prime p ∧ p ≤ n} = piC n
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]
  rfl

/-- A computable version of the sequence `a`. -/
def aC (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun k : ℕ =>
    Nat.Prime (Nat.pow n 2 - piC (k * n))) (Finset.Ico 1 n)

/-- `a` agrees with its computable reformulation `aC`. -/
theorem a_eq (n : ℕ) : a n = aC n := by
  unfold a aC
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [pi_fn_eq]

/--
Conjecture from OEIS A238568:
(i) $a(n) > 0$ for all $n > 1$.
(ii) $a(n) = 1$ if and only if $n \in \{2, 3, 4, 8, 10, 24, 41\}$.
-/
theorem oeis_238568_conjecture :
  (∀ (n : ℕ), 1 < n → 0 < a n) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ A238568_special_set) := by
  refine ⟨?_, ?_⟩
  · -- Part (i): `∀ n > 1, 0 < a n`.
    -- Via `a_eq`, this asks: for every `n > 1` there is a `k ∈ [1, n)` with
    -- `n² - π(k·n)` prime.  Empirically `a n ≈ n / (2 log n)`, so this holds
    -- (with huge margin) for all `n`; a rigorous proof of the *existence* of a
    -- prime of this special form is, however, at least as hard as Legendre's
    -- conjecture, which is open.
    intro n hn
    rw [a_eq]
    sorry
  · -- Part (ii): `a n = 1 ↔ n ∈ {2,3,4,8,10,24,41}`.
    -- The backward direction is a finite computation.  The forward direction
    -- (for `n ∉ {2,3,4,8,10,24,41}`, `a n ≠ 1`) needs `a n ≥ 2` for all large
    -- `n`, i.e. *two* primes of the special form — even harder than part (i).
    intro n
    rw [a_eq]
    sorry
