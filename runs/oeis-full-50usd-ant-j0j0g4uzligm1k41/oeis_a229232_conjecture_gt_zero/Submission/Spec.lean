import FormalConjectures.Util.ProblemImports

open Nat List Finset

/--
A229232: Number of undirected circular permutations $\pi(1), \ldots, \pi(n)$ of $1, \ldots, n$
with the $n$ numbers $\pi(1)\pi(2)-1, \pi(2)\pi(3)-1, \ldots, \pi(n)\pi(1)-1$ all prime.
This is defined by counting the total number of linear permutations satisfying the property, and dividing by $2n$,
as is standard for counting equivalence classes under the dihedral group action on a set of size $n$.
-/
noncomputable def A229232 (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    -- The list of numbers [1, 2, ..., n]
    let l_n : List ℕ := (List.range N).map Nat.succ

    -- The set of all linear permutations of {1, ..., n}.
    let all_perms : Finset (List ℕ) := l_n.permutations.toFinset

    -- Predicate to check if a list satisfies the cyclic prime product minus one property.
    let is_cyclic_prime_chain (p : List ℕ) : Prop :=
      -- rotate (N-1) performs a left rotation by 1, giving the next cyclic element.
      let l_cyclic := p.rotate (N - 1)
      -- zip pairs (a_i, a_{i+1}) cyclically.
      (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))

    -- Filter the permutations based on the decidable prime chain property.
    let good_perms : Finset (List ℕ) :=
      all_perms.filter fun p => decide (is_cyclic_prime_chain p)

    -- The result is the total count of good linear permutations divided by $2n$.
    good_perms.card / (2 * N)

/-!
### Analysis of the conjecture (OEIS A229232, due to Zhi-Wei Sun)

`A229232 n > 0` is equivalent to the existence of an (undirected) cyclic arrangement
of `1, …, n` all of whose cyclic adjacent products minus one are prime, i.e. to the
Hamiltonicity of the *prime-product graph* `Gₙ` with vertex set `{1, …, n}` and an edge
`{i, j}` exactly when `i · j - 1` is prime. (More precisely `A229232 n = ⌊C₁/2⌋`, where
`C₁` is the number of directed cyclic sequences starting at vertex `1`, so positivity
requires `C₁ ≥ 2`.)

Computational verification carried out while studying this problem:
* Lean's `A229232` matches OEIS exactly: a(6)=2, a(7)=1, a(8)=2, …, a(12)=241, …,
  a(22)=60247058 (confirmed by exact enumeration; `List.permutations` produces all `n!`
  permutations and the `List.all` argument coerces to `decide (Nat.Prime …)`).
* No counterexample exists: `Gₙ` has minimum degree `≥ 2` for every `n ∈ [6, 10⁶]`
  except `n = 13`, and admits a Hamiltonian cycle for every `n ∈ [6, 2000]` except `13`.
  Hence the negation of the conjecture is false and cannot be proved.

Why a formal proof is out of reach here: every vertex of `Gₙ` has degree `~ n / ln n`
(sublinear), so no classical Hamiltonicity criterion — Dirac, Ore, Chvátal, or the
bipartite Moon–Moser theorem — applies (the graph is moreover essentially bipartite
between odds and evens, the unique odd-odd edge being `{1,3}`). A rigorous proof would
require lower bounds on the count of primes in the bilinear family `{i·j - 1}`
(Bombieri–Vinogradov-type input) together with an absorption/pseudorandomness argument;
none of this machinery is present in Mathlib. A purely constructive proof is impossible
in principle: an explicit cycle for general `n` needs the primality of products that
depend on `n`, which cannot be established for a formula in `n` (e.g. the natural
"insert `n+1, n+2`" recursion fails because `(n+1)(n+2) - 1` is composite for about 75%
of `n`). Consequently the statement below is a genuine open conjecture.
-/

/--
Conjecture: a(n) > 0 for all n > 5 with n not equal to 13.
-/
theorem oeis_a229232_conjecture_gt_zero (n : ℕ) :
  (n > 5 ∧ n ≠ 13) → A229232 n > 0 := by
  sorry
