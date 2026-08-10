import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The OEIS sequence A241922: Smallest $k^2 \ge 0$ such that $n-k^2$ is semiprime, or $a(n)=2$ if there is no such $k^2$.
A number $m$ is semiprime if $\Omega(m)=2$, where $\Omega(m)$ is the number of prime factors of $m$ counted with multiplicity.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- $\Omega(m)$ function definition.
  let omega (m : ℕ) : ℕ :=
    if m ≤ 1 then 0
    else (Nat.factorization m).sum (fun _ k => k)

  -- Semiprime predicate as a Boolean function.
  let is_semiprime (m : ℕ) : Bool := omega m == 2

  -- The maximum $k$ to check is $\lfloor \sqrt{n} \rfloor$.
  let k_max := Nat.sqrt n

  -- We search the list of candidates $\{0, 1, \dots, k_{\max}\}$ in ascending order.
  let k_candidates := List.range (k_max + 1)

  -- List.find? returns the smallest k satisfying the predicate, which minimizes k^2.
  match k_candidates.find? (fun k => is_semiprime (n - k * k)) with
  | some k => k * k
  | none   => 2

-- Auxiliary definitions for the conjecture

/--
The Goldbach binary conjecture states that every even integer greater than 2 is the sum of two prime numbers.
-/
def goldbach_binary_conjecture : Prop :=
  ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- A number is in A100570 if A241922(n) = 2.
A100570: Numbers $n$ such that $n-k^2$ is never semiprime for $0 \le k^2 \le n$.
-/
def is_A100570 (n : ℕ) : Prop := a n = 2

/-!
## Status of the formalised conjecture

The stated conjecture
`goldbach_binary_conjecture ↔ ¬ ∃ n, (∃ m, n = m * m) ∧ is_A100570 n`
is *provably equivalent to `¬ goldbach_binary_conjecture`*, hence is **false**
(binary Goldbach being true), and its negation is *provably equivalent to the
binary Goldbach conjecture itself*.

Reason.  `a 0 = 2` (provable by `rfl`: for `m ≤ 1` the function `omega` returns `0`
without touching the noncomputable `Nat.factorization`, so `find?` returns `none`).
Thus `is_A100570 0` holds, and since `0 = 0 * 0` is a perfect square, the existential
`E := ∃ n, (∃ m, n = m * m) ∧ is_A100570 n` is **provably true** (witness `n = 0`).
Therefore `¬ E` is provably **false**, the biconditional collapses to
`goldbach_binary_conjecture ↔ False`, and the negation collapses to
`goldbach_binary_conjecture`.

The trivial squares `0` and `1` lie in `A100570` because, via
`m² ∈ A100570 ↔ 2m is not a sum of two primes (and 2m-1 is not semiprime)`, they
correspond to the even numbers `0` and `2`, both outside Goldbach's range `n > 2`;
the OEIS comment overlooks these trivial squares, making the *formalised* statement
strictly equivalent to (the negation of) binary Goldbach.

The two reduction lemmas below are *complete, axiom-clean proofs* (no `sorry`):
they witness, inside Lean, the equivalences
  `(conjecture)   ↔ ¬ goldbach_binary_conjecture`
  `¬ (conjecture) ↔   goldbach_binary_conjecture`.
Consequently the disproof's single irreducible obligation is precisely a proof of
`goldbach_binary_conjecture` — the binary Goldbach conjecture (open since 1742,
verified computationally up to `4·10¹⁸`, with no proof available in Mathlib).
-/

/-- The existential side of the conjecture is provably true: `0 = 0²` is a perfect
square with `a 0 = 2`, i.e. `0 ∈ A100570`. -/
theorem exists_square_in_A100570 :
    ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n :=
  ⟨0, ⟨0, rfl⟩, rfl⟩

/-- **Reduction lemma (complete proof).** The formalised conjecture is logically
equivalent to the *negation* of binary Goldbach. -/
theorem conjecture_iff_not_goldbach :
    (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n)
      ↔ ¬ goldbach_binary_conjecture := by
  have hE := exists_square_in_A100570
  constructor
  · intro h hg; exact (h.mp hg) hE
  · intro hng
    exact ⟨fun hg => absurd hg hng, fun hne => absurd hE hne⟩

/-- **Reduction lemma (complete proof).** The disproof of the formalised conjecture
is logically equivalent to binary Goldbach itself. -/
theorem disproof_iff_goldbach :
    (¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n))
      ↔ goldbach_binary_conjecture := by
  have hE := exists_square_in_A100570
  constructor
  · intro h
    by_contra hng
    exact h ⟨fun hg => absurd hg hng, fun hne => absurd hE hne⟩
  · intro hg h; exact (h.mp hg) hE

/-- Conditional disproof: *granting* binary Goldbach, the formalised conjecture is
false.  This packages the entire argument with the open conjecture isolated as a
hypothesis; it is a complete, `sorry`-free, axiom-clean proof. -/
theorem disproof_of_goldbach (hG : goldbach_binary_conjecture) :
    ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) :=
  (disproof_iff_goldbach).mpr hG

/-- The disproof of the conjecture.

Its sole irreducible content is a proof of `goldbach_binary_conjecture` (the binary
Goldbach conjecture): by `disproof_iff_goldbach`, the statement below is logically
equivalent to binary Goldbach. The `sorry` marks exactly this open-mathematics
obligation, for which no proof exists in current mathematics or in Mathlib. -/
theorem oeis_241922_conjecture_1.disproof :
    ¬ (goldbach_binary_conjecture ↔ ¬ ∃ n : ℕ, (∃ m, n = m * m) ∧ is_A100570 n) := by
  have hG : goldbach_binary_conjecture := by sorry
  exact disproof_of_goldbach hG
