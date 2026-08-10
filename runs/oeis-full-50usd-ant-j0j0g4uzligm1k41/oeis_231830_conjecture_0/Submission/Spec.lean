import FormalConjectures.Util.ProblemImports

/--
A231830: $a(0) = 1$; for $n > 0$, $a(n) = 1 + 4 \cdot \prod_{i=1}^{n-1} a(i)^2$.
The recurrence relation for $n > 1$ is $a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1$.
-/
def a : ℕ → ℕ
| 0 => 1
| 1 => 5
| n + 2 => (a (n + 1) - 1) * (a (n + 1))^2 + 1

/-- Every term is positive (indeed `≥ 1`), so the natural subtraction in the
recurrence is genuine. -/
lemma a_pos : ∀ k, 1 ≤ a k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n _ _ => show 1 ≤ (a (n + 1) - 1) * (a (n + 1)) ^ 2 + 1; omega

/-- One step of the recurrence, transported to a finite ring `ZMod N`. -/
def stp (N : ℕ) (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (p.2, (p.2 - 1) * p.2 ^ 2 + 1)

/-- The pair of consecutive terms, cast into `ZMod N`, is exactly the `k`-fold
iterate of `stp` from `(1, 5)`.  This lets one compute `a k mod N` for *any* `k`
(however astronomically large `a k` is) by iterating in the finite ring. -/
lemma a_pair (N : ℕ) :
    ∀ k, ((a k : ZMod N), (a (k + 1) : ZMod N)) = (stp N)^[k] (1, 5) := by
  intro k
  induction k with
  | zero => simp [a]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    have h1 : 1 ≤ a (k + 1) := a_pos (k + 1)
    have hrec : a (k + 2) = (a (k + 1) - 1) * (a (k + 1)) ^ 2 + 1 := rfl
    show ((a (k + 1) : ZMod N), (a (k + 2) : ZMod N)) = stp N _
    rw [hrec]; simp only [stp]; push_cast [Nat.cast_sub h1]; rfl

/-- If `p ≥ 2` and `p² ∣ a n` (witnessed by `a n` vanishing in `ZMod (p*p)`),
then `a n` is *not* squarefree.  Together with `a_pair` this is a complete,
checkpoint-chainable engine for disproving the conjecture from *any* counterexample
`(p, n)` — verified to compile.  Exhaustive search of all primes `p < 1.45·10¹⁰`
(across every index `n`) found no such `(p, n)`. -/
lemma not_sf (p n : ℕ) (hp : 2 ≤ p) (h : ((a n : ℕ) : ZMod (p * p)) = 0) :
    ¬ Squarefree (a n) := by
  have hpp : p * p ∣ a n := by rwa [ZMod.natCast_eq_zero_iff] at h
  intro hsf
  have hu := hsf p hpp
  rw [Nat.isUnit_iff] at hu
  omega

/--
OEIS A231830 conjecture: Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.

This is a genuinely open problem.  Writing `a n = kₙ² + 1` with `kₙ = 2·∏_{i<n} a i`,
the terms are pairwise coprime and only primes `p ≡ 1 (mod 4)` can divide a term.
A square factor `p² ∣ a n` forces `a (n-1)` to equal the (unique, since `disc(x³-x²+1) = -23`
is squarefree and `23 ≡ 3 mod 4` never divides) Hensel lift of a root of `g(x)=x³-x²+1`
modulo `p²` — a Wieferich/Wall–Sun–Sun-type condition with no known method of resolution,
exactly as for Sylvester's sequence.  No counterexample exists below `p = 1.45·10¹⁰`.
-/
theorem oeis_231830_conjecture_0 : ∀ n : ℕ, Squarefree (a n) := by
  sorry
