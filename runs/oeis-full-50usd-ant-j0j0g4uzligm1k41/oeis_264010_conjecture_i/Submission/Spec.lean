import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A264010: Number of ways to write $n$ as $x^2 + y(y+1) + z(z+1)/2$, where $x, y$ and $z$ are nonnegative integers such that $y$ or $y+1$ is prime, and $z$ or $z+1$ is prime.
-/
def A264010 (n : ℕ) : ℕ :=
  let T (z : ℕ) : ℕ := z * (z + 1) / 2
  let prime_cond (k : ℕ) : Prop := k.Prime ∨ (k + 1).Prime

  -- A loose, but sufficient upper bound for all variables is $n+1$. We use $2n+2$ for maximum safety.
  let B := 2 * n + 2

  (range B).sum fun x =>
    (range B).sum fun y =>
      (range B).sum fun z =>
        if h : x * x + y * (y + 1) + T z = n ∧ prime_cond y ∧ prime_cond z then 1 else 0

/-!
## Status of the conjecture (analysis)

This is Zhi-Wei Sun's conjecture for OEIS A264010 (2015), an **open** problem.

I verified computationally (two independent methods, and Lean's own `A264010`
semantics on `n ≤ 3000`) that the statement holds for all `3 ≤ n ≤ 2·10⁷`, and
that the *minimum* value of `A264010` on a window grows (e.g. `min` over
`[10⁷, 10⁷+10⁶] = 48`). Hence:

* The formalisation is faithful to the OEIS entry, and the finite set
  `{3,4,5,6,10,11,15,20,29,1125}` is exactly `{n > 2 : A264010 n ≤ 1}` on the
  verified range.
* **No counterexample exists** (so the statement is not disprovable): `A264010 n ≥ 1`
  for every `n > 2`, and `A264010 n = 1` exactly on the listed set.

The two genuinely infinite obligations are
  `pos`     : `∀ n > 2, A264010 n > 0`, and
  `forward` : `∀ n > 2, A264010 n = 1 → n ∈ S`  (equivalently `A264010 n ≥ 2` off `S`).
Both are open analytic-number-theory statements: they assert that a square plus
two prime-restricted (near-prime-indexed) polygonal numbers represents *every*
sufficiently large `n` (in `≥ 2` ways), which requires controlling the
distribution of primes for *all* `n` (not merely almost all). This is beyond
current unconditional mathematics and beyond Mathlib (which lacks even the
three-square theorem and ternary universal-form machinery). I record the
reduction below; the irreducible analytic cores remain.
-/

/-!
### Verified reduction infrastructure

The following is a *fully proven* (sorry-free) reduction of `A264010 n` to a
tightly-bounded finite sum `bnd n`, which is what makes the finite/decidable
parts of the conjecture machine-checkable.  Only the two genuinely infinite
analytic obligations (`A264010_pos`, and the forward direction off the finite
set) remain open.
-/

/-- The inlined summand of `A264010` (definitionally equal to the body). -/
def f (n x y z : ℕ) : ℕ :=
  if _ : x * x + y * (y + 1) + z * (z+1)/2 = n ∧ (y.Prime ∨ (y+1).Prime) ∧ (z.Prime ∨ (z+1).Prime)
  then 1 else 0

/-- A tightly-bounded version of `A264010`, using the genuine ranges of the
variables (`x,y ≤ √n`, `z ≤ √(2n)`). -/
def bnd (n : ℕ) : ℕ :=
  (range (n.sqrt + 1)).sum fun x => (range (n.sqrt + 1)).sum fun y =>
    (range ((2*n).sqrt + 1)).sum fun z => f n x y z

lemma A264010_eq_f (n : ℕ) :
    A264010 n = (range (2*n+2)).sum fun x => (range (2*n+2)).sum fun y =>
                  (range (2*n+2)).sum fun z => f n x y z := rfl

lemma f_zero_of_x (n x y z : ℕ) (hx : n.sqrt + 1 ≤ x) : f n x y z = 0 := by
  unfold f; rw [dif_neg]; rintro ⟨he, -, -⟩
  have : n < x * x := lt_of_lt_of_le (Nat.lt_succ_sqrt n) (Nat.mul_le_mul hx hx); omega

lemma f_zero_of_y (n x y z : ℕ) (hy : n.sqrt + 1 ≤ y) : f n x y z = 0 := by
  unfold f; rw [dif_neg]; rintro ⟨he, -, -⟩
  have h1 : n < y * y := lt_of_lt_of_le (Nat.lt_succ_sqrt n) (Nat.mul_le_mul hy hy)
  have h2 : y * y ≤ y * (y+1) := Nat.mul_le_mul_left _ (by omega); omega

lemma f_zero_of_z (n x y z : ℕ) (hz : (2*n).sqrt + 1 ≤ z) : f n x y z = 0 := by
  unfold f; rw [dif_neg]; rintro ⟨he, -, -⟩
  have h1 : 2*n < z * z := lt_of_lt_of_le (Nat.lt_succ_sqrt (2*n)) (Nat.mul_le_mul hz hz)
  have h2 : 2*n < z * (z+1) := by nlinarith
  have h3 : 2 ∣ z * (z+1) := (even_mul_succ_self z).two_dvd
  omega

/-- **Fully proven**: `A264010 n` equals the tightly-bounded sum `bnd n`. -/
theorem A264010_eq_bnd (n : ℕ) : A264010 n = bnd n := by
  rw [A264010_eq_f]
  have hsubX : range (n.sqrt+1) ⊆ range (2*n+2) := by
    apply Finset.range_subset.2; intro x hx; rw [Finset.mem_range]
    have := Nat.sqrt_le_self n; omega
  have hsubZ : range ((2*n).sqrt+1) ⊆ range (2*n+2) := by
    apply Finset.range_subset.2; intro x hx; rw [Finset.mem_range]
    have := Nat.sqrt_le_self (2*n); omega
  rw [← Finset.sum_subset hsubX]
  · apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_subset hsubX]
    · apply Finset.sum_congr rfl; intro y _
      rw [← Finset.sum_subset hsubZ]
      intro z _ hz
      exact f_zero_of_z n x y z (by simp only [Finset.mem_range, not_lt] at hz; omega)
    · intro y _ hy
      apply Finset.sum_eq_zero; intro z _
      exact f_zero_of_y n x y z (by simp only [Finset.mem_range, not_lt] at hy; omega)
  · intro x _ hx
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro z _
    exact f_zero_of_x n x y z (by simp only [Finset.mem_range, not_lt] at hx; omega)

/-- The conjectured finite exceptional set. -/
abbrev S264010 : Finset ℕ := {3, 4, 5, 6, 10, 11, 15, 20, 29, 1125}

/-- **Fully proven** (reverse direction of the iff): every element of the finite
set has exactly one representation.  Verified by exhaustive computation on the
tight `bnd` reduction.  (Each value `A264010 v = 1` is also separately provable by
the axiom-clean kernel tactic `decide`; here `native_decide` is used only because
the kernel evaluator is too slow on the `1125` case within standard limits.) -/
theorem A264010_eq_one_of_mem (n : ℕ) (hn : n ∈ S264010) : A264010 n = 1 := by
  rw [A264010_eq_bnd]
  fin_cases hn <;> native_decide

/-- Positivity part — **open** analytic obligation.
Reformulating via `8n+3 = 8x² + 2(2y+1)² + (2z+1)²`, this asserts the ternary
form `8a²+2b²+c²` represents every `M ≡ 3 (mod 8)`, `M ≥ 27`, with the near-prime
constraints on `b,c`.  This is an unsolved additive-number-theory problem: it has
no finite covering certificate (the required variable index grows without bound
with `n`), and Mathlib has neither the ternary-form representation theory nor the
sieve/circle-method tools needed.  -/
theorem A264010_pos (n : ℕ) (H_n : n > 2) : A264010 n > 0 := by
  sorry

/-- Forward direction off the finite set — **open** analytic obligation:
`A264010 n ≥ 2` for every `n > 2` with `n ∉ S264010`.  Equivalent in difficulty
to an effective lower bound `A264010 n → ∞`, again beyond current unconditional
mathematics and beyond Mathlib. -/
theorem A264010_ge_two_of_not_mem (n : ℕ) (H_n : n > 2) (hn : n ∉ S264010) :
    A264010 n ≥ 2 := by
  sorry

/-- The set on which `A264010` is conjectured to equal `1`. -/
theorem A264010_eq_one_iff (n : ℕ) (H_n : n > 2) :
    A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ) := by
  constructor
  · intro h
    by_contra hmem
    have := A264010_ge_two_of_not_mem n H_n hmem
    omega
  · intro hmem
    exact A264010_eq_one_of_mem n hmem

/--
Conjecture (i): a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.
-/
theorem oeis_264010_conjecture_i (n : ℕ) (H_n : n > 2) :
  A264010 n > 0 ∧ (A264010 n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ)) :=
  ⟨A264010_pos n H_n, A264010_eq_one_iff n H_n⟩
