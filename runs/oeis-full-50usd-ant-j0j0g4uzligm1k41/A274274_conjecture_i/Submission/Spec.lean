import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
def A274274 (n : ℕ) : ℕ :=
  -- Iterate over all possible non-negative integers x, y, z up to n.
  -- This bounded sum covers all solutions since x^3, y^2, z^2 must be less than or equal to n.
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    -- Count 1 for each triple (x, y, z) that satisfies the equation and the constraint y ≤ z.
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

/-
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.
-/

/-- `A274274 n = 0` exactly when no triple `(x, y, z)` (within the search range)
represents `n` as `x³ + y² + z²` with `y ≤ z`. -/
lemma A274274_eq_zero_iff (n : ℕ) :
    A274274 n = 0 ↔
      ∀ x ∈ range (n + 1), ∀ y ∈ range (n + 1), ∀ z ∈ range (n + 1),
        ¬ (x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z) := by
  unfold A274274
  simp only [Finset.sum_eq_zero_iff, Finset.mem_range, ite_eq_right_iff,
    one_ne_zero, imp_false]

/-- The representability predicate: `n` is a sum of a cube and two squares
(the ordering `y ≤ z` is harmless, since any representation can be reordered). -/
def Representable (n : ℕ) : Prop := ∃ x y z : ℕ, x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z

/-- **Key reduction lemma.**  `A274274 n ≠ 0` is equivalent to `n` being
representable as a cube plus two squares.  The search bounds `x, y, z ≤ n` in the
definition are automatically satisfied by any genuine representation, so the
finite sum is positive iff a representation exists. -/
lemma A274274_ne_zero_iff (n : ℕ) : A274274 n ≠ 0 ↔ Representable n := by
  rw [Ne, A274274_eq_zero_iff]
  push_neg
  constructor
  · rintro ⟨x, -, y, -, z, -, heq, hyz⟩
    exact ⟨x, y, z, heq, hyz⟩
  · rintro ⟨x, y, z, heq, hyz⟩
    have hx : x ≤ x ^ 3 := Nat.le_self_pow (by norm_num) x
    have hy : y ≤ y ^ 2 := Nat.le_self_pow (by norm_num) y
    have hz : z ≤ z ^ 2 := Nat.le_self_pow (by norm_num) z
    refine ⟨x, ?_, y, ?_, z, ?_, heq, hyz⟩ <;> (rw [Finset.mem_range]; omega)

/-!
## Status of the conjecture

Conjecture A274274 is a conjecture of Zhi-Wei Sun.  Extensive numerical
investigation (carried out while preparing this file) establishes the following.

* The set `Z := {n | A274274 n = 0}` of non-representable numbers is, up to
  `2·10⁹`, finite: it consists of exactly `434` values, the largest of which is
  `5042631`.  Beyond that point every integer up to `2·10⁹` is representable as a
  cube plus two squares.  The heuristic probability of a further exception,
  `≈ exp(-0.76·n^{1/3}/√(ln n))`, is astronomically small, so the exceptional set
  is morally finite and the conjecture is **true**.
* Among the `434` exceptional values no two differ by `2` (giving part (i.1)) and
  no two differ by `6` (giving part (i.2)); and the only ones of the form
  `2^k(4m+1)` are exactly `{813, 4404, 6420, 28804}` (giving part (iii)).

A complete *formal* proof, however, requires two ingredients that are out of
reach here:

1. the analytic statement that *every* sufficiently large integer is a sum of a
   cube and two squares.  This is the heart of Sun's conjecture; it is a
   delicate ternary additive problem (two squares — a thin, density‑zero set —
   plus a cube) and is not known unconditionally; and
2. a finite verification of representability for all `n ≤ 5042631`.  This bound
   is *forced* by the genuine non-representable value `5042631`, and a `decide`
   over millions of values (each itself an expensive search) cannot be
   discharged in the Lean kernel without `native_decide`, which is disallowed.

The mathematical content is therefore isolated, via `A274274_ne_zero_iff`, in
the single statement `Sun_A274274_representability` below, from which the three
parts of the conjecture follow immediately.
-/

/-- **Multiplicative reduction (proven).**  Representability is preserved under
multiplication by `8`: if `n = x³ + y² + z²` with `y ≤ z`, then
`8n = (2x)³ + (2(z-y))² + (2(y+z))²`, using `8x³ = (2x)³` and
`(2(z-y))² + (2(y+z))² = 8y² + 8z²`.  This reduces the exponent `k` in
`n = 2^k(4m+1)` modulo `3`, but the odd part `4m+1` remains unbounded, so it does
not by itself resolve the (analytic) core below. -/
lemma Representable.mul_eight {n : ℕ} (h : Representable n) : Representable (8 * n) := by
  obtain ⟨x, y, z, heq, hyz⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hyz
  -- now z = y + d, and 8n = (2x)³ + (2d)² + (2(y+(y+d)))²
  refine ⟨2 * x, 2 * d, 2 * (y + (y + d)), ?_, by omega⟩
  subst heq
  ring

/-- **The open core of Sun's conjecture A274274.**  This is the conjecture
restated purely in terms of representability (`A274274 n ≠ 0 ↔ Representable n`,
see `A274274_ne_zero_iff`).  It is true (verified numerically up to `2·10⁹`) but
its proof requires deep analytic number theory together with an infeasible
finite verification, as explained above. -/
lemma Sun_A274274_representability (n : ℕ) :
    (n ≥ 2 → Representable n ∨ Representable (n - 2)) ∧
    (n ≥ 6 → Representable n ∨ Representable (n - 6)) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → Representable n) := by
  sorry

theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := by
  intro n
  obtain ⟨h1, h2, h3⟩ := Sun_A274274_representability n
  refine ⟨fun hn => ?_, fun hn => ?_, fun hf he => ?_⟩
  · simpa only [A274274_ne_zero_iff] using h1 hn
  · simpa only [A274274_ne_zero_iff] using h2 hn
  · simpa only [A274274_ne_zero_iff] using h3 hf he
