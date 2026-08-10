import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306250: Number of ways to write $n$ as $x(3x+1) + y(3y-1) + z(3z+2) + w(3w-2)$,
where $x,y,z,w$ are nonnegative integers with $x \cdot y \cdot z = 0$.
-/
def A306250 (n : ℕ) : ℕ :=
  let T₁ (x : ℕ) : ℕ := x * (3 * x + 1)
  let T₂ (y : ℕ) : ℕ := y * (3 * y - 1)
  let T₃ (z : ℕ) : ℕ := z * (3 * z + 2)
  let T₄ (w : ℕ) : ℕ := w * (3 * w - 2)

  -- The search space for each variable is bounded by $n$.
  -- A more precise bound can be derived, but `n+1` is a safe upper limit for the range.
  -- For non-negative $x,y,z,w$, $T_i(v) \ge v$. If $T_i(v) \le n$, then $v \le n$.
  let R := range (n + 1)

  -- We compute the number of tuples $(x, y, z, w)$ satisfying the conditions using a sum of indicator functions.
  R.sum fun x =>
    R.sum fun y =>
      R.sum fun z =>
        R.sum fun w =>
          if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then
            1
          else
            0

lemma le_T1 (x : ℕ) : x ≤ x * (3*x+1) := by
  by_cases hx : x = 0
  · simp [hx]
  · have : 1 ≤ 3*x+1 := by omega
    simpa using Nat.le_mul_of_pos_right x this

lemma le_T2 (y : ℕ) : y ≤ y * (3*y-1) := by
  rcases y with _|y
  · simp
  · have : 1 ≤ 3 * Nat.succ y - 1 := by omega
    simpa using Nat.le_mul_of_pos_right (Nat.succ y) this

lemma le_T3 (z : ℕ) : z ≤ z * (3*z+2) := by
  have : 1 ≤ 3*z+2 := by omega
  simpa using Nat.le_mul_of_pos_right z this

lemma le_T4 (w : ℕ) : w ≤ w * (3*w-2) := by
  rcases w with _|w
  · simp
  · have : 1 ≤ 3 * Nat.succ w - 2 := by omega
    simpa using Nat.le_mul_of_pos_right (Nat.succ w) this

lemma A_pos_of_exists {n x y z w : ℕ}
    (hzero : x = 0 ∨ y = 0 ∨ z = 0)
    (hsum : x * (3 * x + 1) + y * (3 * y - 1) + z * (3 * z + 2) + w * (3 * w - 2) = n) :
    A306250 n > 0 := by
  unfold A306250
  let R := range (n+1)
  have hxmem : x ∈ R := by
    simp [R]
    have hxleterm := le_T1 x
    have htermle : x * (3*x+1) ≤ n := by omega
    omega
  have hymem : y ∈ R := by
    simp [R]
    have hyleterm := le_T2 y
    have htermle : y * (3*y-1) ≤ n := by omega
    omega
  have hzmem : z ∈ R := by
    simp [R]
    have hzleterm := le_T3 z
    have htermle : z * (3*z+2) ≤ n := by omega
    omega
  have hwmem : w ∈ R := by
    simp [R]
    have hwleterm := le_T4 w
    have htermle : w * (3*w-2) ≤ n := by omega
    omega
  apply Finset.sum_pos'
  · intro a ha
    exact Finset.sum_nonneg (by intro b hb; exact Finset.sum_nonneg (by intro c hc; exact Finset.sum_nonneg (by intro d hd; split <;> omega)))
  · refine ⟨x, hxmem, ?_⟩
    apply Finset.sum_pos'
    · intro a ha
      exact Finset.sum_nonneg (by intro b hb; exact Finset.sum_nonneg (by intro c hc; split <;> omega))
    · refine ⟨y, hymem, ?_⟩
      apply Finset.sum_pos'
      · intro a ha
        exact Finset.sum_nonneg (by intro b hb; split <;> omega)
      · refine ⟨z, hzmem, ?_⟩
        apply Finset.sum_pos'
        · intro a ha; split <;> omega
        · refine ⟨w, hwmem, ?_⟩
          simp [hzero, hsum]

/--
Conjecture: a(n) > 0 for any nonnegative integer n.
-/
theorem oeis_306250_conjecture_0 (n : ℕ) : A306250 n > 0 := by sorry
