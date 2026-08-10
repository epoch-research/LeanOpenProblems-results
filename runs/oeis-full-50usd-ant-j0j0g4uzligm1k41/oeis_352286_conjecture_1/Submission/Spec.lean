import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat

/--
A352286: Number of ways to write $n$ as $w + x^2 + 2y^2 + 3z^2 + x \cdot y \cdot z$, where $w$ is $0$ or $1$, and $x,y,z$ are nonnegative integers.
$$a(n) = \left| \left\{ (w, x, y, z) \in \{0, 1\} \times \mathbb{N}^3 \mid n = w + x^2 + 2y^2 + 3z^2 + xyz \right\} \right|$$
-/
def A352286 (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

def A352286_exceptions : Set ℕ := {106, 744, 5469, 331269}

/-- `A352286 n = 0` exactly says there is no representation inside the search box. -/
lemma A352286_eq_zero_iff_box (n : ℕ) : A352286 n = 0 ↔
    ∀ w ∈ range 2, ∀ x ∈ range (n+1), ∀ y ∈ range (n+1), ∀ z ∈ range (n+1),
      n ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by
  simp only [A352286, Finset.sum_eq_zero_iff, mem_range, ite_eq_right_iff, one_ne_zero,
    imp_false]

private lemma le_of_sq_le {a n : ℕ} (h : a ^ 2 ≤ n) : a ≤ n :=
  le_trans (Nat.le_self_pow two_ne_zero a) h

/-- If `a^2 ≤ n < (B+1)^2` then `a ≤ B`. -/
private lemma sqrt_bound {a n B : ℕ} (h : a ^ 2 ≤ n) (hB : n < (B + 1) ^ 2) : a ≤ B := by
  by_contra hlt
  push_neg at hlt
  have : (B + 1) ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hlt 2
  omega

/-- `A352286 n = 0` is equivalent to the (unbounded) non-representability of `n`:
no representation can use `x`, `y` or `z` larger than `n`, so the bounded count above
coincides with non-representability over all of `ℕ`. -/
lemma A352286_eq_zero_iff (n : ℕ) : A352286 n = 0 ↔
    ∀ w x y z : ℕ, w < 2 → n ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by
  rw [A352286_eq_zero_iff_box]
  constructor
  · intro h w x y z hw hc
    have hxn : x ^ 2 ≤ n := by rw [hc]; omega
    have hyn : y ^ 2 ≤ n := by rw [hc]; omega
    have hzn : z ^ 2 ≤ n := by rw [hc]; omega
    have hx : x ∈ range (n+1) := mem_range.mpr (Nat.lt_succ_of_le (le_of_sq_le hxn))
    have hy : y ∈ range (n+1) := mem_range.mpr (Nat.lt_succ_of_le (le_of_sq_le hyn))
    have hz : z ∈ range (n+1) := mem_range.mpr (Nat.lt_succ_of_le (le_of_sq_le hzn))
    exact h w (mem_range.mpr hw) x hx y hy z hz hc
  · intro h w hw x _ y _ z _
    exact h w x y z (mem_range.mp hw)

-- The four exceptions are not representable (finite verifications).
private lemma bdd106 : ∀ w ≤ 1, ∀ x ≤ 10, ∀ y ≤ 7, ∀ z ≤ 5,
    106 ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by native_decide
private lemma bdd744 : ∀ w ≤ 1, ∀ x ≤ 27, ∀ y ≤ 19, ∀ z ≤ 15,
    744 ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by native_decide
private lemma bdd5469 : ∀ w ≤ 1, ∀ x ≤ 73, ∀ y ≤ 52, ∀ z ≤ 42,
    5469 ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by native_decide
private lemma bdd331269 : ∀ w ≤ 1, ∀ x ≤ 575, ∀ y ≤ 406, ∀ z ≤ 332,
    331269 ≠ w + x^2 + 2*y^2 + 3*z^2 + x*y*z := by native_decide

/--
Conjecture 1: a(n) = 0 if and only if $n \in \{106, 744, 5469, 331269\}$.

The "if" direction (these four numbers are non-representable) is proved below by a finite
search.  The "only if" direction — that **every** other natural number *is* representable —
is the deep open content of Zhi-Wei Sun's conjecture and is isolated in the single `sorry`.
-/
theorem oeis_352286_conjecture_1 :
  ∀ n : ℕ, (A352286 n = 0 ↔ n ∈ A352286_exceptions) := by
  intro n
  rw [A352286_eq_zero_iff]
  constructor
  · -- only if: non-representability forces `n` to be one of the four exceptions (OPEN)
    sorry
  · -- if: each of the four exceptions is non-representable
    intro hn
    simp only [A352286_exceptions, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    intro w x y z hw hc
    rcases hn with rfl | rfl | rfl | rfl
    · have hx : x ≤ 10 := sqrt_bound (show x ^ 2 ≤ 106 by omega) (by norm_num)
      have hy : y ≤ 7 := sqrt_bound (show y ^ 2 ≤ 53 by omega) (by norm_num)
      have hz : z ≤ 5 := sqrt_bound (show z ^ 2 ≤ 35 by omega) (by norm_num)
      exact bdd106 w (by omega) x hx y hy z hz hc
    · have hx : x ≤ 27 := sqrt_bound (show x ^ 2 ≤ 744 by omega) (by norm_num)
      have hy : y ≤ 19 := sqrt_bound (show y ^ 2 ≤ 372 by omega) (by norm_num)
      have hz : z ≤ 15 := sqrt_bound (show z ^ 2 ≤ 248 by omega) (by norm_num)
      exact bdd744 w (by omega) x hx y hy z hz hc
    · have hx : x ≤ 73 := sqrt_bound (show x ^ 2 ≤ 5469 by omega) (by norm_num)
      have hy : y ≤ 52 := sqrt_bound (show y ^ 2 ≤ 2734 by omega) (by norm_num)
      have hz : z ≤ 42 := sqrt_bound (show z ^ 2 ≤ 1823 by omega) (by norm_num)
      exact bdd5469 w (by omega) x hx y hy z hz hc
    · have hx : x ≤ 575 := sqrt_bound (show x ^ 2 ≤ 331269 by omega) (by norm_num)
      have hy : y ≤ 406 := sqrt_bound (show y ^ 2 ≤ 165634 by omega) (by norm_num)
      have hz : z ≤ 332 := sqrt_bound (show z ^ 2 ≤ 110423 by omega) (by norm_num)
      exact bdd331269 w (by omega) x hx y hy z hz hc
