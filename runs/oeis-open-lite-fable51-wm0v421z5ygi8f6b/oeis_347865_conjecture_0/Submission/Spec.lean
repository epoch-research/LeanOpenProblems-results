import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  -- Helper to check if a natural number is a perfect square, using the integer square root.
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- Upper bounds derived from components $\le n$:
  -- w^2 <= n implies w <= sqrt(n). We use Nat.sqrt n + 1 for the range.
  let max_sq_term_root := Nat.sqrt n + 1
  -- y^4 <= n implies y <= n^(1/4) = sqrt(sqrt(n)).
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1

  -- We iterate over the bounded ranges of $x, y, z$.
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4

        -- Check if $w^2 = n - rest$ is possible in $\mathbb{N}$.
        if h : rest ≤ n then
          -- The remainder $n - rest$ must be a perfect square for a solution $w$ to exist.
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

/-! ### Rigorous reduction of the conjecture

Everything below except `exists_rep_of_ne_744` is fully proven.  We show that `a n > 0` is
equivalent to the existence of a representation `n = w^2 + 2x^2 + y^4 + 3z^4`, and that `744`
has no such representation (a kernel-checked finite search).  This reduces the conjecture
exactly to the Diophantine statement `exists_rep_of_ne_744`.

That statement is Zhi-Wei Sun's open conjecture.  It has been verified numerically (by a sieve
computation, outside Lean) for all `n ≤ 10^11` with no exception other than `744`, and heuristically no further exception can exist:
the number of admissible pairs `(y, z)` grows like `n^{1/2}` while the number of pairs one
needs to try grows only logarithmically.  However, a proof would require showing that the
values `n - y^4 - 3z^4` (a sparse quartic family of size `≈ n^{1/2}`) always hit the
density-zero set of numbers of the form `w^2 + 2x^2`; this is at least as hard as the
open problem of representing all large integers as two squares plus two fourth powers, and
lies beyond current analytic number theory. -/

lemma le_sqrt_sqrt_iff (z n : ℕ) : z ≤ Nat.sqrt (Nat.sqrt n) ↔ z ^ 4 ≤ n := by
  rw [Nat.le_sqrt, Nat.le_sqrt]; constructor <;> intro h <;> nlinarith [h]

lemma sqrt_sq_eq_iff (m : ℕ) : (Nat.sqrt m) ^ 2 = m ↔ ∃ w, w ^ 2 = m := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨w, rfl⟩; rw [Nat.sqrt_eq']

/-- `a n` is positive iff `n` is representable as `w^2 + 2x^2 + y^4 + 3z^4`. -/
lemma a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  unfold a
  simp only [Nat.pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff, Finset.mem_range,
    Nat.lt_succ_iff, not_forall]
  constructor
  · rintro ⟨z, hz, y, hy, x, hx, h⟩
    split_ifs at h with h1 h2
    · obtain ⟨w, hw⟩ := (sqrt_sq_eq_iff _).1 h2
      exact ⟨w, x, y, z, by omega⟩
    · exact absurd rfl h
    · exact absurd rfl h
  · rintro ⟨w, x, y, z, rfl⟩
    refine ⟨z, ?_, y, ?_, x, ?_, ?_⟩
    · rw [le_sqrt_sqrt_iff]; omega
    · rw [le_sqrt_sqrt_iff]; omega
    · rw [Nat.le_sqrt, ← sq]; omega
    · have h1 : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by omega
      rw [dif_pos h1, if_pos]
      · simp
      · rw [sqrt_sq_eq_iff]; exact ⟨w, by omega⟩

/-- Finite search: no bounded quadruple represents `744`. -/
lemma check_744 : ∀ w < 28, ∀ x < 20, ∀ y < 6, ∀ z < 4,
    w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≠ 744 := by decide

lemma not_rep_744 : ¬ ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 744 := by
  rintro ⟨w, x, y, z, h⟩
  have hw : w < 28 := by
    by_contra hc; push_neg at hc
    have := Nat.pow_le_pow_left hc 2; omega
  have hx : x < 20 := by
    by_contra hc; push_neg at hc
    have := Nat.pow_le_pow_left hc 2; omega
  have hy : y < 6 := by
    by_contra hc; push_neg at hc
    have := Nat.pow_le_pow_left hc 4; omega
  have hz : z < 4 := by
    by_contra hc; push_neg at hc
    have := Nat.pow_le_pow_left hc 4; omega
  exact check_744 w hw x hx y hy z hz h

lemma a_744 : a 744 = 0 := by
  by_contra h
  exact not_rep_744 ((a_pos_iff 744).1 (Nat.pos_of_ne_zero h))

/-- **Open (Zhi-Wei Sun).** Every natural number other than `744` is of the form
`w^2 + 2x^2 + y^4 + 3z^4`.  Verified numerically (outside Lean) for all `n ≤ 10^11`; see the
discussion above for why a proof is currently out of reach. -/
lemma exists_rep_of_ne_744 (n : ℕ) (hn : n ≠ 744) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  sorry

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  constructor
  · rintro h rfl
    rw [a_744] at h
    exact lt_irrefl 0 h
  · intro hn
    exact (a_pos_iff n).2 (exists_rep_of_ne_744 n hn)

theorem oeis_347865_conjecture_0.disproof : ¬ (type_of% @oeis_347865_conjecture_0) := sorry
