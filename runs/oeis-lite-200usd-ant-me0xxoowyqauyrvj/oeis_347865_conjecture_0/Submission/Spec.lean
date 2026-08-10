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

/-- The counting function `a n` is positive iff `n` admits at least one representation
`n = w^2 + 2 x^2 + y^4 + 3 z^4`.  The search ranges in `a` are wide enough to capture every
representation, since each summand is `≤ n`. -/
theorem a_pos_iff (n : ℕ) :
    0 < a n ↔ ∃ w x y z : ℕ, n = w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
  constructor
  · intro hpos
    simp only [a, Finset.sum_pos_iff, Finset.mem_range] at hpos
    obtain ⟨z, _, y, _, x, _, hx⟩ := hpos
    split_ifs at hx with hrest hsq
    · exact ⟨Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)), x, y, z, by
        have hw : (Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4))) ^ 2
            = n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := hsq
        omega⟩
    · exact absurd hx (lt_irrefl 0)
    · exact absurd hx (lt_irrefl 0)
  · rintro ⟨w, x, y, z, rfl⟩
    set N := w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 with hN
    rw [a]
    apply Finset.sum_pos'
    · intro i _
      exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => by positivity))
    · refine ⟨z, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hz2 : z ^ 2 ≤ Nat.sqrt N := by
          rw [Nat.le_sqrt]
          nlinarith [sq_nonneg w, sq_nonneg x, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
        have : z ≤ Nat.sqrt (Nat.sqrt N) := by rw [Nat.le_sqrt]; nlinarith [hz2]
        omega
      · apply Finset.sum_pos'
        · intro j _; exact Finset.sum_nonneg (fun k _ => by positivity)
        · refine ⟨y, ?_, ?_⟩
          · rw [Finset.mem_range]
            have hy2 : y ^ 2 ≤ Nat.sqrt N := by
              rw [Nat.le_sqrt]
              nlinarith [sq_nonneg w, sq_nonneg x, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
            have : y ≤ Nat.sqrt (Nat.sqrt N) := by rw [Nat.le_sqrt]; nlinarith [hy2]
            omega
          · apply Finset.sum_pos'
            · intro k _; positivity
            · refine ⟨x, ?_, ?_⟩
              · rw [Finset.mem_range]
                have : x ≤ Nat.sqrt N := by
                  rw [Nat.le_sqrt]
                  nlinarith [sq_nonneg w, sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
                omega
              · simp only
                have hle : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ N := by rw [hN]; nlinarith [sq_nonneg w]
                rw [dif_pos hle, if_pos]
                · norm_num
                · show Nat.sqrt (N - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)) ^ 2
                      = N - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)
                  have : N - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) = w ^ 2 := by rw [hN]; omega
                  rw [this, Nat.sqrt_eq']

set_option maxRecDepth 100000 in
/-- `744` admits no representation `744 = w^2 + 2 x^2 + y^4 + 3 z^4`
(verified by a finite search over the necessarily bounded ranges of `w, x, y, z`). -/
theorem not_rep_744 : ¬ ∃ w x y z : ℕ, 744 = w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
  have key : ∀ w ∈ Finset.range 28, ∀ x ∈ Finset.range 21, ∀ y ∈ Finset.range 6,
      ∀ z ∈ Finset.range 5, 744 ≠ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by decide
  rintro ⟨w, x, y, z, h⟩
  have hw2 : w ^ 2 ≤ 744 := by omega
  have hx2 : x ^ 2 ≤ 372 := by omega
  have hy4 : y ^ 4 ≤ 744 := by omega
  have hz4 : z ^ 4 ≤ 248 := by omega
  have hw : w < 28 := by
    by_contra hc; push_neg at hc
    have : (28 : ℕ) ^ 2 ≤ w ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at this; omega
  have hx : x < 21 := by
    by_contra hc; push_neg at hc
    have : (21 : ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at this; omega
  have hy : y < 6 := by
    by_contra hc; push_neg at hc
    have : (6 : ℕ) ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left hc 4
    norm_num at this; omega
  have hz : z < 5 := by
    by_contra hc; push_neg at hc
    have : (5 : ℕ) ^ 4 ≤ z ^ 4 := Nat.pow_le_pow_left hc 4
    norm_num at this; omega
  exact key w (mem_range.2 hw) x (mem_range.2 hx) y (mem_range.2 hy) z (mem_range.2 hz) h

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  constructor
  · -- If `n` is representable then `n ≠ 744`, since `744` is not representable.
    intro hpos hne
    subst hne
    exact not_rep_744 ((a_pos_iff 744).1 hpos)
  · -- Every `n ≠ 744` is representable.  This is the substantive (open) direction of A347865.
    intro hne
    rw [gt_iff_lt, a_pos_iff]
    sorry
