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

/--
Reduction lemma: `a n > 0` holds iff `n` admits a representation `w^2 + 2x^2 + y^4 + 3z^4`.
This proves in particular that the truncated `Nat.sqrt` search bounds in `a` never miss a
genuine representation (the bounds `x ≤ √n`, `y,z ≤ √√n` are non-truncating). Uses only the
allowed axioms `propext, Classical.choice, Quot.sound`.
-/
theorem a_pos_iff (n : ℕ) :
    a n > 0 ↔ ∃ w x y z : ℕ, n = w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
  unfold a
  simp only [gt_iff_lt]
  constructor
  · intro h
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at h
    obtain ⟨z, _, h⟩ := h
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at h
    obtain ⟨y, _, h⟩ := h
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at h
    obtain ⟨x, _, h⟩ := h
    split_ifs at h with hle hps
    · refine ⟨Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)), x, y, z, ?_⟩
      have hw : Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)) ^ 2
          = n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := hps
      omega
    · exact absurd h (lt_irrefl 0)
    · exact absurd h (lt_irrefl 0)
  · rintro ⟨w, x, y, z, rfl⟩
    have hz4 : z ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by omega
    have hy4 : y ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by omega
    have hx2 : x ^ 2 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by omega
    set n := w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 with hn
    have hzb : z < Nat.sqrt (Nat.sqrt n) + 1 := by
      have : z ^ 2 ≤ Nat.sqrt n := by
        rw [Nat.le_sqrt']; calc (z ^ 2) ^ 2 = z ^ 4 := by ring
          _ ≤ n := hz4
      have : z ≤ Nat.sqrt (Nat.sqrt n) := by rw [Nat.le_sqrt']; exact this
      omega
    have hyb : y < Nat.sqrt (Nat.sqrt n) + 1 := by
      have : y ^ 2 ≤ Nat.sqrt n := by
        rw [Nat.le_sqrt']; calc (y ^ 2) ^ 2 = y ^ 4 := by ring
          _ ≤ n := hy4
      have : y ≤ Nat.sqrt (Nat.sqrt n) := by rw [Nat.le_sqrt']; exact this
      omega
    have hxb : x < Nat.sqrt n + 1 := by
      have : x ≤ Nat.sqrt n := by rw [Nat.le_sqrt']; exact hx2
      omega
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    refine ⟨z, Finset.mem_range.mpr hzb, ?_⟩
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    refine ⟨y, Finset.mem_range.mpr hyb, ?_⟩
    rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
    refine ⟨x, Finset.mem_range.mpr hxb, ?_⟩
    have hle : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n := by omega
    rw [dif_pos hle]
    have hrest : n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) = w ^ 2 := by omega
    rw [hrest, Nat.sqrt_eq']
    simp

/--
Base case: `744` is not representable. Proved by bounding the four variables and a finite
`decide` over the resulting box (pure arithmetic; only the allowed axioms are used).
-/
theorem not_rep_744 : ¬ ∃ w x y z : ℕ, (744 : ℕ) = w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
  rintro ⟨w, x, y, z, h⟩
  have hw2 : w ^ 2 ≤ 744 := by omega
  have hx2 : x ^ 2 ≤ 372 := by omega
  have hy4 : y ^ 4 ≤ 744 := by omega
  have hz4 : z ^ 4 ≤ 248 := by omega
  have hw : w < 28 := by nlinarith [hw2]
  have hx : x < 20 := by nlinarith [hx2]
  have hy : y < 6 := by
    by_contra hc; push_neg at hc
    have : (1296 : ℕ) ≤ y ^ 4 := by
      calc (1296 : ℕ) = 6 ^ 4 := by norm_num
        _ ≤ y ^ 4 := Nat.pow_le_pow_left hc 4
    omega
  have hz : z < 4 := by
    by_contra hc; push_neg at hc
    have : (256 : ℕ) ≤ z ^ 4 := by
      calc (256 : ℕ) = 4 ^ 4 := by norm_num
        _ ≤ z ^ 4 := Nat.pow_le_pow_left hc 4
    omega
  have key : ∀ w < 28, ∀ x < 20, ∀ y < 6, ∀ z < 4,
      (744 : ℕ) ≠ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by decide
  exact key w hw x hx y hy z hz h

/--
Covering lemma: every `n ≠ 744` is representable as `w^2 + 2x^2 + y^4 + 3z^4`.

This is the substantive content of the conjecture (OEIS A347865, due to Zhi-Wei Sun). It is
equivalent to `{w²+2x²} + {y⁴+3z⁴} ⊇ ℕ \ {744}`. It has been verified true for all `n ≤ 10¹⁰`,
but a proof is an open problem: it is an exception-free additive covering by the density-0 set
`{w²+2x²}` shifted by the sparse quartic set `{y⁴+3z⁴}`. No finite reduction exists (a finite
union of shifts of a density-0 set cannot be cofinite, so the number of representation types
needed grows without bound), and the circle method only yields an "almost all" statement.
-/
theorem covering (n : ℕ) (hn : n ≠ 744) :
    ∃ w x y z : ℕ, n = w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
  sorry

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  rw [a_pos_iff]
  constructor
  · intro h hn
    subst hn
    exact not_rep_744 h
  · exact covering n
