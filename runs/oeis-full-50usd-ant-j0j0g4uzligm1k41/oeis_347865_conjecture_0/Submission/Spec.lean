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

/-- If `a n` is positive then `n` admits a representation `w^2 + 2x^2 + y^4 + 3z^4`. -/
theorem a_pos_imp (n : ℕ) (h : 0 < a n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  unfold a at h
  simp only at h
  replace h := h.ne'
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  refine ⟨Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)), x, y, z, ?_⟩
  by_cases hle : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n
  · rw [dif_pos hle] at hx
    by_cases hps :
        Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)) ^ 2 = n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)
    · rw [hps]; omega
    · rw [if_neg hps] at hx; exact absurd rfl hx
  · rw [dif_neg hle] at hx; exact absurd rfl hx

/-- A representation with the witnesses inside the iteration ranges makes `a n` positive. -/
theorem a_pos_of_rep (n w x y z : ℕ)
    (hz : z < Nat.sqrt (Nat.sqrt n) + 1)
    (hy : y < Nat.sqrt (Nat.sqrt n) + 1)
    (hx : x < Nat.sqrt n + 1)
    (hrep : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : 0 < a n := by
  have hrest : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n := by nlinarith [hrep, sq_nonneg w]
  have hsub : n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) = w ^ 2 := by omega
  have hps :
      Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4)) ^ 2 = n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := by
    rw [hsub, Nat.sqrt_eq']
  unfold a
  simp only
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨z, Finset.mem_range.mpr hz, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨y, Finset.mem_range.mpr hy, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨x, Finset.mem_range.mpr hx, ?_⟩
  rw [dif_pos hrest, if_pos hps]
  norm_num

/-- Any representation makes `a n` positive: the iteration ranges are always large enough. -/
theorem a_pos_of_rep' (n w x y z : ℕ)
    (hrep : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : 0 < a n := by
  apply a_pos_of_rep n w x y z _ _ _ hrep
  · have h1 : z ^ 2 ≤ Nat.sqrt n := by
      apply Nat.le_sqrt'.mpr; nlinarith [hrep, sq_nonneg w, sq_nonneg x, sq_nonneg (y ^ 2)]
    have : z ≤ Nat.sqrt (Nat.sqrt n) := Nat.le_sqrt'.mpr h1
    omega
  · have h1 : y ^ 2 ≤ Nat.sqrt n := by
      apply Nat.le_sqrt'.mpr; nlinarith [hrep, sq_nonneg w, sq_nonneg x, sq_nonneg (z ^ 2)]
    have : y ≤ Nat.sqrt (Nat.sqrt n) := Nat.le_sqrt'.mpr h1
    omega
  · have : x ≤ Nat.sqrt n := by
      apply Nat.le_sqrt'.mpr; nlinarith [hrep, sq_nonneg w, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
    omega

/-- `744` has no representation `w^2 + 2x^2 + y^4 + 3z^4`, verified by a finite check. -/
private theorem not_rep_744 : ∀ w ∈ Finset.range 28, ∀ x ∈ Finset.range 20,
    ∀ y ∈ Finset.range 6, ∀ z ∈ Finset.range 4,
    w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≠ 744 := by decide

/-- **Sun's conjecture (A347865).** Every `n ≠ 744` is a sum `w^2 + 2x^2 + y^4 + 3z^4`. -/
theorem sun_representability (n : ℕ) (hn : n ≠ 744) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  sorry

/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  constructor
  · intro h hn
    subst hn
    obtain ⟨w, x, y, z, hrep⟩ := a_pos_imp 744 h
    have hw : w < 28 := by nlinarith [hrep, sq_nonneg x, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
    have hx : x < 20 := by nlinarith [hrep, sq_nonneg w, sq_nonneg (y ^ 2), sq_nonneg (z ^ 2)]
    have hy : y < 6 := by
      by_contra hc; push_neg at hc
      have : (6 : ℕ) ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left hc 4
      nlinarith [hrep, sq_nonneg w, sq_nonneg x, sq_nonneg (z ^ 2)]
    have hz : z < 4 := by
      by_contra hc; push_neg at hc
      have : (4 : ℕ) ^ 4 ≤ z ^ 4 := Nat.pow_le_pow_left hc 4
      nlinarith [hrep, sq_nonneg w, sq_nonneg x, sq_nonneg (y ^ 2)]
    exact not_rep_744 w (Finset.mem_range.mpr hw) x (Finset.mem_range.mpr hx)
      y (Finset.mem_range.mpr hy) z (Finset.mem_range.mpr hz) hrep
  · intro hn
    obtain ⟨w, x, y, z, hrep⟩ := sun_representability n hn
    exact a_pos_of_rep' n w x y z hrep
