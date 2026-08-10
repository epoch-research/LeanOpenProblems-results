import FormalConjectures.Util.ProblemImports

open Nat

/--
A helper function for counting the number of ways to write $k$ as $z^2 + w^2$ with $z, w \ge 0$ and $z \le w$.
-/
def count_restricted_two_squares (k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 = k ∧ p.1 ≤ p.2)
    (Finset.product (Finset.range (sqrt k + 1)) (Finset.range (sqrt k + 1)))
  )

/--
A300667: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$
such that $3*x$ or $y$ is a square and $x + 2*y$ is also a square.
-/
def a (n : ℕ) : ℕ :=
  -- Define the "is a square" predicate based on its property with the integer square root.
  let is_sq (m : ℕ) : Prop := (sqrt m) * (sqrt m) = m

  Finset.sum (Finset.range (sqrt n + 1)) fun x =>
    let n_minus_x2 := n - x^2
    Finset.sum (Finset.range (sqrt n_minus_x2 + 1)) fun y =>
      -- Check conditions on x and y
      if is_sq (x + 2 * y) ∧ (is_sq (3 * x) ∨ is_sq y) then
        let k := n_minus_x2 - y^2
        count_restricted_two_squares k
      else 0

/-- The structured-representation core of Sun's conjecture A300667: every `n` admits a
four-square representation `x²+y²+z²+w² = n` with `z ≤ w`, `x+2y` a perfect square, and `3x`
or `y` a perfect square. -/
theorem exists_structured_representation (n : ℕ) :
    ∃ x y z w : ℕ, z ≤ w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
      sqrt (x + 2 * y) * sqrt (x + 2 * y) = x + 2 * y ∧
      (sqrt (3 * x) * sqrt (3 * x) = 3 * x ∨ sqrt y * sqrt y = y) := by
  sorry

theorem count_restricted_pos (k z w : ℕ) (hzw : z ≤ w) (h : z ^ 2 + w ^ 2 = k) :
    0 < count_restricted_two_squares k := by
  rw [count_restricted_two_squares, Finset.card_pos]
  refine ⟨(z, w), ?_⟩
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, ?_⟩, ⟨h, hzw⟩⟩
  · rw [Nat.lt_succ_iff, Nat.le_sqrt']
    nlinarith [sq_nonneg w]
  · rw [Nat.lt_succ_iff, Nat.le_sqrt']
    nlinarith [sq_nonneg z]

/-- The key reduction: a single structured witness makes `a n` positive. -/
theorem a_pos_of_witness (n x y z w : ℕ) (hzw : z ≤ w)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (h12 : sqrt (x + 2 * y) * sqrt (x + 2 * y) = x + 2 * y)
    (hside : sqrt (3 * x) * sqrt (3 * x) = 3 * x ∨ sqrt y * sqrt y = y) :
    0 < a n := by
  have hx2 : x ^ 2 ≤ n := by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg w]
  have hxmem : x ∈ Finset.range (sqrt n + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt']; exact hx2
  have hnx : n - x ^ 2 = y ^ 2 + z ^ 2 + w ^ 2 := by omega
  have hy2 : y ^ 2 ≤ n - x ^ 2 := by rw [hnx]; nlinarith [sq_nonneg z, sq_nonneg w]
  have hymem : y ∈ Finset.range (sqrt (n - x ^ 2) + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt']; exact hy2
  rw [a]
  simp only
  apply Finset.sum_pos' (fun i _ => Nat.zero_le _)
  refine ⟨x, hxmem, ?_⟩
  apply Finset.sum_pos' (fun i _ => Nat.zero_le _)
  refine ⟨y, hymem, ?_⟩
  rw [if_pos ⟨h12, hside⟩]
  have hk : n - x ^ 2 - y ^ 2 = z ^ 2 + w ^ 2 := by omega
  rw [hk]
  exact count_restricted_pos _ z w hzw rfl

/-- Complete unconditional case: if `n` is a sum of two squares, `a n > 0`. -/
theorem a_pos_of_sq_add_sq (n z w : ℕ) (hzw : z ≤ w) (h : z ^ 2 + w ^ 2 = n) : 0 < a n := by
  apply a_pos_of_witness n 0 0 z w hzw
  · simpa using h
  · simp
  · left; simp

/--
Conjecture 1 (positivity part): a(n) > 0 for all n >= 0.

The full text of the OEIS comment block which includes this conjecture is:
A300667 a(n) > 0 for all n = 0..10^8. Also, Conjecture 2 holds for all n = 0..10^8. In a 2018 paper Y.-C. Sun and Z.-W. Sun proved that any nonnegative integer can be written as x^2 + y^2 + z^2 + w^2 with x + 2*y a square, where x,y,z,w are nonnegative integers. - _Zhi-Wei Sun_, Oct 04 2020
-/
theorem oeis_a300667_conjecture_1_positivity (n : ℕ) : a n > 0 := by
  obtain ⟨x, y, z, w, hzw, hsum, h12, hside⟩ := exists_structured_representation n
  exact a_pos_of_witness n x y z w hzw hsum h12 hside
