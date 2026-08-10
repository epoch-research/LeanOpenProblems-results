import FormalConjectures.Util.ProblemImports

open Nat

/--
A286885: Number of ways to write $6n+1$ as $x^2 + 3y^2 + 54z^2$ with $x,y,z$ nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  -- Maximum possible values for x, y, and z, giving tight bounds for the search space.
  -- x_max = floor(sqrt(N))
  let X_max : ℕ := N.sqrt
  -- y_max = floor(sqrt(N/3))
  let Y_max : ℕ := (N / 3).sqrt
  -- z_max = floor(sqrt(N/54))
  let Z_max : ℕ := (N / 54).sqrt

  -- The search sets for each variable.
  let X_set : Finset ℕ := Finset.range (X_max + 1)
  let Y_set : Finset ℕ := Finset.range (Y_max + 1)
  let Z_set : Finset ℕ := Finset.range (Z_max + 1)

  -- The Finset of all candidate triples $(x, y, z)$, structured as $ℕ \times (ℕ \times ℕ)$.
  let Candidates : Finset (ℕ × ℕ × ℕ) := Finset.product X_set (Finset.product Y_set Z_set)

  -- The result is the cardinality of the filtered set that satisfies the Diophantine equation.
  Finset.card <| Candidates.filter
    (fun p : ℕ × (ℕ × ℕ) =>
      let x := p.fst
      let y := p.snd.fst
      let z := p.snd.snd
      x^2 + 3 * y^2 + 54 * z^2 = N)

/--
The arithmetic core of A286885: every number of the form `6 * n + 1` is represented by the
ternary quadratic form `x² + 3y² + 54z²`.

This is the substantive content of Zhi-Wei Sun's conjecture.  The form is *irregular*
(for example it does not represent `10`, even though `10` is represented everywhere locally,
i.e. by the other class in its genus), so this is a genuine *spinor genus* statement and not a
mere congruence condition.  Indeed it is equivalent to:
`∀ N ≡ 1 (mod 6), ∃ t, N - 54 t²` is of the form `x² + 3y²`.
-/
theorem oeis_286885_exists (n : ℕ) : ∃ x y z : ℕ, x ^ 2 + 3 * y ^ 2 + 54 * z ^ 2 = 6 * n + 1 := by
  sorry

/--
Conjecture: a(n) > 0 for all n = 0,1,2,....

The reduction below is complete and rigorous: `a n` is, by construction, the number of triples
`(x, y, z)` within the (sufficient) search bounds satisfying `x² + 3y² + 54z² = 6n+1`, so it is
positive exactly when a representation exists.  We supply an explicit witness from
`oeis_286885_exists` and verify it lies in the search box (the floor-sqrt bounds are large enough
because any solution satisfies `x² ≤ N`, `3y² ≤ N`, `54z² ≤ N`).
-/
theorem oeis_286885_conjecture_0 : ∀ n : ℕ, a n > 0 := by
  intro n
  obtain ⟨x, y, z, hxyz⟩ := oeis_286885_exists n
  rw [a]
  simp only
  rw [gt_iff_lt, Finset.card_pos]
  refine ⟨(x, (y, z)), ?_⟩
  rw [Finset.mem_filter]
  constructor
  · refine Finset.mk_mem_product ?_ (Finset.mk_mem_product ?_ ?_)
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt']
      calc x ^ 2 ≤ x ^ 2 + 3 * y ^ 2 + 54 * z ^ 2 := by omega
        _ = 6 * n + 1 := hxyz
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt', Nat.le_div_iff_mul_le (by norm_num)]
      calc y ^ 2 * 3 = 3 * y ^ 2 := by ring
        _ ≤ x ^ 2 + 3 * y ^ 2 + 54 * z ^ 2 := by omega
        _ = 6 * n + 1 := hxyz
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt', Nat.le_div_iff_mul_le (by norm_num)]
      calc z ^ 2 * 54 = 54 * z ^ 2 := by ring
        _ ≤ x ^ 2 + 3 * y ^ 2 + 54 * z ^ 2 := by omega
        _ = 6 * n + 1 := hxyz
  · simp only
    exact hxyz
