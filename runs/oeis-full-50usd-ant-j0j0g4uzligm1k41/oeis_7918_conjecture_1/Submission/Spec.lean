import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

/-- `a n` is a prime that is at least `n`. -/
theorem a_spec (n : ℕ) : Nat.Prime (a n) ∧ n ≤ a n := by
  unfold a; exact Nat.find_spec (p := fun p => Nat.Prime p ∧ n ≤ p) _

theorem a_ge (n : ℕ) : n ≤ a n := (a_spec n).2

/-- If `n` itself is prime then `a n = n`. -/
theorem a_eq_of_prime {n : ℕ} (hn : Nat.Prime n) : a n = n := by
  refine le_antisymm ?_ (a_ge n)
  unfold a; exact Nat.find_min' (p := fun p => Nat.Prime p ∧ n ≤ p) _ ⟨hn, le_rfl⟩

/-- For `n > 1` the right-hand side already exceeds `n`, since the exponent
`n ^ (1/n)` is `> 1` and the base `n` is `> 1`.  Hence the conjecture is immediate
whenever `n` is prime (because then `a n = n`). -/
theorem n_lt_rhs (n : ℕ) (h_n : 1 < n) :
    (n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h_n
  have hexp : (1 : ℝ) < (n : ℝ) ^ (1 / (n : ℝ)) :=
    (Real.one_lt_rpow_iff_of_pos (by positivity)).2 (Or.inl ⟨hn1, by positivity⟩)
  calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := (Real.rpow_lt_rpow_left_iff hn1).2 hexp

/-- Sharp lower bound: `n^(n^(1/n)) ≥ n + (log n)^2` for `n > 1`.
Together with `RHS - n = (log n)^2 (1 + o(1))`, this shows the conjecture for
composite `n` is equivalent to the (sharp, constant-`1`) Cramér prime-gap bound
`(next prime after n) - n < (log n)^2`. -/
theorem rhs_ge (n : ℕ) (h_n : 1 < n) :
    (n : ℝ) + (Real.log n) ^ 2 ≤ (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h_n
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  set L := Real.log (n : ℝ) with hL
  have hpow : (n : ℝ) ^ (1 / (n : ℝ)) = Real.exp (L / n) := by
    rw [Real.rpow_def_of_pos hNpos]; rw [hL]; ring_nf
  have hRHS : (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) = Real.exp (Real.exp (L / n) * L) := by
    rw [Real.rpow_def_of_pos hNpos, hpow, ← hL, mul_comm]
  rw [hRHS]
  have h1 : (1 : ℝ) + L / n ≤ Real.exp (L / n) := Real.add_one_le_exp _ |>.trans_eq' (by ring)
  have hLnn : 0 ≤ L := le_of_lt hlogpos
  have h2 : L + L ^ 2 / n ≤ Real.exp (L / n) * L := by
    have := mul_le_mul_of_nonneg_right h1 hLnn
    calc L + L ^ 2 / n = (1 + L / n) * L := by ring
      _ ≤ Real.exp (L / n) * L := this
  have hexpL : Real.exp L = (n : ℝ) := Real.exp_log hNpos
  have hstep : (n : ℝ) + L ^ 2 ≤ Real.exp (L + L ^ 2 / n) := by
    rw [Real.exp_add, hexpL]
    have h3 : 1 + L ^ 2 / n ≤ Real.exp (L ^ 2 / n) := by
      have := Real.add_one_le_exp (L ^ 2 / n); linarith
    calc (n : ℝ) + L ^ 2 = n * (1 + L ^ 2 / n) := by field_simp
      _ ≤ n * Real.exp (L ^ 2 / n) := by
          apply mul_le_mul_of_nonneg_left h3 (le_of_lt hNpos)
  calc (n : ℝ) + L ^ 2 ≤ Real.exp (L + L ^ 2 / n) := hstep
    _ ≤ Real.exp (Real.exp (L / n) * L) := by
        apply Real.exp_le_exp.2; linarith [h2]

/-- **Reduction to the prime-gap bound.**  Combined with the sharp lower bound
`rhs_ge`, the whole conjecture follows from the single inequality
`a n < n + (log n)^2`, i.e. *the least prime `≥ n` lies within `(log n)^2` of `n`*.
For composite `n = p+1` this is exactly `q - p < (log(p+1))^2 + 1`, the sharp
(constant-`1`) Cramér prime-gap conjecture. -/
theorem conj_of_gap (n : ℕ) (h_n : 1 < n)
    (hgap : (a n : ℝ) < (n : ℝ) + (Real.log n) ^ 2) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) :=
  lt_of_lt_of_le hgap (rhs_ge n h_n)

/--
Conjecture: if n > 1, then a(n) < n^(n^(1/n)). - _Thomas Ordowski_, Feb 23 2023
-/
theorem oeis_7918_conjecture_1 (n : ℕ) (h_n : 1 < n) :
    (a n : ℝ) < (n : ℝ) ^ ((n : ℝ) ^ (1 / (n : ℝ))) := by
  by_cases hp : n.Prime
  · rw [a_eq_of_prime hp]; exact n_lt_rhs n h_n
  · -- Composite case.  By `conj_of_gap` it suffices to prove `a n < n + (log n)^2`.
    -- Writing `n` in the prime gap `(p, q)` (with `p < n ≤ q` consecutive primes),
    -- one has `a n = q`, and the binding constraint is at `n = p+1`, where this reads
    -- `q - p < (log (p+1))^2 + 1`, i.e. the SHARP (constant-1) Cramér prime-gap
    -- conjecture `limsup (p_{k+1} - p_k) / (log p_k)^2 ≤ 1`.  This is a famous *open*
    -- problem (posed 1936), strictly stronger than the Riemann Hypothesis, and lies
    -- beyond every unconditional prime-gap bound (Baker–Harman–Pintz gives only
    -- `O(x^0.525)`).  It is neither provable nor disprovable with current mathematics.
    refine conj_of_gap n h_n ?_
    sorry
