import FormalConjectures.Util.ProblemImports

open List Nat

/-- The substitution rule for A284851: $0 \mapsto [0, 1]$, $1 \mapsto [0, 1, 0, 0]$. -/
def A284851_subst_rule : ℕ → List ℕ
| 0 => [0, 1]
| 1 => [0, 1, 0, 0]
| _ => []

/--
The sequence of finite prefixes of A284851.
$L_0 = [0]$. $L_{n+1} = L_n$.flatMap $A284851\_subst\_rule$.
-/
def A284851_list_at_step : ℕ → List ℕ
| 0 => [0]
| (n + 1) => (A284851_list_at_step n).flatMap A284851_subst_rule

/--
A proxy for the infinite word A284851.
We take the value from a large-enough prefix (10th iteration).
-/
noncomputable def A284851_value (n : ℕ) : ℕ :=
  (A284851_list_at_step 10).getD n 1

/--
A284852: Positions of 0 in A284851; complement of A284853.
The $n$-th term $a(n)$ is the sequence of 1-indexed positions $k$ such that $A284851(k-1) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is 1-indexed, so we find the (n-1)-th 0-indexed position k, and add 1.
  (n - 1).nth (fun k => A284851_value k = 0) + 1

-- The constant r = (3 + sqrt(3)) / 3
noncomputable def r : ℝ := (3 + Real.sqrt 3) / 3

/-!
The `A284851_value` function only inspects a finite prefix (`A284851_list_at_step 10`)
and returns the default value `1` for every index beyond that list.  Consequently the
predicate `fun k => A284851_value k = 0` holds for only finitely many `k`, so
`Nat.nth` of that predicate eventually returns `0` and `a n = 1` for all sufficiently
large `n`.  Since `r ≥ 1`, the quantity `n * r - a n` grows without bound, contradicting
the claimed bound `< 2`.  Hence the conjecture (as formalised) is false.
-/

private lemma subst_len (x : ℕ) : (A284851_subst_rule x).length ≤ 4 := by
  match x with
  | 0 => decide
  | 1 => decide
  | (n+2) => simp [A284851_subst_rule]

private lemma len_bound : ∀ n, (A284851_list_at_step n).length ≤ 4^n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    rw [A284851_list_at_step, List.length_flatMap]
    have hb : (List.map (fun a => (A284851_subst_rule a).length) (A284851_list_at_step k)).sum
        ≤ 4 * (A284851_list_at_step k).length := by
      have := List.sum_le_card_nsmul
        (List.map (fun a => (A284851_subst_rule a).length) (A284851_list_at_step k)) 4
        (by
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact subst_len y)
      simpa [List.length_map, Nat.mul_comm, smul_eq_mul] using this
    calc (List.map (fun a => (A284851_subst_rule a).length) (A284851_list_at_step k)).sum
        ≤ 4 * (A284851_list_at_step k).length := hb
      _ ≤ 4 * 4^k := Nat.mul_le_mul_left 4 ih
      _ = 4^(k+1) := by ring

private lemma a_large : a (4^10 + 1) = 1 := by
  unfold a
  have hp : ∀ k, A284851_value k = 0 → k < 4^10 := by
    intro k hk
    by_contra h
    push_neg at h
    have hlen : (A284851_list_at_step 10).length ≤ k := le_trans (len_bound 10) h
    unfold A284851_value at hk
    rw [List.getD_eq_default _ _ hlen] at hk
    exact absurd hk (by decide)
  have hsub : {k | A284851_value k = 0} ⊆ Set.Iio (4^10) := fun k hk => hp k hk
  have hfin : {k | A284851_value k = 0}.Finite := (Set.finite_Iio (4^10)).subset hsub
  have hcard : hfin.toFinset.card ≤ 4^10 := by
    have hsubf : hfin.toFinset ⊆ (Set.finite_Iio (4^10)).toFinset :=
      (Set.Finite.toFinset_subset_toFinset).2 hsub
    have := Finset.card_le_card hsubf
    rwa [show (Set.finite_Iio (4^10)).toFinset = Finset.Iio (4^10) by
      ext x; simp, Nat.card_Iio] at this
  have hzero : (4^10 + 1 - 1).nth (fun k => A284851_value k = 0) = 0 := by
    rw [show (4^10 + 1 - 1) = 4^10 by ring]
    exact Nat.nth_of_card_le hfin hcard
  rw [hzero]

/--
Conjecture A284852: -2 < n*r - a(n) < 2 for n >= 1, where r = (3+sqrt(3))/3.

This is **false** as formalised, because `A284851_value` uses only a finite prefix
(`A284851_list_at_step 10`) and thus `a n = 1` for all large `n`, while `n * r`
grows without bound.
-/
theorem oeis_284852_conjecture.disproof :
    ¬ (∀ (n : ℕ), 0 < n → abs ((n : ℝ) * r - (a n : ℝ)) < 2) := by
  intro h
  have hn := h (4^10 + 1) (by positivity)
  rw [a_large] at hn
  have hr : (1:ℝ) ≤ r := by
    have h3 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    unfold r
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith
  rw [abs_lt] at hn
  simp only [Nat.cast_one] at hn
  have hpos : (0:ℝ) ≤ ((4^10 + 1 : ℕ) : ℝ) := by positivity
  have hmul : ((4^10 + 1 : ℕ) : ℝ) ≤ ((4^10 + 1 : ℕ) : ℝ) * r := le_mul_of_one_le_right hpos hr
  have hc : (3:ℝ) ≤ ((4^10 + 1 : ℕ) : ℝ) := by norm_num
  linarith [hn.2, hmul, hc]
