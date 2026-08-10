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

/--
Conjecture A284852: -2 < n*r - a(n) < 2 for n >= 1, where r = (3+sqrt(3))/3.
-/
theorem oeis_284852_conjecture.disproof : ¬ (∀ (n : ℕ), 0 < n →
  abs ((n : ℝ) * r - (a n : ℝ)) < 2) := by
  intro h
  have ha : a 1048577 = 1 := by
    unfold a
    let p : ℕ → Prop := fun k => A284851_value k = 0
    have hnth : Nat.nth p 1048576 = 0 := by
      have hstep : ∀ l : List ℕ, (l.flatMap A284851_subst_rule).length ≤ 4 * l.length := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih =>
            rw [List.flatMap_cons, List.length_append]
            simp only [List.length_cons]
            have hx : (A284851_subst_rule x).length ≤ 4 := by
              cases x with
              | zero => simp [A284851_subst_rule]
              | succ x =>
                  cases x with
                  | zero => simp [A284851_subst_rule]
                  | succ x => simp [A284851_subst_rule]
            omega
      have hlen_bound_all : ∀ n : ℕ, (A284851_list_at_step n).length ≤ 4 ^ n := by
        intro n
        induction n with
        | zero => simp [A284851_list_at_step]
        | succ n ih =>
            calc
              (A284851_list_at_step (n + 1)).length
                  = ((A284851_list_at_step n).flatMap A284851_subst_rule).length := rfl
              _ ≤ 4 * (A284851_list_at_step n).length := hstep _
              _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 ih
              _ = 4 ^ (n + 1) := by exact (pow_succ' (4 : ℕ) n).symm
      have hlen_bound : (A284851_list_at_step 10).length ≤ 1048576 := by
        have h := hlen_bound_all 10
        norm_num at h ⊢
        exact h
      have ht : ({i : ℕ | i < 1048576} : Set ℕ).Finite := Set.finite_lt_nat 1048576
      have hsub : setOf p ⊆ ({i : ℕ | i < 1048576} : Set ℕ) := by
        intro k hk
        dsimp [p, A284851_value] at hk
        dsimp
        by_contra hnot
        have hle : (A284851_list_at_step 10).length ≤ k := by
          have hkge : 1048576 ≤ k := Nat.le_of_not_gt hnot
          omega
        have hget : (A284851_list_at_step 10).getD k 1 = 1 := List.getD_eq_default _ _ hle
        rw [hget] at hk
        norm_num at hk
      have hf : (setOf p).Finite := ht.subset hsub
      have hto : hf.toFinset ⊆ ht.toFinset := by
        exact (Set.Finite.toFinset_subset_toFinset).2 hsub
      have hcard_le : hf.toFinset.card ≤ ht.toFinset.card := Finset.card_le_card hto
      have htcard : ht.toFinset.card = 1048576 := by
        have htfinset : ht.toFinset = Finset.range 1048576 := by
          ext x
          simp
        rw [htfinset]
        simp
      exact Nat.nth_of_card_le hf (by omega)
    change Nat.nth (fun k => A284851_value k = 0) (1048577 - 1) + 1 = 1
    dsimp [p] at hnth
    norm_num
    exact hnth
  have hb := h 1048577 (by norm_num)
  rw [ha] at hb
  unfold r at hb
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hgt : (2 : ℝ) < (1048577 : ℝ) * ((3 + Real.sqrt 3) / 3) - 1 := by
    nlinarith [hsqrt_nonneg]
  have habs : 2 < abs ((1048577 : ℝ) * ((3 + Real.sqrt 3) / 3) - (1 : ℝ)) := by
    rw [abs_of_pos]
    · exact hgt
    · linarith
  linarith
