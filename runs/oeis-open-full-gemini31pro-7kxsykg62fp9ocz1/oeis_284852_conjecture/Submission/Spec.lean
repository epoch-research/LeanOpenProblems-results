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
theorem oeis_284852_conjecture : ∀ (n : ℕ), 0 < n →
  abs ((n : ℝ) * r - (a n : ℝ)) < 2 := by sorry

lemma A284851_value_eq_one {k : ℕ} (hk : (A284851_list_at_step 10).length ≤ k) :
  A284851_value k = 1 := by
  dsimp [A284851_value]
  rw [List.getD_eq_default]
  exact hk

lemma A284851_value_zero_lt {k : ℕ} (hk : A284851_value k = 0) : k < (A284851_list_at_step 10).length := by
  by_contra! h
  have h1 := A284851_value_eq_one h
  rw [hk] at h1
  contradiction

lemma A284851_value_zero_finite : Set.Finite {k | A284851_value k = 0} := by
  apply Set.Finite.subset (Set.finite_Iio (A284851_list_at_step 10).length)
  intro k hk
  exact A284851_value_zero_lt hk

lemma a_val_large (n : ℕ) (hn : (A284851_list_at_step 10).length < n) : a n = 1 := by
  dsimp [a]
  rw [Nat.nth]
  have hF : (setOf (fun k => A284851_value k = 0)).Finite := A284851_value_zero_finite
  rw [dif_pos hF]
  have h_len : (hF.toFinset.sort fun a b ↦ a ≤ b).length = hF.toFinset.card := Finset.length_sort _
  have h_card : hF.toFinset.card ≤ (A284851_list_at_step 10).length := by
    calc hF.toFinset.card
      _ ≤ (Finset.range (A284851_list_at_step 10).length).card := by
        apply Finset.card_le_card
        intro x hx
        rw [Set.Finite.mem_toFinset] at hx
        rw [Finset.mem_range]
        exact A284851_value_zero_lt hx
      _ = (A284851_list_at_step 10).length := Finset.card_range _
  have h_bound : (hF.toFinset.sort fun a b ↦ a ≤ b).length ≤ n - 1 := by omega
  rw [List.getD_eq_default _ _ h_bound]

lemma r_gt_one_half : (3 : ℝ) / 2 < r := by
  dsimp [r]
  have h_sqrt : (1.5 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  calc (3 : ℝ) / 2 = (3 + 1.5) / 3 := by norm_num
    _ < (3 + Real.sqrt 3) / 3 := by gcongr

lemma r_pos : 0 < r := lt_trans (by norm_num) r_gt_one_half

theorem oeis_284852_conjecture.disproof : ¬ (type_of% @oeis_284852_conjecture) := by
  intro h
  let N := (A284851_list_at_step 10).length + 2
  have hN_pos : 0 < N := by omega
  have h_a_N : a N = 1 := a_val_large N (by omega)
  have h_ineq := h N hN_pos
  rw [h_a_N, Nat.cast_one] at h_ineq
  have h_abs : 2 < abs ((N : ℝ) * r - 1) := by
    have h1 : (2 : ℝ) < (N : ℝ) * r - 1 := by
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
        dsimp [N]
        exact_mod_cast Nat.le_add_left 2 _
      calc (2 : ℝ) = (2 : ℝ) * (3 / 2) - 1 := by norm_num
        _ < (2 : ℝ) * r - 1 := by gcongr; exact r_gt_one_half
        _ ≤ (N : ℝ) * r - 1 := by gcongr; exact r_pos.le
    exact lt_of_lt_of_le h1 (le_abs_self _)
  linarith
