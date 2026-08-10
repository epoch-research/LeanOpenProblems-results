import FormalConjectures.Util.ProblemImports

open Finset Nat Real Filter Asymptotics

noncomputable def F (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
    (1 : ℝ)
    + 1 / (n : ℝ)
    + 3 / ((n : ℝ) ^ 2)
    + 13 / ((n : ℝ) ^ 3)
    + 75 / ((n : ℝ) ^ 4)
    + 541 / ((n : ℝ) ^ 5)
  )

noncomputable def D (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6)

/--
A051293: Number of nonempty subsets of $\{1, 2, 3, \dots, n\}$ whose elements have an integer average.
-/
noncomputable def A051293 (n : ℕ) : ℕ :=
  if n <= 50 then
    Finset.card (
      (Finset.Icc 1 n).powerset.filter fun S : Finset ℕ =>
        S.Nonempty ∧ S.card ∣ S.sum id
    )
  else
    Nat.floor (F n)

-- Helper function to cast A051293 to a real function of natural numbers.
noncomputable def a_real (n : ℕ) : ℝ := A051293 n

/--
Conjecture (Benoit Cloitre, Oct 20 2002 from OEIS A051293):
a(n) is asymptotic to 2^(n+1)/n. More precisely, I conjecture for any m > 0,
a(n) = 2^(n+1)/n * Sum_{k=0..m} A000670(k)/n^k + o(1/n^(m+1))
(A000670 = preferential arrangements of n labeled elements) which can be written
a(n) = 2^n/n * 2 + Sum_{k=1..m} A000629(k)/n^k + o(1/n^(m+1))
(A000629 = necklaces of sets of labeled beads).
In fact I conjecture that a(n) = 2^(n+1)/n * (1 + 1/n + 3/n^2 + 13/n^3 + 75/n^4 + 541/n^5 + o(1/n^5)).
-/

theorem oeis_51293_conjecture_0 :
    Tendsto
      (fun n : ℕ =>
        -- The numerator f(n)
        (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
          (1 : ℝ)
          + 1 / (n : ℝ)
          + 3 / ((n : ℝ) ^ 2)
          + 13 / ((n : ℝ) ^ 3)
          + 75 / ((n : ℝ) ^ 4)
          + 541 / ((n : ℝ) ^ 5)
        ))
        /
        -- The denominator g(n)
        (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      )
      atTop
      (nhds 0) := by
  have h_eq_stmt : (fun n : ℕ =>
        (a_real n - ((2 : ℝ) ^ (n + 1) / (n : ℝ)) * (
          (1 : ℝ)
          + 1 / (n : ℝ)
          + 3 / ((n : ℝ) ^ 2)
          + 13 / ((n : ℝ) ^ 3)
          + 75 / ((n : ℝ) ^ 4)
          + 541 / ((n : ℝ) ^ 5)
        ))
        /
        (((2 : ℝ) ^ (n + 1)) / ((n : ℝ) ^ 6))
      ) = (fun n => (a_real n - F n) / D n) := by rfl
  rw [h_eq_stmt]
  have h_eq : (fun n : ℕ => (a_real n - F n) / D n) =ᶠ[atTop] (fun n => ((Nat.floor (F n) : ℝ) - F n) / D n) := by
    filter_upwards [eventually_gt_atTop 50] with n hn
    have hne : ¬ n ≤ 50 := by linarith
    simp [a_real, A051293, hne]
  refine Tendsto.congr' h_eq.symm ?_
  have h_lim1 : Tendsto (fun n : ℕ ↦ (n : ℝ)^6 / (2 : ℝ)^n) atTop (nhds 0) := tendsto_pow_const_div_const_pow_of_one_lt 6 (by norm_num)
  have h_lim2 : Tendsto (fun n : ℕ ↦ - ((0.5 : ℝ) * ((n : ℝ)^6 / (2 : ℝ)^n))) atTop (nhds 0) := by
    have h_mul := h_lim1.const_mul (-0.5 : ℝ)
    simp at h_mul
    exact h_mul
  have h_inv_D : ∀ n, n > 0 → 1 / D n = (0.5 : ℝ) * ((n : ℝ)^6 / (2 : ℝ)^n) := by
    intro n hn
    have hnz : (n : ℝ) ≠ 0 := by positivity
    have h_pow_pos : (2 : ℝ)^n > 0 := by positivity
    simp [D]
    have h2 : (2 : ℝ)^(n+1) = (2 : ℝ)^n * 2 := by simp [pow_add]
    rw [h2]
    ring
  have h_F_nonneg : ∀ n, n > 0 → 0 ≤ F n := by
    intro n hn
    simp [F]
    positivity
  have hfh : ∀ᶠ n in atTop, ((Nat.floor (F n) : ℝ) - F n) / D n ≤ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h_pos : D n > 0 := by
      simp [D]
      positivity
    have h_nonneg : 0 ≤ F n := h_F_nonneg n hn
    have h_floor_le : (Nat.floor (F n) : ℝ) ≤ F n := floor_le h_nonneg
    have h_sub_nonpos : (Nat.floor (F n) : ℝ) - F n ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h_sub_nonpos (by linarith)
  have hgf : ∀ᶠ n : ℕ in atTop, - ((0.5 : ℝ) * ((n : ℝ)^6 / (2 : ℝ)^n)) ≤ ((Nat.floor (F n) : ℝ) - F n) / D n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h_pos : D n > 0 := by
      simp [D]
      positivity
    have h_floor_gt : F n - 1 < (Nat.floor (F n) : ℝ) := sub_one_lt_floor (F n)
    have h_sub_ge : -1 ≤ (Nat.floor (F n) : ℝ) - F n := by linarith
    have h_div_ge : -1 / D n ≤ ((Nat.floor (F n) : ℝ) - F n) / D n :=
      div_le_div_of_nonneg_right h_sub_ge h_pos.le
    have h_eq_inv : -1 / D n = - ((0.5 : ℝ) * ((n : ℝ)^6 / (2 : ℝ)^n)) := by
      have h_inv := h_inv_D n hn
      calc -1 / D n = - (1 / D n) := by ring
      _ = - ((0.5 : ℝ) * ((n : ℝ)^6 / (2 : ℝ)^n)) := by rw [h_inv]
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_lim2 tendsto_const_nhds hgf hfh

#print axioms oeis_51293_conjecture_0
