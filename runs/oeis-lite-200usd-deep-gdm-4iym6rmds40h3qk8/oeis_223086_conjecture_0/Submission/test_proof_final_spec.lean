import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000000

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def T : ℕ → ℕ
  | 0 => 65
  | i + 1 => (4 * T i + 3) / 3

lemma T_le_succ (a : ℕ) : T a ≤ T (a + 1) := by
  dsimp [T]
  omega

lemma T_monotone (i j : ℕ) (h : i ≤ j) : T i ≤ T j := by
  induction j generalizing i with
  | zero =>
    have h_eq : i = 0 := by omega
    subst h_eq
    exact le_refl _
  | succ j ih =>
    by_cases h_eq : i = j + 1
    · subst h_eq
      exact le_refl _
    · have h_le : i ≤ j := by omega
      have ih_val := ih i h_le
      have h_succ := T_le_succ j
      exact le_trans ih_val h_succ

lemma T_spec (i : ℕ) (x : ℕ) (hx : x ≥ T (i + 1)) : A006368_map x ≥ T i := by
  have h_map : A006368_map x ≥ (3 * x - 1) / 4 := by
    unfold A006368_map
    split_ifs with h1 h2 h3 <;> omega
  have h_T : T (i + 1) = (4 * T i + 3) / 3 := rfl
  rw [h_T] at hx
  omega

lemma T_iterate_spec (i : ℕ) (k : ℕ) (x : ℕ) (hx : x ≥ T (i + k)) : A006368_map^[k] x ≥ T i := by
  induction k generalizing x i with
  | zero =>
    exact hx
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have h_step : A006368_map x ≥ T (i + k) := by
      have hx' : x ≥ T (i + k + 1) := by
        have h_eq : i + (k + 1) = i + k + 1 := by omega
        rw [h_eq] at hx
        exact hx
      exact T_spec (i + k) x hx'
    exact ih i (A006368_map x) h_step

lemma T_iterate_spec_zero (k : ℕ) (x : ℕ) (hx : x ≥ T k) : A006368_map^[k] x ≠ 64 := by
  have h1 : A006368_map^[k] x ≥ T 0 := by
    have h_eq : T k = T (0 + k) := by
      have h0 : 0 + k = k := by omega
      rw [h0]
    rw [h_eq] at hx
    exact T_iterate_spec 0 k x hx
  have h_T0 : T 0 = 65 := rfl
  rw [h_T0] at h1
  omega

def B : ℕ := 100000000000000000000000000000000000

def my_map (k : ℕ) : ℕ :=
  if k ≤ B then
    A006368_map k
  else
    B + k

lemma iterate_large (k : ℕ) (x : ℕ) (hx : x > B) : my_map^[k] x > B := by
  induction k generalizing x with
  | zero =>
    exact hx
  | succ k ih =>
    have h_next : my_map x > B := by
      unfold my_map A006368_map
      split_ifs <;> omega
    exact ih (my_map x) h_next

lemma step1 : my_map^[100] 64 = 11574 := by decide
lemma step2 : my_map^[100] 11574 = 2089746 := by decide
lemma step3 : my_map^[100] 2089746 = 47162797 := by decide
lemma step4 : my_map^[100] 47162797 = 139513299931002 := by decide
lemma step5 : my_map^[100] 139513299931002 = 100756188284683804 := by decide
lemma step6 : my_map^[100] 100756188284683804 = 4657016978965305652129 := by decide
lemma step7 : my_map^[100] 4657016978965305652129 = 105102721346651848180727 := by decide
lemma step8 : my_map^[100] 105102721346651848180727 = 607239572799050767489311236 := by decide
lemma step9 : my_map^[100] 607239572799050767489311236 = 219273520019636635525971950843 := by decide
lemma step10 : my_map^[100] 219273520019636635525971950843 = 9897427377833507869287616648508 := by decide

lemma my_map_iterate_1000 : my_map^[1000] 64 = 9897427377833507869287616648508 := by
  have h1 : my_map^[100] 64 = 11574 := step1
  have h2 : my_map^[200] 64 = 2089746 := by
    rw [show 200 = 100 + 100 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h1, step2]
  have h3 : my_map^[300] 64 = 47162797 := by
    rw [show 300 = 100 + 200 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h2, step3]
  have h4 : my_map^[400] 64 = 139513299931002 := by
    rw [show 400 = 100 + 300 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h3, step4]
  have h5 : my_map^[500] 64 = 100756188284683804 := by
    rw [show 500 = 100 + 400 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h4, step5]
  have h6 : my_map^[600] 64 = 4657016978965305652129 := by
    rw [show 600 = 100 + 500 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h5, step6]
  have h7 : my_map^[700] 64 = 105102721346651848180727 := by
    rw [show 700 = 100 + 600 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h6, step7]
  have h8 : my_map^[800] 64 = 607239572799050767489311236 := by
    rw [show 800 = 100 + 700 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h7, step8]
  have h9 : my_map^[900] 64 = 219273520019636635525971950843 := by
    rw [show 900 = 100 + 800 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h8, step9]
  rw [show 1000 = 100 + 900 by omega, Function.iterate_add]
  dsimp only [Function.comp_apply]
  rw [h9, step10]

lemma my_map_iterate_le_B (i : ℕ) (hi : i ≤ 1000) : my_map^[i] 64 ≤ B := by
  by_contra h_gt
  push_neg at h_gt
  have h_large := iterate_large (1000 - i) (my_map^[i] 64) h_gt
  have h_eq : (1000 - i) + i = 1000 := by omega
  rw [← Function.iterate_add, h_eq] at h_large
  have h_val := my_map_iterate_1000
  unfold B at h_large
  rw [h_val] at h_large
  revert h_large
  decide

lemma A006368_map_iterate_eq_my_map (i : ℕ) (hi : i ≤ 1000) : A006368_map^[i] 64 = my_map^[i] 64 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_le : i ≤ 1000 := by omega
    have ih_val := ih hi_le
    rw [Function.iterate_succ', Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    rw [ih_val]
    have h_le := my_map_iterate_le_B i hi_le
    unfold my_map
    rw [if_pos h_le]

lemma V_1000_ge_T_89 : A006368_map^[1000] 64 ≥ T 89 := by
  have h_eq : A006368_map^[1000] 64 = 9897427377833507869287616648508 := by
    rw [A006368_map_iterate_eq_my_map 1000 (by omega)]
    exact my_map_iterate_1000
  rw [h_eq]
  decide
