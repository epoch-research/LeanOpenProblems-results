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

def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

lemma f_g_eq (y : ℕ) : A006368_map (g y) = y := by
  unfold A006368_map g
  split_ifs with h1 h2 h3 h4 h5 <;> omega

lemma g_f_eq (x : ℕ) : g (A006368_map x) = x := by
  unfold A006368_map g
  split_ifs with h1 h2 h3 h4 h5 <;> omega

theorem f_iterate_eq_g_iterate (s : ℕ) (x : ℕ) : A006368_map^[s] x = 64 ↔ x = g^[s] 64 := by
  induction s generalizing x with
  | zero =>
    dsimp
    constructor <;> intro h <;> exact h
  | succ s ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [ih (A006368_map x)]
    rw [Function.iterate_succ', Function.comp_apply]
    constructor
    · intro h
      have h2 : g (A006368_map x) = g (g^[s] 64) := by rw [h]
      rw [g_f_eq] at h2
      exact h2
    · intro h
      have h2 : A006368_map x = A006368_map (g (g^[s] 64)) := by rw [h]
      rw [f_g_eq] at h2
      exact h2

lemma g_iterate_lt_T (s : ℕ) : g^[s] 64 < T s := by
  by_contra h
  push_neg at h
  have h1 := T_iterate_spec_zero s (g^[s] 64) h
  have h2 : A006368_map^[s] (g^[s] 64) = 64 := by
    rw [f_iterate_eq_g_iterate]
  contradiction

def B : ℕ := 100000000000000000000000000000000000 -- 10^35

def my_map (k : ℕ) : ℕ :=
  if k ≤ B then
    A006368_map k
  else
    B + k

theorem my_map_injective : ∀ x y, my_map x = my_map y → x = y := by
  intro x y h
  unfold my_map A006368_map at h
  split_ifs at h <;> omega

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
lemma step11 : my_map^[100] 9897427377833507869287616648508 = 435545354785631173804541675568346905 := by decide

lemma iterate_1100_eq : my_map^[1100] 64 = 435545354785631173804541675568346905 := by
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
  have h10 : my_map^[1000] 64 = 9897427377833507869287616648508 := by
    rw [show 1000 = 100 + 900 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h9, step10]
  rw [show 1100 = 100 + 1000 by omega, Function.iterate_add]
  dsimp only [Function.comp_apply]
  rw [h10, step11]

lemma iterate_1100_large : my_map^[1100] 64 > B := by
  rw [iterate_1100_eq]
  decide

def check_orbit (x : ℕ) (steps : ℕ) : Bool :=
  if x == 64 then
    false
  else
    match steps with
    | 0 => true
    | n + 1 => check_orbit (my_map x) n

theorem check_orbit_eq_true : check_orbit (my_map 64) 1100 = true := by
  decide

lemma check_orbit_spec (x : ℕ) (steps : ℕ) (h : check_orbit x steps = true) :
  ∀ d, d ≤ steps → my_map^[d] x ≠ 64 := by
  induction steps generalizing x with
  | zero =>
    intro d hd
    have hd_eq : d = 0 := by omega
    subst hd_eq
    dsimp only [Function.iterate_zero, id_eq]
    intro h_eq
    subst h_eq
    dsimp [check_orbit] at h
    cases h
  | succ n ih =>
    intro d hd
    by_cases hx : x = 64
    · subst hx
      dsimp [check_orbit] at h
      cases h
    · cases d with
      | zero =>
        dsimp only [Function.iterate_zero, id_eq]
        exact hx
      | succ d =>
        have hd_le : d ≤ n := by omega
        have h_neq : (x == 64) = false := by
          cases h_eq : (x == 64) with
          | false => rfl
          | true =>
            rw [beq_iff_eq] at h_eq
            contradiction
        dsimp [check_orbit] at h
        rw [h_neq] at h
        have ih_spec := ih (my_map x) h d hd_le
        exact ih_spec

lemma iterate_succ_apply {α : Type*} (f : α → α) (n : ℕ) (x : α) : f^[n + 1] x = f^[n] (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, ih]
    rfl

theorem my_map_no_cycle_small (d : ℕ) (hd : d ≤ 1100) (h : my_map^[d] 64 = 64) : d = 0 := by
  by_cases h0 : d = 0
  · exact h0
  · have hd_pos : d > 0 := by omega
    have h_check : check_orbit (my_map 64) 1100 = true := check_orbit_eq_true
    have h_spec := check_orbit_spec (my_map 64) 1100 h_check (d - 1) (by omega)
    have h_rw : my_map^[d - 1] (my_map 64) = my_map^[d] 64 := by
      have h_eq : d = d - 1 + 1 := by omega
      nth_rw 2 [h_eq]
      rw [iterate_succ_apply]
    rw [h_rw, h] at h_spec
    contradiction

theorem my_map_no_cycle : ∀ d, my_map^[d] 64 = 64 → d = 0 := by
  intro d h
  rcases le_or_gt d 1100 with hd1100 | hd1100
  · exact my_map_no_cycle_small d hd1100 h
  · -- d > 1100
    have h_sub : d = (d - 1100) + 1100 := by omega
    rw [h_sub] at h
    rw [Function.iterate_add] at h
    dsimp only [Function.comp_apply] at h
    have h_large := iterate_large (d - 1100) (my_map^[1100] 64) iterate_1100_large
    rw [h] at h_large
    have h_false : False := by
      unfold B at *
      revert h_large
      omega
    exact h_false.elim
#print axioms my_map_no_cycle
