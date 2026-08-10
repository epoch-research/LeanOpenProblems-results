import FormalConjectures.Util.ProblemImports

open Nat

def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

def S (y : ℕ) : Prop :=
  y ≥ 17363 ∨ (y ≥ 11575 ∧ g y ≥ 17363)

lemma g_ge_11575_of_ge_17363 (y : ℕ) (hy : y ≥ 17363) : g y ≥ 11575 := by
  unfold g
  split_ifs with h1 h2 <;> omega

lemma g_g_0 (q : ℕ) : g (g (9 * q)) = 4 * q := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_1 (q : ℕ) : g (g (9 * q + 1)) = 16 * q + 1 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_2 (q : ℕ) : g (g (9 * q + 2)) = 8 * q + 2 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_3 (q : ℕ) : g (g (9 * q + 3)) = 8 * q + 3 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_4 (q : ℕ) : g (g (9 * q + 4)) = 16 * q + 7 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_5 (q : ℕ) : g (g (9 * q + 5)) = 16 * q + 9 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_6 (q : ℕ) : g (g (9 * q + 6)) = 8 * q + 5 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_7 (q : ℕ) : g (g (9 * q + 7)) = 8 * q + 6 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma g_g_8 (q : ℕ) : g (g (9 * q + 8)) = 16 * q + 15 := by
  unfold g
  split_ifs with h1 h2 h3 h4 <;> omega

lemma invariant_step (y : ℕ) (hy : S y) : S (g y) := by
  unfold S at *
  rcases hy with h1 | ⟨h2, h3⟩
  · -- Case 1: y ≥ 17363
    by_cases hg : g y ≥ 17363
    · left; exact hg
    · right
      constructor
      · exact g_ge_11575_of_ge_17363 y h1
      · -- We need g (g y) ≥ 17363
        have h_mod : y % 9 = 0 ∨ y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 3 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 6 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
        rcases h_mod with h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod | h_mod
        · have h_eq : y = 9 * (y / 9) + 0 := by omega
          rw [h_eq]
          rw [g_g_0 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 1 := by omega
          rw [h_eq]
          rw [g_g_1 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 2 := by omega
          rw [h_eq]
          rw [g_g_2 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 3 := by omega
          rw [h_eq]
          rw [g_g_3 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 4 := by omega
          rw [h_eq]
          rw [g_g_4 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 5 := by omega
          rw [h_eq]
          rw [g_g_5 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 6 := by omega
          rw [h_eq]
          rw [g_g_6 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 7 := by omega
          rw [h_eq]
          rw [g_g_7 (y / 9)]
          omega
        · have h_eq : y = 9 * (y / 9) + 8 := by omega
          rw [h_eq]
          rw [g_g_8 (y / 9)]
          omega
  · -- Case 2: y ≥ 11575 ∧ g y ≥ 17363
    left; exact h3


lemma S_iterate (k : ℕ) (y : ℕ) (hy : S y) : S (g^[k] y) := by
  induction k generalizing y with
  | zero =>
    exact hy
  | succ k ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    exact ih (g y) (invariant_step y hy)

lemma S_ge_11575 (y : ℕ) (hy : S y) : y ≥ 11575 := by
  unfold S at hy
  rcases hy with h1 | ⟨h2, h3⟩
  · omega
  · exact h2

lemma S_g_65 : S (g^[65] 64) := by
  decide

lemma g_iterate_ge_11575 (d : ℕ) (hd : d ≥ 65) : g^[d] 64 ≥ 11575 := by
  have h_eq : d = (d - 65) + 65 := by omega
  rw [h_eq, Function.iterate_add]
  dsimp only [Function.comp_apply]
  apply S_ge_11575
  apply S_iterate
  exact S_g_65

lemma g_iterate_neq_64_large (d : ℕ) (hd : d ≥ 65) : g^[d] 64 ≠ 64 := by
  have h_ge := g_iterate_ge_11575 d hd
  omega

def check_orbit_g (x : ℕ) (steps : ℕ) : Bool :=
  if x == 64 then
    false
  else
    match steps with
    | 0 => true
    | n + 1 => check_orbit_g (g x) n

theorem check_orbit_g_eq_true : check_orbit_g (g 64) 64 = true := by
  decide

lemma check_orbit_g_spec (x : ℕ) (steps : ℕ) (h : check_orbit_g x steps = true) :
  ∀ d, d ≤ steps → g^[d] x ≠ 64 := by
  induction steps generalizing x with
  | zero =>
    intro d hd
    have hd_eq : d = 0 := by omega
    subst hd_eq
    dsimp only [Function.iterate_zero, id_eq]
    intro h_eq
    subst h_eq
    dsimp [check_orbit_g] at h
    cases h
  | succ n ih =>
    intro d hd
    by_cases hx : x = 64
    · subst hx
      dsimp [check_orbit_g] at h
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
        dsimp [check_orbit_g] at h
        rw [h_neq] at h
        have ih_spec := ih (g x) h d hd_le
        exact ih_spec

lemma g_iterate_neq_64_small (d : ℕ) (hd : d < 65) (hd_pos : d > 0) : g^[d] 64 ≠ 64 := by
  have h_check : check_orbit_g (g 64) 64 = true := check_orbit_g_eq_true
  have h_spec := check_orbit_g_spec (g 64) 64 h_check (d - 1) (by omega)
  have h_rw : g^[d - 1] (g 64) = g^[d] 64 := by
    have h_eq : d = d - 1 + 1 := by omega
    nth_rw 2 [h_eq]
    rw [← Function.iterate_succ]
  rw [h_rw] at h_spec
  exact h_spec

theorem g_iterate_neq_64 (d : ℕ) (hd : d > 0) : g^[d] 64 ≠ 64 := by
  rcases le_or_gt 65 d with h_ge | h_lt
  · exact g_iterate_neq_64_large d h_ge
  · exact g_iterate_neq_64_small d h_lt hd

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

lemma g_f_eq (x : ℕ) : g (A006368_map x) = x := by
  unfold A006368_map g
  split_ifs with h1 h2 h3 h4 h5 <;> omega

lemma g_f_iterate_eq (d : ℕ) (x : ℕ) : g^[d] (A006368_map^[d] x) = x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    rw [g_f_eq]
    exact ih x

theorem A006368_map_no_cycle : ∀ d, A006368_map^[d] 64 = 64 → d = 0 := by
  intro d h_cycle
  by_contra hd_pos
  have hd_gt : d > 0 := by omega
  have h_g_f := g_f_iterate_eq d 64
  rw [h_cycle] at h_g_f
  have h_neq := g_iterate_neq_64 d hd_gt
  exact h_neq h_g_f
