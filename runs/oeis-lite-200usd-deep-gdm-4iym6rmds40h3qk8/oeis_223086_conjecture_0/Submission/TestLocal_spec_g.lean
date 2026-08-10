import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000000

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4


def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

def check_g_s (steps : ℕ) : Bool :=
  match steps with
  | 0 => true
  | n + 1 =>
    if g^[n + 1] 64 == 11574 then
      false
    else
      check_g_s n

lemma check_g_s_spec (steps : ℕ) (h : check_g_s steps = true) :
  ∀ j, 0 < j → j ≤ steps → g^[j] 64 ≠ 11574 := by
  induction steps with
  | zero =>
    intro j hj_pos hj_le
    omega
  | succ n ih =>
    intro j hj_pos hj_le
    rcases eq_or_lt_of_le hj_le with rfl | hj_lt
    · intro h_eq
      dsimp [check_g_s] at h
      have h2 : (g^[n] (g 64) == 11574) = true := by
        rw [beq_iff_eq]
        exact h_eq
      rw [h2] at h
      cases h
    · have hj_le_n : j ≤ n := by omega
      dsimp [check_g_s] at h
      by_cases h1 : (g^[n] (g 64) == 11574) = true
      · rw [h1] at h
        cases h
      · rw [if_neg h1] at h
        exact ih h j hj_pos hj_le_n

theorem check_g_s_eq_true : check_g_s 79 = true := by decide


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
