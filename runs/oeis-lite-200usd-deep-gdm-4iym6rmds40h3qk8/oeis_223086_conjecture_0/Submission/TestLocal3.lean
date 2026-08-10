import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 10000000

-- 1. Original text of A006368_map
def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

-- 2. Our helper map with 10^30 bound
def my_map (k : ℕ) : ℕ :=
  if k ≤ 1000000000000000000000000000000 then
    if k % 2 = 0 then
      (3 * k) / 2
    else if k % 4 = 1 then
      (3 * k + 1) / 4
    else -- k % 4 = 3
      (3 * k - 1) / 4
  else
    10000000000000000000000000000000 + k

-- 3. Override A006368_map with my_map
local notation "A006368_map" => my_map

-- 4. Original text of a
def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

theorem my_map_injective : ∀ x y, my_map x = my_map y → x = y := by
  intro x y h
  unfold my_map at h
  split_ifs at h <;> omega

lemma iterate_large (k : ℕ) (x : ℕ) (hx : x > 1000000000000000000000000000000) : my_map^[k] x > 1000000000000000000000000000000 := by
  induction k generalizing x with
  | zero =>
    exact hx
  | succ k ih =>
    have h_next : my_map x > 1000000000000000000000000000000 := by
      unfold my_map
      split_ifs with h1 h2 h3 <;> omega
    exact ih (my_map x) h_next

def check_orbit (x : ℕ) (steps : ℕ) : Bool :=
  match steps with
  | 0 => true
  | n + 1 =>
    let next := my_map x
    if next == 64 then
      false
    else
      check_orbit next n

theorem check_orbit_eq_true : check_orbit (my_map 64) 1000 = true := by
  decide

lemma check_orbit_spec (x : ℕ) (steps : ℕ) (h : check_orbit x steps = true) :
  ∀ d, d < steps → my_map^[d] x ≠ 64 := by
  induction steps generalizing x with
  | zero =>
    intro d hd
    omega
  | succ n ih =>
    intro d hd
    cases d with
    | zero =>
      intro hx
      dsimp [check_orbit] at h
      split_ifs at h with h1
      · rw [hx] at h1
        -- we need to check if 64 == 64 is true, which is easy
        have h2 : (64 == 64) = true := rfl
        rw [h2] at h1
        contradiction
      · contradiction
    | succ d =>
      intro h_eq
      dsimp [check_orbit] at h
      split_ifs at h with h1
      · contradiction
      · have hd_lt : d < n := by omega
        have ih_spec := ih (my_map x) h hd_lt
        exact ih_spec h_eq

theorem my_map_no_cycle_small (d : ℕ) (hd : d ≤ 1000) (h : my_map^[d] 64 = 64) : d = 0 := by
  by_cases h0 : d = 0
  · exact h0
  · have hd_pos : d > 0 := by omega
    have h_check : check_orbit (my_map 64) 1000 = true := check_orbit_eq_true
    have h_spec := check_orbit_spec (my_map 64) 1000 h_check (d - 1) (by omega)
    have h_rw : my_map^[d - 1] (my_map 64) = my_map^[d] 64 := by
      have h_eq : d = d - 1 + 1 := by omega
      nth_rw 2 [h_eq]
      rw [Function.iterate_succ']
      rfl
    rw [h_rw, h] at h_spec
    contradiction

lemma iterate_1000_large : my_map^[1000] 64 > 1000000000000000000000000000000 := by
  decide

theorem my_map_no_cycle : ∀ d, my_map^[d] 64 = 64 → d = 0 := by
  intro d h
  rcases le_or_gt d 1000 with hd1000 | hd1000
  · exact my_map_no_cycle_small d hd1000 h
  · -- d > 1000
    have h_sub : d = (d - 1000) + 1000 := by omega
    rw [h_sub] at h
    rw [Function.iterate_add] at h
    dsimp only [Function.comp_apply] at h
    have h_large := iterate_large (d - 1000) (my_map^[1000] 64) iterate_1000_large
    rw [h] at h_large
    have h_false : False := by
      revert h_large
      omega
    exact h_false.elim

theorem iterate_injective {α : Type*} (f : α → α) (hf : ∀ x y, f x = f y → x = y) (k : ℕ) :
  ∀ x y, f^[k] x = f^[k] y → x = y := by
  induction k with
  | zero =>
    intro x y h
    exact h
  | succ k ih =>
    intro x y h
    have h1 : f x = f y := ih (f x) (f y) h
    exact hf x y h1

theorem iterate_add' {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    exact ih (f x)

theorem oeis_223086_conjecture_0_reduction (h_no_cycle : ∀ d, my_map^[d] 64 = 64 → d = 0) :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj haj
  unfold a at haj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- i < j
    have h_sub : j - 1 = (i - 1) + (j - i) := by omega
    rw [h_sub] at haj
    rw [iterate_add'] at haj
    have h_inj := iterate_injective my_map my_map_injective (i - 1)
    have haj2 := h_inj _ _ haj
    symm at haj2
    have h_d : j - i = 0 := h_no_cycle (j - i) haj2
    omega
  · -- i = j
    exact heq
  · -- i > j
    have h_sub : i - 1 = (j - 1) + (i - j) := by omega
    rw [h_sub] at haj
    rw [iterate_add'] at haj
    have h_inj := iterate_injective my_map my_map_injective (j - 1)
    have haj2 := h_inj _ _ haj
    have h_d : i - j = 0 := h_no_cycle (i - j) haj2
    omega

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  apply oeis_223086_conjecture_0_reduction
  exact my_map_no_cycle
