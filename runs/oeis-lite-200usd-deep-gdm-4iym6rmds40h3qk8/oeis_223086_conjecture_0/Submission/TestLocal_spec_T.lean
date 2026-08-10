import FormalConjectures.Util.ProblemImports


set_option maxRecDepth 10000000

open Nat

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


lemma my_ineq : A006368_map^[1011] 64 ≥ T 89 := by decide


def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

#eval g^[89] 64

def find_drop : ℕ → ℕ → Option ℕ
  | 0, _ => Option.none
  | n + 1, y =>
    let next := g y
    if next < 11575 then
      Option.some (n + 1)
    else
      find_drop n next

#eval find_drop 1000 (g^[65] 64)


def find_drop_65 : ℕ → ℕ → Option ℕ
  | 0, _ => Option.none
  | n + 1, y =>
    let next := g y
    if next < 65 then
      Option.some (n + 1)
    else
      find_drop_65 n next

#eval find_drop_65 10000 (g 64)


def find_K : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, val =>
    if val ≥ T (n + 1) then
      n + 1
    else
      find_K n val

#eval find_K 500 (A006368_map^[1100] 64)

