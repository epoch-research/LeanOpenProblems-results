import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

lemma le_foldr_max (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => contradiction
  | cons a as ih =>
    cases hx with
    | head =>
      dsimp [List.foldr]
      exact le_max_left _ _
    | tail _ h =>
      dsimp [List.foldr]
      have ih_val := ih h
      exact le_trans ih_val (le_max_right _ _)

def B (d : ℕ) : ℕ :=
  100000000000000000000000000000000000 + ((List.range (d + 1)).map (fun i => A006368_map^[i] 64)).foldr max 0

lemma B_ge_base (d : ℕ) : B d ≥ 100000000000000000000000000000000000 := by
  unfold B
  omega

lemma A_le_B (d : ℕ) (j : ℕ) (hj : j ≤ d) : A006368_map^[j] 64 ≤ B d := by
  unfold B
  have h1 : A006368_map^[j] 64 ∈ (List.range (d + 1)).map (fun i => A006368_map^[i] 64) := by
    rw [List.mem_map]
    use j
    constructor
    · rw [List.mem_range]
      omega
    · rfl
  have h2 := le_foldr_max _ _ h1
  omega

def my_map (d : ℕ) (k : ℕ) : ℕ :=
  if k ≤ B d then
    A006368_map k
  else
    B d + k

lemma my_map_injective (d : ℕ) : ∀ x y, my_map d x = my_map d y → x = y := by
  intro x y h
  unfold my_map A006368_map at h
  split_ifs at h <;> omega

lemma iterate_large (d : ℕ) (k : ℕ) (x : ℕ) (hx : x > B d) : (my_map d)^[k] x > B d := by
  induction k generalizing x with
  | zero =>
    exact hx
  | succ k ih =>
    have h_next : my_map d x > B d := by
      unfold my_map A006368_map
      split_ifs <;> omega
    exact ih (my_map d x) h_next

lemma my_map_eq_A (d : ℕ) (j : ℕ) (hj : j ≤ d) : (my_map d)^[j] 64 = A006368_map^[j] 64 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj_le : j ≤ d := by omega
    have ih_val := ih (by omega)
    rw [Function.iterate_succ' (my_map d) j, Function.comp_apply, ih_val]
    unfold my_map
    have h_le := A_le_B d j hj_le
    rw [if_pos h_le]
    rw [Function.iterate_succ' A006368_map j]
    rfl




