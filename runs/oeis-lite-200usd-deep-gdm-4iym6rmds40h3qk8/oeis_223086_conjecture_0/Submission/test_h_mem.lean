import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

lemma iterate_add_apply {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
  rw [Function.iterate_add]; rfl

def S (k : ℕ) : List ℕ :=
  (List.range (k + 1)).map (fun i => A006368_map^[i] 64)

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

def C (k : ℕ) : ℕ :=
  (((S k).map A006368_map) ++ S k).foldr max 0 + 1

lemma lt_C (k : ℕ) (x : ℕ) (hx : x ∈ S k) : x < C k := by
  have h1 : x ∈ (S k).map A006368_map ++ S k := by
    rw [List.mem_append]
    right
    exact hx
  have h2 := le_foldr_max _ _ h1
  unfold C
  omega

lemma f_lt_C (k : ℕ) (x : ℕ) (hx : x ∈ S k) : A006368_map x < C k := by
  have h1 : A006368_map x ∈ (S k).map A006368_map ++ S k := by
    rw [List.mem_append]
    left
    exact List.mem_map_of_mem hx
  have h2 := le_foldr_max _ _ h1
  unfold C
  omega

def h (k : ℕ) (x : ℕ) : ℕ :=
  if x ∈ S k ∧ x ≠ 64 then
    A006368_map x
  else
    C k + x

lemma h_def (k : ℕ) (x : ℕ) : h k x = if x ∈ S k ∧ x ≠ 64 then A006368_map x else C k + x := rfl

lemma iterate_succ_apply' {α : Type*} (f : α → α) (n : ℕ) (x : α) : f (f^[n] x) = f^[n + 1] x := by
  rw [Function.iterate_succ']
  rfl

lemma h_iterate_eq_of_not_mem (k : ℕ) (i : ℕ) (x : ℕ) (hi : i ≤ k) (h_mem : ∀ j < i, A006368_map^[j] x ∈ S k) (h_neq : ∀ j < i, A006368_map^[j] x ≠ 64) : (h k)^[i] x = A006368_map^[i] x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih_val : (h k)^[i] x = A006368_map^[i] x := by
      apply ih (by omega) (fun j hj => h_mem j (by omega)) (fun j hj => h_neq j (by omega))
    rw [Function.iterate_succ' (h k) i, Function.comp_apply, ih_val]
    rw [h_def]
    have h_cond : A006368_map^[i] x ∈ S k ∧ A006368_map^[i] x ≠ 64 := ⟨h_mem i (by omega), h_neq i (by omega)⟩
    rw [if_pos h_cond]
    rw [iterate_succ_apply' A006368_map i x]
