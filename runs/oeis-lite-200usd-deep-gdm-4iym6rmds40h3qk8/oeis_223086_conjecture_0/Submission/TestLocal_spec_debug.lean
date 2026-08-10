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

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

lemma g_injective : ∀ x y, g x = g y → x = y := by
  intro x y h
  have h1 : A006368_map (g x) = A006368_map (g y) := by rw [h]
  rw [f_g_eq, f_g_eq] at h1
  exact h1

lemma iterate_succ_apply {α : Type*} (f : α → α) (n : ℕ) (x : α) : f^[n + 1] x = f^[n] (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, ih]
    rfl

lemma iterate_add_apply {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
  rw [Function.iterate_add]
  rfl

lemma g_iterate_injective (k : ℕ) : ∀ x y, g^[k] x = g^[k] y → x = y := by
  induction k with
  | zero =>
    intro x y h
    exact h
  | succ k ih =>
    intro x y h
    rw [iterate_succ_apply, iterate_succ_apply] at h
    have h1 : g x = g y := ih _ _ h
    exact g_injective _ _ h1

def S (k : ℕ) : List ℕ :=
  (List.range (k + 1002)).map (fun i => A006368_map^[i] 64)

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

lemma mem_S_of_lt (k : ℕ) (i : ℕ) (hi : i ≤ k + 1001) : A006368_map^[i] 64 ∈ S k := by
  unfold S
  rw [List.mem_map]
  use i
  constructor
  · rw [List.mem_range]
    omega
  · rfl

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
  if x ∈ S k ∧ x ≠ A006368_map^[k] 64 then
    A006368_map x
  else
    C k + x

lemma h_def (k : ℕ) (x : ℕ) : h k x = if x ∈ S k ∧ x ≠ A006368_map^[k] 64 then A006368_map x else C k + x := rfl

theorem h_injective (k : ℕ) : ∀ x y, h k x = h k y → x = y := by
  intro x y heq
  simp_rw [h_def] at heq
  by_cases hx : x ∈ S k ∧ x ≠ A006368_map^[k] 64
  · rw [if_pos hx] at heq
    by_cases hy : y ∈ S k ∧ y ≠ A006368_map^[k] 64
    · rw [if_pos hy] at heq
      exact A006368_map_injective _ _ heq
    · rw [if_neg hy] at heq
      have h_lt : A006368_map x < C k := f_lt_C k x hx.1
      omega
  · rw [if_neg hx] at heq
    by_cases hy : y ∈ S k ∧ y ≠ A006368_map^[k] 64
    · rw [if_pos hy] at heq
      have h_lt : A006368_map y < C k := f_lt_C k y hy.1
      omega
    · rw [if_neg hy] at heq
      omega

lemma h_ge_C (k : ℕ) (x : ℕ) (hx : x ≥ C k) : h k x ≥ C k + x := by
  rw [h_def]
  have h_not_S : ¬ x ∈ S k := by
    intro h_in
    have h_lt := lt_C k x h_in
    omega
  have h_cond : ¬ (x ∈ S k ∧ x ≠ A006368_map^[k] 64) := by
    intro h_and
    exact h_not_S h_and.1
  rw [if_neg h_cond]

lemma h_iterate_ge_C (k : ℕ) (n : ℕ) (x : ℕ) (hx : x ≥ C k) : (h k)^[n] x ≥ n * C k + x := by
  induction n generalizing x with
  | zero =>
    dsimp
    omega
  | succ n ih =>
    rw [iterate_succ_apply]
    have h1 : h k x ≥ C k + x := h_ge_C k x hx
    have h2 : h k x ≥ C k := by omega
    have ih_val := ih (h k x) h2
    rw [Nat.succ_mul]
    omega

lemma h_iterate_eq (k : ℕ) (i : ℕ) (hi : i ≤ k) (h_neq : ∀ j < i, A006368_map^[j] 64 ≠ A006368_map^[k] 64) : (h k)^[i] 64 = A006368_map^[i] 64 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_lt : i < k := by omega
    have ih_val : (h k)^[i] 64 = A006368_map^[i] 64 := by
      apply ih (by omega)
      intro j hj
      exact h_neq j (by omega)
    rw [Function.iterate_succ', Function.comp_apply, ih_val]
    rw [h_def]
    have h_mem : A006368_map^[i] 64 ∈ S k := mem_S_of_lt k i (by omega)
    have h_neq2 : A006368_map^[i] 64 ≠ A006368_map^[k] 64 := h_neq i (by omega)
    rw [if_pos ⟨h_mem, h_neq2⟩]
    rw [Function.iterate_succ']
    rfl

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

lemma h_g_eq (m0 : ℕ) (hm0 : m0 > 2000) (h_cyc : A006368_map^[m0] 64 = 64) (k : ℕ) (hk : k = m0 - 1001) (j : ℕ) (hj_pos : 0 < j) (hj_le : j ≤ 1000) (h_neq : g^[j] 64 ≠ A006368_map^[k] 64) :
  h k (g^[j] 64) = g^[j-1] 64 := by
  rw [h_def]
  have h_mem : g^[j] 64 ∈ S k := by
    have h_eq : g^[j] 64 = A006368_map^[k + 1001 - j] 64 := by
      have h_lhs : A006368_map^[j] (g^[j] 64) = 64 := by
        rw [f_iterate_eq_g_iterate]
      have h_rhs : A006368_map^[j] (A006368_map^[k + 1001 - j] 64) = 64 := by
        rw [← iterate_add_apply A006368_map j (k + 1001 - j) 64]
        have h_sum : j + (k + 1001 - j) = m0 := by omega
        rw [h_sum]
        exact h_cyc
      have h_eq_img : A006368_map^[j] (g^[j] 64) = A006368_map^[j] (A006368_map^[k + 1001 - j] 64) := by
        rw [h_lhs, h_rhs]
      exact iterate_injective A006368_map A006368_map_injective j _ _ h_eq_img
    rw [h_eq]
    apply mem_S_of_lt
    omega
  rw [if_pos ⟨h_mem, h_neq⟩]
  have h_eq2 : g^[j] 64 = g (g^[j - 1] 64) := by
    have h_eq3 : j = j - 1 + 1 := by omega
    nth_rw 1 [h_eq3]
    rw [Function.iterate_succ']
    rfl
  rw [h_eq2, f_g_eq]


lemma h_g_iterate (m0 : ℕ) (hm0 : m0 > 2000) (h_cyc : A006368_map^[m0] 64 = 64) (k : ℕ) (hk : k = m0 - 1001) (j : ℕ) (hj_le : j ≤ 1000) (h_neq : ∀ m, 0 < m → m ≤ j → g^[m] 64 ≠ A006368_map^[k] 64) :
  (h k)^[j] (g^[j] 64) = 64 := by
  induction j with
  | zero =>
    rfl
  | succ j ih =>
    have hj_le' : j ≤ 1000 := by omega
    have h_neq' : ∀ m, 0 < m → m ≤ j → g^[m] 64 ≠ A006368_map^[k] 64 := by
      intro m hm_pos hm_le
      exact h_neq m hm_pos (by omega)
    have ih_val := ih hj_le' h_neq'
    rw [iterate_succ_apply]
    have h_step : h k (g^[j + 1] 64) = g^[j] 64 := by
      apply h_g_eq m0 hm0 h_cyc k hk (j + 1) (by omega) hj_le
      exact h_neq (j + 1) (by omega) (by omega)
    rw [h_step]
    exact ih_val
