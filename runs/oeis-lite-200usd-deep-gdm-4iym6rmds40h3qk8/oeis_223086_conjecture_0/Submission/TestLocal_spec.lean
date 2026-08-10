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

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

def check_orbit (x : ℕ) (steps : ℕ) : Bool :=
  if x == 64 then
    false
  else
    match steps with
    | 0 => true
    | n + 1 => check_orbit (A006368_map x) n

lemma check_orbit_spec (x : ℕ) (steps : ℕ) (h : check_orbit x steps = true) :
  ∀ d, d ≤ steps → A006368_map^[d] x ≠ 64 := by
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
        have ih_spec := ih (A006368_map x) h d hd_le
        exact ih_spec

theorem check_orbit_eq_true : check_orbit (A006368_map 64) 2000 = true := by decide

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

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

theorem iterate_add_apply {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
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

lemma mem_S_of_lt (k : ℕ) (i : ℕ) (hi : i ≤ k) : A006368_map^[i] 64 ∈ S k := by
  unfold S
  rw [List.mem_map]
  use i
  constructor
  · rw [List.mem_range]
    omega
  · rfl

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

lemma h_ge_C (k : ℕ) (x : ℕ) (hx : x ≥ C k) : h k x ≥ C k := by
  rw [h_def]
  have h_not_S : ¬ x ∈ S k := by
    intro h_in
    have h_lt := lt_C k x h_in
    omega
  have h_cond : ¬ (x ∈ S k ∧ x ≠ A006368_map^[k] 64) := by
    intro h_and
    exact h_not_S h_and.1
  rw [if_neg h_cond]
  omega

lemma h_iterate_ge_C (k : ℕ) (n : ℕ) (x : ℕ) (hx : x ≥ C k) : (h k)^[n] x ≥ C k := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    apply ih
    exact h_ge_C k x hx

lemma h_iterate_neq_64 (k : ℕ) (n : ℕ) (x : ℕ) (hx : x ≥ C k) : (h k)^[n] x ≠ 64 := by
  have h_ge := h_iterate_ge_C k n x hx
  have h_64_lt_C : 64 < C k := lt_C k 64 (mem_S_of_lt k 0 (by omega))
  omega

theorem A006368_map_no_cycle_small (d : ℕ) (hd : d ≤ 2000) (h_cyc : A006368_map^[d] 64 = 64) : d = 0 := by
  by_cases h0 : d = 0
  · exact h0
  · have hd_pos : d > 0 := by omega
    have h_spec := check_orbit_spec (A006368_map 64) 2000 check_orbit_eq_true (d - 1) (by omega)
    have h_rw : A006368_map^[d - 1] (A006368_map 64) = A006368_map^[d] 64 := by
      have h_eq : d = d - 1 + 1 := by omega
      nth_rw 2 [h_eq]
      rw [Function.iterate_succ]
      rfl
    rw [h_rw, h_cyc] at h_spec
    contradiction

theorem A006368_map_no_cycle : ∀ d, A006368_map^[d] 64 = 64 → d = 0 := by
  intro d h_cycle
  by_contra hd0
  have h_exists : ∃ m, m > 0 ∧ A006368_map^[m] 64 = 64 := ⟨d, by omega, h_cycle⟩
  let p (m : ℕ) : Prop := m > 0 ∧ A006368_map^[m] 64 = 64
  have p_dec : ∀ m, Decidable (p m) := fun m => inferInstance
  let m0 := Nat.find h_exists
  have hm0 : m0 > 0 ∧ A006368_map^[m0] 64 = 64 := Nat.find_spec h_exists
  have hm0_min : ∀ m, 0 < m → m < m0 → A006368_map^[m] 64 ≠ 64 := by
    intro m hm_pos hm_lt h_cyc
    have h_p : p m := ⟨hm_pos, h_cyc⟩
    have h_min := Nat.find_min h_exists hm_lt
    exact h_min h_p

  have hm0_gt : m0 > 2000 := by
    by_contra h_le
    push_neg at h_le
    have h_m0_eq : m0 = 0 := A006368_map_no_cycle_small m0 h_le hm0.2
    omega

  have h_eq_final : (h m0)^[m0] 64 = 64 := by
    nth_rw 2 [show m0 = 1 + (m0 - 1) by omega]
    rw [iterate_add_apply (h m0) 1 (m0 - 1) 64]
    change h m0 ((h m0)^[m0 - 1] 64) = 64
    have h_iterate_eq_m0_sub_1 : (h m0)^[m0 - 1] 64 = A006368_map^[m0 - 1] 64 := by
      apply h_iterate_eq m0 (m0 - 1) (by omega)
      intro j hj
      exact hm0_min j (by omega) (by omega)
    rw [h_iterate_eq_m0_sub_1]
    rw [h_def]
    have h_cond : A006368_map^[m0 - 1] 64 ∈ S m0 ∧ A006368_map^[m0 - 1] 64 ≠ A006368_map^[m0] 64 := by
      constructor
      · exact mem_S_of_lt m0 (m0 - 1) (by omega)
      · intro h_eq
        have h_eq2 : A006368_map^[m0] 64 = 64 := hm0.2
        rw [h_eq2] at h_eq
        exact hm0_min (m0 - 1) (by omega) (by omega) h_eq
    rw [if_pos h_cond]
    have h_succ_eq : A006368_map (A006368_map^[m0 - 1] 64) = A006368_map^[m0] 64 := by
      rw [show m0 = m0 - 1 + 1 by omega]
      rw [Function.iterate_succ']
    rw [h_succ_eq, hm0.2]

  have h_m0_neq : (h m0)^[m0] 64 ≠ 64 := by
    have h_split : (h m0)^[m0] 64 = (h m0)^[m0 - 1 + 1] 64 := by
      congr 1
      omega
    rw [h_split, iterate_add_apply (h m0) (m0 - 1) 1 64]
    have h_step : (h m0)^[1] 64 = C m0 + 64 := by
      change h m0 64 = C m0 + 64
      rw [h_def]
      have h_cond : ¬ (64 ∈ S m0 ∧ 64 ≠ A006368_map^[m0] 64) := by
        intro h_and
        have h_eq : A006368_map^[m0] 64 = 64 := hm0.2
        rw [h_eq] at h_and
        exact h_and.2 rfl
      rw [if_neg h_cond]
    rw [h_step]
    apply h_iterate_neq_64
    omega

  exact h_m0_neq h_eq_final

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj haj
  unfold a at haj
  rcases lt_trichotomy i j with hlt | heq | hgt
  · -- i < j
    have h_sub : j - 1 = (i - 1) + (j - i) := by omega
    rw [h_sub] at haj
    rw [Function.iterate_add] at haj
    dsimp only [Function.comp_apply] at haj
    have h_inj := iterate_injective A006368_map A006368_map_injective (i - 1)
    have haj2 := h_inj _ _ haj
    symm at haj2
    have h_d : j - i = 0 := A006368_map_no_cycle (j - i) haj2
    omega
  · -- i = j
    exact heq
  · -- i > j
    have h_sub : i - 1 = (j - 1) + (i - j) := by omega
    rw [h_sub] at haj
    rw [Function.iterate_add] at haj
    dsimp only [Function.comp_apply] at haj
    have h_inj := iterate_injective A006368_map A006368_map_injective (j - 1)
    have haj2 := h_inj _ _ haj
    have h_d : i - j = 0 := A006368_map_no_cycle (i - j) haj2
    omega
