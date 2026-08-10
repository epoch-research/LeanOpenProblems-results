import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000

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

theorem h_injective (k : ℕ) : ∀ x y, h k x = h k y → x = y := by
  intro x y heq
  simp_rw [h_def] at heq
  by_cases hx : x ∈ S k ∧ x ≠ 64
  · rw [if_pos hx] at heq
    by_cases hy : y ∈ S k ∧ y ≠ 64
    · rw [if_pos hy] at heq
      exact A006368_map_injective _ _ heq
    · rw [if_neg hy] at heq
      have h_lt : A006368_map x < C k := f_lt_C k x hx.1
      omega
  · rw [if_neg hx] at heq
    by_cases hy : y ∈ S k ∧ y ≠ 64
    · rw [if_pos hy] at heq
      have h_lt : A006368_map y < C k := f_lt_C k y hy.1
      omega
    · rw [if_neg hy] at heq
      omega

theorem h_iterate_injective (k : ℕ) (n : ℕ) : ∀ x y, (h k)^[n] x = (h k)^[n] y → x = y := by
  induction n with
  | zero =>
    intro x y heq
    exact heq
  | succ n ih =>
    intro x y heq
    have h1 : h k x = h k y := ih (h k x) (h k y) heq
    exact h_injective k x y h1

lemma mem_S_of_lt (k : ℕ) (i : ℕ) (hi : i ≤ k) : A006368_map^[i] 64 ∈ S k := by
  unfold S
  rw [List.mem_map]
  use i
  constructor
  · rw [List.mem_range]
    omega
  · rfl

lemma h_iterate_eq_of_not_mem (k : ℕ) (i : ℕ) (x : ℕ) (hi : i ≤ k) (h_mem : ∀ j < i, A006368_map^[j] x ∈ S k) (h_neq : ∀ j < i, A006368_map^[j] x ≠ 64) : (h k)^[i] x = A006368_map^[i] x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih_val : (h k)^[i] x = A006368_map^[i] x := by
      apply ih (by omega) (fun j hj => h_mem j (by omega)) (fun j hj => h_neq j (by omega))
    rw [Function.iterate_succ', Function.comp_apply, ih_val]
    rw [h_def]
    have h_cond : A006368_map^[i] x ∈ S k ∧ A006368_map^[i] x ≠ 64 := ⟨h_mem i (by omega), h_neq i (by omega)⟩
    rw [if_pos h_cond]
    rw [Function.iterate_succ']

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
    have h_le2 : m0 ≤ 2000 := by omega
    have h_m0_eq : m0 = 0 := A006368_map_no_cycle_small m0 h_le2 hm0.2
    omega

  have h_eq_64 : (h m0)^[m0 - 1] 96 = 64 := by
    have h_eq_map : (h m0)^[m0 - 1] 96 = A006368_map^[m0 - 1] 96 := by
      apply h_iterate_eq_of_not_mem m0 (m0 - 1) 96 (Nat.sub_le m0 1)
      · intro j hj
        have h_rw : A006368_map^[j] 96 = A006368_map^[j + 1] 64 := by
          rw [show 96 = A006368_map^[1] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply mem_S_of_lt
        omega
      · intro j hj
        have h_rw : A006368_map^[j] 96 = A006368_map^[j + 1] 64 := by
          rw [show 96 = A006368_map^[1] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply hm0_min (j + 1) (by omega) (by omega)
    rw [h_eq_map]
    have h_rw2 : A006368_map^[m0 - 1] 96 = A006368_map^[m0] 64 := by
      rw [show 96 = A006368_map^[1] 64 by rfl]
      rw [← iterate_add_apply]
      congr 1
      omega
    rw [h_rw2, hm0.2]

  have h_eq_step_216 : (h m0)^[m0 - 3] 216 = 64 := by
    have h_eq_map : (h m0)^[m0 - 3] 216 = A006368_map^[m0 - 3] 216 := by
      apply h_iterate_eq_of_not_mem m0 (m0 - 3) 216 (Nat.sub_le m0 3)
      · intro j hj
        have h_rw : A006368_map^[j] 216 = A006368_map^[j + 3] 64 := by
          rw [show 216 = A006368_map^[3] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply mem_S_of_lt
        omega
      · intro j hj
        have h_rw : A006368_map^[j] 216 = A006368_map^[j + 3] 64 := by
          rw [show 216 = A006368_map^[3] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply hm0_min (j + 3) (by omega) (by omega)
    rw [h_eq_map]
    have h_rw2 : A006368_map^[m0 - 3] 216 = A006368_map^[m0] 64 := by
      rw [show 216 = A006368_map^[3] 64 by rfl]
      rw [← iterate_add_apply]
      congr 1
      omega
    rw [h_rw2, hm0.2]

  have h_eq_324_64 : (h m0)^[m0 - 4] 324 = 64 := by
    have h_eq_map : (h m0)^[m0 - 4] 324 = A006368_map^[m0 - 4] 324 := by
      apply h_iterate_eq_of_not_mem m0 (m0 - 4) 324 (Nat.sub_le m0 4)
      · intro j hj
        have h_rw : A006368_map^[j] 324 = A006368_map^[j + 4] 64 := by
          rw [show 324 = A006368_map^[4] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply mem_S_of_lt
        omega
      · intro j hj
        have h_rw : A006368_map^[j] 324 = A006368_map^[j + 4] 64 := by
          rw [show 324 = A006368_map^[4] 64 by rfl]
          rw [← iterate_add_apply]
        rw [h_rw]
        apply hm0_min (j + 4) (by omega) (by omega)
    rw [h_eq_map]
    have h_rw2 : A006368_map^[m0 - 4] 324 = A006368_map^[m0] 64 := by
      rw [show 324 = A006368_map^[4] 64 by rfl]
      rw [← iterate_add_apply]
      congr 1
      omega
    rw [h_rw2, hm0.2]

  have h_eq_216_step : (h m0)^[m0 - 3] 216 = (h m0)^[m0 - 4] (h m0 216) := by
    rw [show m0 - 3 = (m0 - 4) + 1 by omega, Function.iterate_succ]
    rfl

  have h_contra : 324 = 216 := by
    have h_inj := h_iterate_injective m0 (m0 - 4) (h m0 216) 324
    have h_eq_final : (h m0)^[m0 - 4] (h m0 216) = (h m0)^[m0 - 4] 324 := by
      rw [← h_eq_216_step]
      rw [h_eq_step_216, h_eq_324_64]
    have h_eq_h216_324 := h_inj h_eq_final
    have h_216 : h m0 216 = 324 := by
      rw [h_def]
      have h_cond : 216 ∈ S m0 ∧ 216 ≠ 64 := by
        constructor
        · have h_eq : 216 = A006368_map^[3] 64 := rfl
          rw [h_eq]
          apply mem_S_of_lt; omega
        · decide
      rw [if_pos h_cond]
      rfl
    -- wait, we want a contradiction, so we need to prove h m0 216 is NOT 324 or something?
    -- No!
    -- Wait, if h m0 216 = 324, and h_inj says h m0 216 = 324, then we don't get a contradiction!
    -- Ah!
    -- Let's change the injection elements to get a contradiction!
    sorry

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
