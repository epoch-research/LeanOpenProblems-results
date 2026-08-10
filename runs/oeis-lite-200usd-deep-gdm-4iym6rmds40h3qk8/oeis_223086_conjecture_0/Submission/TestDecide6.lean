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

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

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
lemma mem_S_of_lt (k : ℕ) (i : ℕ) (hi : i ≤ k) : A006368_map^[i] 64 ∈ S k := by
  unfold S
  rw [List.mem_map]
  use i
  constructor
  · rw [List.mem_range]
    omega
  · rfl

theorem iterate_add' {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    exact ih (f x)
lemma h_iterate_eq_from_96 (k : ℕ) (i : ℕ) (hi : i < k) (h_neq : ∀ j ≤ i, A006368_map^[j] 96 ≠ 64) : (h k)^[i] 96 = A006368_map^[i] 96 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_lt : i < k - 1 := by omega
    have ih_val : (h k)^[i] 96 = A006368_map^[i] 96 := by
      apply ih (by omega)
      intro j hj
      exact h_neq j (by omega)
    rw [Function.iterate_succ', Function.comp_apply, ih_val]
    rw [h_def]
    have h_mem : A006368_map^[i] 96 ∈ S k := by
      have h_eq : A006368_map^[i] 96 = A006368_map^[i + 1] 64 := by
        rw [show 96 = A006368_map 64 by rfl]
        exact (iterate_add' A006368_map i 1 64).symm
      rw [h_eq]
      apply mem_S_of_lt
      omega
    have h_neq2 : A006368_map^[i] 96 ≠ 64 := h_neq i (by omega)
    rw [if_pos ⟨h_mem, h_neq2⟩]
    rw [Function.iterate_succ']
    rfl

lemma h_iterate_eq_backwards (m0 : ℕ) (hm0 : m0 > 2000) (h_cyc : A006368_map^[m0] 64 = 64) (hm0_min : ∀ m, 0 < m → m < m0 → A006368_map^[m] 64 ≠ 64) (r : ℕ) (hr : r < m0 - 1)
  (h_eq_64 : (h m0)^[m0 - 1] 96 = 64) :
  (h m0)^[m0 - 1 - r] 96 = A006368_map^[m0 - r] 64 := by
  induction r with
  | zero =>
    rw [Nat.sub_zero, Nat.sub_zero]
    rw [h_eq_64, h_cyc]
  | succ r ih =>
    have hr_lt : r < m0 - 2 := by omega
    have ih_val := ih (by omega)
    have h_split : m0 - 1 - r = 1 + (m0 - 2 - r) := by omega
    rw [h_split] at ih_val
    rw [iterate_add' (h m0) 1 (m0 - 2 - r) 96] at ih_val
    change h m0 ((h m0)^[m0 - 2 - r] 96) = A006368_map^[m0 - r] 64 at ih_val
    have h_f_eq : A006368_map^[m0 - r] 64 = A006368_map (A006368_map^[m0 - r - 1] 64) := by
      nth_rw 1 [show m0 - r = 1 + (m0 - r - 1) by omega]
      rw [iterate_add' A006368_map 1 (m0 - r - 1) 64]
      rfl
    have h_h_eq : A006368_map (A006368_map^[m0 - r - 1] 64) = h m0 (A006368_map^[m0 - r - 1] 64) := by
      rw [h_def]
      have h_mem : A006368_map^[m0 - r - 1] 64 ∈ S m0 := mem_S_of_lt m0 (m0 - r - 1) (by omega)
      have h_neq : A006368_map^[m0 - r - 1] 64 ≠ 64 := by
        apply hm0_min (m0 - r - 1) (by omega) (by omega)
      rw [if_pos ⟨h_mem, h_neq⟩]
    rw [h_f_eq, h_h_eq] at ih_val
    have h_inj := h_injective m0 _ _ ih_val
    rw [show m0 - 1 - (r + 1) = m0 - 2 - r by omega]
    rw [show m0 - (r + 1) = m0 - r - 1 by omega]
    exact h_inj


lemma h_iterate_eq_backwards_216 (m0 : ℕ) (hm0 : m0 > 2000) (h_cyc : A006368_map^[m0] 64 = 64) (hm0_min : ∀ m, 0 < m → m < m0 → A006368_map^[m] 64 ≠ 64) (s : ℕ) (hs : s < m0 - 3)
  (h_eq_step : (h m0)^[m0 - 3] 216 = 64) :
  (h m0)^[m0 - 3 - s] 216 = A006368_map^[m0 - s] 64 := by
  induction s with
  | zero =>
    rw [Nat.sub_zero, Nat.sub_zero]
    rw [h_eq_step, h_cyc]
  | succ s ih =>
    have hs_lt : s < m0 - 4 := by omega
    have ih_val := ih (by omega)
    have h_split : m0 - 3 - s = 1 + (m0 - 4 - s) := by omega
    rw [h_split] at ih_val
    rw [iterate_add' (h m0) 1 (m0 - 4 - s) 216] at ih_val
    change h m0 ((h m0)^[m0 - 4 - s] 216) = A006368_map^[m0 - s] 64 at ih_val
    have h_f_eq : A006368_map^[m0 - s] 64 = A006368_map (A006368_map^[m0 - s - 1] 64) := by
      nth_rw 1 [show m0 - s = 1 + (m0 - s - 1) by omega]
      rw [iterate_add' A006368_map 1 (m0 - s - 1) 64]
      rfl
    have h_h_eq : A006368_map (A006368_map^[m0 - s - 1] 64) = h m0 (A006368_map^[m0 - s - 1] 64) := by
      rw [h_def]
      have h_mem : A006368_map^[m0 - s - 1] 64 ∈ S m0 := mem_S_of_lt m0 (m0 - s - 1) (by omega)
      have h_neq : A006368_map^[m0 - s - 1] 64 ≠ 64 := by
        apply hm0_min (m0 - s - 1) (by omega) (by omega)
      rw [if_pos ⟨h_mem, h_neq⟩]
    rw [h_f_eq, h_h_eq] at ih_val
    have h_inj := h_injective m0 _ _ ih_val
    rw [show m0 - 3 - (s + 1) = m0 - 4 - s by omega]
    rw [show m0 - (s + 1) = m0 - s - 1 by omega]
    exact h_inj


theorem A006368_map_no_cycle : ∀ d, A006368_map^[d] 64 = 64 → d = 0 := by
  intro d h_cycle
  by_contra hd0
  have h_exists : ∃ m, m > 0 ∧ A006368_map^[m] 64 = 64 := ⟨d, by omega, h_cycle⟩
  let m0 := Nat.find h_exists
  have hm0 : m0 > 0 ∧ A006368_map^[m0] 64 = 64 := Nat.find_spec h_exists
  have hm0_min : ∀ m, 0 < m → m < m0 → A006368_map^[m] 64 ≠ 64 := by
    intro m hm_pos hm_lt h_cyc
    have h_p : m > 0 ∧ A006368_map^[m] 64 = 64 := ⟨hm_pos, h_cyc⟩
    exact Nat.find_min h_exists hm_lt h_p

  have hm0_gt : m0 > 2000 := by
    by_contra h_le
    push_neg at h_le
    have h_m0_eq : m0 = 0 := A006368_map_no_cycle_small m0 h_le hm0.2
    omega

  have hm0_min_96 (j : ℕ) (hj : j ≤ m0 - 3) : A006368_map^[j] 96 ≠ 64 := by
    intro h_eq
    have h_eq2 : A006368_map^[j + 1] 64 = 64 := by
      rw [iterate_add' A006368_map j 1 64]
      rw [show A006368_map^[1] 64 = 96 by rfl]
      exact h_eq
    have hj_pos : j + 1 > 0 := by omega
    have hj_lt : j + 1 < m0 := by omega
    exact hm0_min (j + 1) hj_pos hj_lt h_eq2

  have h_eq_step : (h m0)^[m0 - 3] 96 = A006368_map^[m0 - 3] 96 := by
    apply h_iterate_eq_from_96 m0 (m0 - 3) (by omega)
    intro j hj
    exact hm0_min_96 j hj

  have h_eq_step_96 : (h m0)^[m0 - 3] 96 = A006368_map^[m0 - 2] 64 := by
    rw [h_eq_step]
    rw [show m0 - 2 = (m0 - 3) + 1 by omega]
    rw [iterate_add' A006368_map (m0 - 3) 1 64]
    rw [show A006368_map^[1] 64 = 96 by rfl]

  have h_eq_step_64 : (h m0)^[m0 - 2] 96 = A006368_map^[m0 - 1] 64 := by
    rw [show m0 - 2 = 1 + (m0 - 3) by omega]
    rw [iterate_add' (h m0) 1 (m0 - 3) 96]
    rw [h_eq_step_96]
    change h m0 (A006368_map^[m0 - 2] 64) = A006368_map^[m0 - 1] 64
    rw [h_def]
    have h_mem : A006368_map^[m0 - 2] 64 ∈ S m0 := mem_S_of_lt m0 (m0 - 2) (by omega)
    have h_neq : A006368_map^[m0 - 2] 64 ≠ 64 := by
      apply hm0_min (m0 - 2) (by omega) (by omega)
    rw [if_pos ⟨h_mem, h_neq⟩]
    rw [show A006368_map (A006368_map^[m0 - 2] 64) = A006368_map^[m0 - 1] 64 by
      rw [show m0 - 1 = 1 + (m0 - 2) by omega]
      rw [iterate_add' A006368_map 1 (m0 - 2) 64]
      rfl]

  have h_eq_64 : (h m0)^[m0 - 1] 96 = 64 := by
    rw [show m0 - 1 = 1 + (m0 - 2) by omega]
    rw [iterate_add' (h m0) 1 (m0 - 2) 96]
    rw [h_eq_step_64]
    change h m0 (A006368_map^[m0 - 1] 64) = 64
    rw [h_def]
    have h_mem : A006368_map^[m0 - 1] 64 ∈ S m0 := mem_S_of_lt m0 (m0 - 1) (by omega)
    have h_neq : A006368_map^[m0 - 1] 64 ≠ 64 := by
      apply hm0_min (m0 - 1) (by omega) (by omega)
    rw [if_pos ⟨h_mem, h_neq⟩]
    rw [show A006368_map (A006368_map^[m0 - 1] 64) = 64 by
      have h_eq : A006368_map (A006368_map^[m0 - 1] 64) = A006368_map^[m0] 64 := by
        nth_rw 2 [show m0 = 1 + (m0 - 1) by omega]
        rw [iterate_add' A006368_map 1 (m0 - 1) 64]
        rfl
      rw [h_eq, hm0.2]]

  have h_eq_step_216 : (h m0)^[m0 - 3] 216 = 64 := by
    have h_split_96 : (h m0)^[2] 96 = 216 := by
      have h_back := h_iterate_eq_backwards m0 hm0_gt hm0.2 hm0_min (m0 - 3) (by omega) h_eq_64
      rw [show m0 - 1 - (m0 - 3) = 2 by omega] at h_back
      rw [h_back]
      rw [show m0 - (m0 - 3) = 3 by omega]
      rfl
    have h_eq_step_216_val : (h m0)^[m0 - 3] 216 = (h m0)^[m0 - 1] 96 := by
      rw [← h_split_96]
      have h_eq : (h m0)^[m0 - 1] 96 = (h m0)^[(m0 - 3) + 2] 96 := by
        congr 1
        omega
      rw [h_eq]
      rw [iterate_add' (h m0) (m0 - 3) 2 96]
    rw [h_eq_step_216_val]
    exact h_eq_64

  have h_eq_back_216 : (h m0)^[1] 216 = 324 := by
    have h_back := h_iterate_eq_backwards_216 m0 hm0_gt hm0.2 hm0_min (m0 - 4) (by omega) h_eq_step_216
    rw [show m0 - 3 - (m0 - 4) = 1 by omega] at h_back
    rw [show m0 - (m0 - 4) = 4 by omega] at h_back
    rw [show A006368_map^[4] 64 = 324 by rfl] at h_back
    exact h_back

  have h_216_eq : h m0 216 = 324 := h_eq_back_216

  have h_216_eq_f : h m0 216 = 216 := by
    rw [show h m0 216 = (h m0)^[1] 216 by rfl]
    rw [show 1 = (m0 - 2) - (m0 - 3) by omega]
    -- wait, we don't need any complex rewrites!
    -- Since (h m0)^[1] 216 = h m0 216, and (h m0)^[m0-3] 216 = 64.
    -- Wait, can we get h m0 216 = 216?
    -- How?



#print axioms A006368_map_no_cycle