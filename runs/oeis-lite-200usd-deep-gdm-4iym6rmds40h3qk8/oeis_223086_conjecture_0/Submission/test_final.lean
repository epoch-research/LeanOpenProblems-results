import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

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

lemma h_f_g_iterate (n : ℕ) (x : ℕ) : A006368_map^[n] (g^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    rw [f_g_eq]
    exact ih x

lemma h_g_f_iterate (n : ℕ) (x : ℕ) : g^[n] (A006368_map^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    rw [Function.iterate_succ', Function.comp_apply]
    rw [g_f_eq]
    exact ih x

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

lemma h_iterate_neq_64 (k : ℕ) (n : ℕ) (x : ℕ) (hx : x ≥ C k) : (h k)^[n] x ≠ 64 := by
  have h_ge := h_iterate_ge_C k n x hx
  have h_64_lt_C : 64 < C k := lt_C k 64 (mem_S_of_lt k 0 (by omega))
  omega

lemma iterate_succ_apply' {α : Type*} (f : α → α) (n : ℕ) (x : α) : f (f^[n] x) = f^[n + 1] x := by
  rw [Function.iterate_succ']
  rfl

lemma h_iterate_eq (k : ℕ) (i : ℕ) (hi : i ≤ k) (h_neq : ∀ j < i, A006368_map^[j] 64 ≠ A006368_map^[k] 64) : (h k)^[i] 64 = A006368_map^[i] 64 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi_lt : i < k := by omega
    have ih_val : (h k)^[i] 64 = A006368_map^[i] 64 := by
      apply ih (by omega)
      intro j hj
      exact h_neq j (by omega)
    rw [Function.iterate_succ' (h k) i, Function.comp_apply, ih_val]
    rw [h_def]
    have h_mem : A006368_map^[i] 64 ∈ S k := mem_S_of_lt k i (by omega)
    have h_neq2 : A006368_map^[i] 64 ≠ A006368_map^[k] 64 := h_neq i (by omega)
    rw [if_pos ⟨h_mem, h_neq2⟩]
    rw [iterate_succ_apply' A006368_map i 64]

lemma h_g_eq (m0 : ℕ) (hm0 : m0 > 1100) (h_cyc : A006368_map^[m0] 64 = 64) (k : ℕ) (hk : k = m0 - 1001) (j : ℕ) (hj_pos : 0 < j) (hj_le : j ≤ 1001) (h_neq : g^[j] 64 ≠ A006368_map^[k] 64) :
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

lemma h_g_iterate_extra (m0 : ℕ) (hm0 : m0 > 1100) (h_cyc : A006368_map^[m0] 64 = 64) (k : ℕ) (hk : k = m0 - 1001) (j : ℕ) (hj_le : j ≤ 999) (h_neq_all : ∀ s, 0 < s → s ≤ 1000 → g^[s] 64 ≠ A006368_map^[k] 64) :
  (h k)^[j] (g^[j + 1] 64) = g^[1] 64 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj_le' : j ≤ 999 := by omega
    have ih_val := ih hj_le'
    rw [iterate_succ_apply]
    have h_step : h k (g^[j + 2] 64) = g^[j + 1] 64 := by
      apply h_g_eq m0 hm0 h_cyc k hk (j + 2) (by omega) (by omega)
      exact h_neq_all (j + 2) (by omega) (by omega)
    rw [show j + 1 + 1 = j + 2 by omega] at h_step
    rw [h_step]
    exact ih_val

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

theorem check_orbit_eq_true : check_orbit (A006368_map 64) 1100 = true := by decide

theorem A006368_map_no_cycle_small (d : ℕ) (hd : d ≤ 1100) (h_cyc : A006368_map^[d] 64 = 64) : d = 0 := by
  by_cases h0 : d = 0
  · exact h0
  · have hd_pos : d > 0 := by omega
    have h_spec := check_orbit_spec (A006368_map 64) 1100 check_orbit_eq_true (d - 1) (by omega)
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

  have hm0_gt : m0 > 1100 := by
    by_contra h_le
    have h_le2 : m0 ≤ 1100 := by omega
    have h_m0_eq : m0 = 0 := A006368_map_no_cycle_small m0 h_le2 hm0.2
    omega

  let k := m0 - 1001
  have hk : k = m0 - 1001 := rfl

  have h_neq_f_i_f_k (i : ℕ) (hi : i < k) : A006368_map^[i] 64 ≠ A006368_map^[k] 64 := by
    intro h_eq
    have h_eq2 : A006368_map^[i] (A006368_map^[k - i] 64) = A006368_map^[i] 64 := by
      rw [← iterate_add_apply A006368_map i (k - i) 64, show i + (k - i) = k by omega, h_eq]
    have h_inj := iterate_injective A006368_map A006368_map_injective i
    have h_eq3 := h_inj _ _ h_eq2
    have h_pos : k - i > 0 := by omega
    have h_lt : k - i < m0 := by omega
    exact hm0_min (k - i) h_pos h_lt h_eq3

  have h_neq_g_j_f_k (j : ℕ) (hj_pos : 0 < j) (hj : j ≤ 1000) : g^[j] 64 ≠ A006368_map^[k] 64 := by
    intro h_eq
    have h_eq2 : A006368_map^[j] (g^[j] 64) = A006368_map^[j] (A006368_map^[k] 64) := by rw [h_eq]
    rw [h_f_g_iterate] at h_eq2
    rw [← iterate_add_apply A006368_map j k 64] at h_eq2
    have h_pos : j + k > 0 := by omega
    have h_lt : j + k < m0 := by
      have : k = m0 - 1001 := rfl
      omega
    exact hm0_min (j + k) h_pos h_lt h_eq2.symm

  have h_fk_eq_g1001 : A006368_map^[k] 64 = g^[1001] 64 := by
    have h_m0 : A006368_map^[1001] (A006368_map^[k] 64) = 64 := by
      rw [← iterate_add_apply A006368_map 1001 k 64, show 1001 + k = m0 by omega]
      exact hm0.2
    have h_m0_g : g^[1001] 64 = g^[1001] (A006368_map^[1001] (A006368_map^[k] 64)) := by rw [h_m0]
    rw [h_g_f_iterate] at h_m0_g
    exact h_m0_g.symm

  have h_iterate_eq_k : (h k)^[k] 64 = A006368_map^[k] 64 := by
    apply h_iterate_eq k k (by omega)
    intro j hj
    exact h_neq_f_i_f_k j hj

  have h_g_iterate_999 : (h k)^[999] (g^[1000] 64) = g^[1] 64 := by
    apply h_g_iterate_extra m0 hm0_gt hm0.2 k hk 999 (by omega)
    intro s hs_pos hs_le
    exact h_neq_g_j_f_k s hs_pos hs_le

  have h_g_iterate_1000 : (h k)^[1000] (g^[1001] 64) = g^[1] 64 := by
    rw [show 1000 = 1 + 999 by omega, iterate_add_apply (h k) 1 999 (g^[1001] 64)]
    rw [h_g_iterate_999]
    change h k (g^[2] 64) = g^[1] 64
    rw [h_def]
    have h_mem : g^[2] 64 ∈ S k := by
      have h_eq : g^[2] 64 = A006368_map^[k + 999] 64 := by
        have h_lhs : A006368_map^[2] (g^[2] 64) = 64 := by rw [h_f_g_iterate]
        have h_rhs : A006368_map^[2] (A006368_map^[k + 999] 64) = 64 := by
          rw [← iterate_add_apply A006368_map 2 (k + 999) 64]
          have h_sum : 2 + (k + 999) = m0 := by
            have : k = m0 - 1001 := rfl
            omega
          rw [h_sum]
          exact hm0.2
        have h_eq_img : A006368_map^[2] (g^[2] 64) = A006368_map^[2] (A006368_map^[k + 999] 64) := by rw [h_lhs, h_rhs]
        exact iterate_injective A006368_map A006368_map_injective 2 _ _ h_eq_img
      rw [h_eq]
      apply mem_S_of_lt
      have : k = m0 - 1001 := rfl
      omega
    have h_neq : g^[2] 64 ≠ A006368_map^[k] 64 := h_neq_g_j_f_k 2 (by omega) (by omega)
    rw [if_pos ⟨h_mem, h_neq⟩]
    rw [show g^[2] 64 = g (g^[1] 64) by rfl, f_g_eq]

  have h_eq_final : (h k)^[k + 1001] 64 = 64 := by
    rw [show k + 1001 = 1001 + k by omega, iterate_add_apply (h k) 1001 k 64]
    rw [h_iterate_eq_k, h_fk_eq_g1001]
    rw [show 1001 = 1 + 1000 by omega, iterate_add_apply (h k) 1 1000 (g^[1001] 64)]
    rw [h_g_iterate_1000]
    change h k (g^[1] 64) = 64
    rw [h_def]
    have h_mem : g^[1] 64 ∈ S k := by
      have h_eq : g^[1] 64 = A006368_map^[k + 1000] 64 := by
        have h_lhs : A006368_map^[1] (g^[1] 64) = 64 := by rw [h_f_g_iterate]
        have h_rhs : A006368_map^[1] (A006368_map^[k + 1000] 64) = 64 := by
          rw [← iterate_add_apply A006368_map 1 (k + 1000) 64]
          have h_sum : 1 + (k + 1000) = m0 := by
            have : k = m0 - 1001 := rfl
            omega
          rw [h_sum]
          exact hm0.2
        have h_eq_img : A006368_map^[1] (g^[1] 64) = A006368_map^[1] (A006368_map^[k + 1000] 64) := by rw [h_lhs, h_rhs]
        exact iterate_injective A006368_map A006368_map_injective 1 _ _ h_eq_img
      rw [h_eq]
      apply mem_S_of_lt
      have : k = m0 - 1001 := rfl
      omega
    have h_neq : g^[1] 64 ≠ A006368_map^[k] 64 := h_neq_g_j_f_k 1 (by omega) (by omega)
    rw [if_pos ⟨h_mem, h_neq⟩]
    rw [show g^[1] 64 = g 64 by rfl, f_g_eq]

  have h_m0_eq : k + 1001 = m0 := by omega
  rw [h_m0_eq] at h_eq_final

  have h_m0_neq : (h k)^[m0] 64 ≠ 64 := by
    rw [show m0 = 1000 + (k + 1) by omega, iterate_add_apply (h k) 1000 (k + 1) 64]
    have h_step : (h k)^[k + 1] 64 = C k + A006368_map^[k] 64 := by
      rw [show k + 1 = 1 + k by omega, iterate_add_apply (h k) 1 k 64]
      rw [h_iterate_eq_k]
      change h k (A006368_map^[k] 64) = C k + A006368_map^[k] 64
      rw [h_def]
      have h_cond : ¬ (A006368_map^[k] 64 ∈ S k ∧ A006368_map^[k] 64 ≠ A006368_map^[k] 64) := by
        intro h_and
        exact h_and.2 rfl
      rw [if_neg h_cond]
    rw [h_step]
    apply h_iterate_neq_64
    exact Nat.le_add_right (C k) (A006368_map^[k] 64)

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
