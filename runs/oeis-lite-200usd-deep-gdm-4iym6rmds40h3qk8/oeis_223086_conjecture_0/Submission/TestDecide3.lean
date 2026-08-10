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

-- Steps of 100 for A006368_map
lemma step1 : A006368_map^[100] 64 = 11574 := by decide
lemma step2 : A006368_map^[100] 11574 = 2089746 := by decide
lemma step3 : A006368_map^[100] 2089746 = 47162797 := by decide
lemma step4 : A006368_map^[100] 47162797 = 139513299931002 := by decide
lemma step5 : A006368_map^[100] 139513299931002 = 100756188284683804 := by decide
lemma step6 : A006368_map^[100] 100756188284683804 = 4657016978965305652129 := by decide
lemma step7 : A006368_map^[100] 4657016978965305652129 = 105102721346651848180727 := by decide
lemma step8 : A006368_map^[100] 105102721346651848180727 = 607239572799050767489311236 := by decide
lemma step9 : A006368_map^[100] 607239572799050767489311236 = 219273520019636635525971950843 := by decide
lemma step10 : A006368_map^[100] 219273520019636635525971950843 = 9897427377833507869287616648508 := by decide

lemma iterate_1000_eq : A006368_map^[1000] 64 = 9897427377833507869287616648508 := by
  have h1 : A006368_map^[100] 64 = 11574 := step1
  have h2 : A006368_map^[200] 64 = 2089746 := by
    rw [show 200 = 100 + 100 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h1, step2]
  have h3 : A006368_map^[300] 64 = 47162797 := by
    rw [show 300 = 100 + 200 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h2, step3]
  have h4 : A006368_map^[400] 64 = 139513299931002 := by
    rw [show 400 = 100 + 300 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h3, step4]
  have h5 : A006368_map^[500] 64 = 100756188284683804 := by
    rw [show 500 = 100 + 400 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h4, step5]
  have h6 : A006368_map^[600] 64 = 4657016978965305652129 := by
    rw [show 600 = 100 + 500 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h5, step6]
  have h7 : A006368_map^[700] 64 = 105102721346651848180727 := by
    rw [show 700 = 100 + 600 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h6, step7]
  have h8 : A006368_map^[800] 64 = 607239572799050767489311236 := by
    rw [show 800 = 100 + 700 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h7, step8]
  have h9 : A006368_map^[900] 64 = 219273520019636635525971950843 := by
    rw [show 900 = 100 + 800 by omega, Function.iterate_add]
    dsimp only [Function.comp_apply]
    rw [h8, step9]
  rw [show 1000 = 100 + 900 by omega, Function.iterate_add]
  dsimp only [Function.comp_apply]
  rw [h9, step10]


theorem check_orbit_eq_true : check_orbit (A006368_map 64) 2000 = true := by decide




def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

theorem f_g (y : ℕ) : A006368_map (g y) = y := by
  unfold A006368_map g
  split_ifs <;> omega

theorem A006368_map_injective : ∀ x y, A006368_map x = A006368_map y → x = y := by
  intro x y h
  unfold A006368_map at h
  split_ifs at h <;> omega

theorem g_f (x : ℕ) : g (A006368_map x) = x := by
  have h1 : A006368_map (g (A006368_map x)) = A006368_map x := f_g (A006368_map x)
  exact A006368_map_injective _ _ h1


lemma h_f_g_iterate (n : ℕ) (x : ℕ) : A006368_map^[n] (g^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ A006368_map n]
    dsimp only [Function.comp_apply]
    rw [Function.iterate_succ' g n]
    dsimp only [Function.comp_apply]
    rw [f_g]
    exact ih x


lemma h_g_f_iterate (n : ℕ) (x : ℕ) : g^[n] (A006368_map^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ A006368_map n]
    dsimp only [Function.comp_apply]
    rw [Function.iterate_succ' g n]
    dsimp only [Function.comp_apply]
    rw [ih (A006368_map x)]
    rw [g_f]

lemma iterate_add_apply {α : Type*} (f : α → α) (n m : ℕ) (x : α) : f^[n + m] x = f^[n] (f^[m] x) := by
  rw [Function.iterate_add]; rfl


def S (k : ℕ) : List ℕ :=
  (List.range (k + 1)).map (fun i => A006368_map^[i] 64) ++
  (List.range (k + 1)).map (fun i => g^[i] 64)

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
  rw [List.mem_append]
  left
  rw [List.mem_map]
  use i
  constructor
  · rw [List.mem_range]
    omega
  · rfl

lemma mem_S_of_lt_g (k : ℕ) (j : ℕ) (hj : j ≤ k) : g^[j] 64 ∈ S k := by
  unfold S
  rw [List.mem_append]
  right
  rw [List.mem_map]
  use j
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

lemma h_g_eq (k : ℕ) (j : ℕ) (hj : 0 < j) (hj_le : j ≤ k) (h_neq : g^[j] 64 ≠ A006368_map^[k] 64) : h k (g^[j] 64) = g^[j-1] 64 := by
  rw [h_def]
  have h_mem : g^[j] 64 ∈ S k := mem_S_of_lt_g k j hj_le
  rw [if_pos ⟨h_mem, h_neq⟩]
  have h_eq : g^[j] 64 = g (g^[j - 1] 64) := by
    have h_sub : j = (j - 1) + 1 := by omega
    nth_rw 1 [h_sub]
    rw [Function.iterate_succ']
    rfl
  rw [h_eq, f_g]

lemma h_g_iterate_offset (k : ℕ) (j : ℕ) (offset : ℕ) (hj_le : j + offset ≤ k) (h_neq : ∀ m, offset < m → m ≤ j + offset → g^[m] 64 ≠ A006368_map^[k] 64) :
  (h k)^[j] (g^[j + offset] 64) = g^[offset] 64 := by
  induction j with
  | zero =>
    rw [show 0 + offset = offset by omega]
    rfl
  | succ j ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have h_g : h k (g^[j + 1 + offset] 64) = g^[j + offset] 64 := by
      have h_step := h_g_eq k (j + 1 + offset) (by omega) (by omega)
      rw [show j + 1 + offset - 1 = j + offset by omega] at h_step
      apply h_step
      exact h_neq (j + 1 + offset) (by omega) (by omega)
    rw [h_g]
    apply ih (by omega)
    intro m hm_pos hm_le
    exact h_neq m hm_pos (by omega)

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

  generalize hk0 : m0 - 1000 = k
  have hk : k > 1000 := by omega

  have h_neq_f_i_f_k (i : ℕ) (hi : i < k) : A006368_map^[i] 64 ≠ A006368_map^[k] 64 := by
    intro h_eq
    have h_eq2 : A006368_map^[i] (A006368_map^[k - i] 64) = A006368_map^[i] 64 := by
      rw [← iterate_add_apply A006368_map i (k - i) 64, show i + (k - i) = k by omega, h_eq]
    have h_inj := iterate_injective A006368_map A006368_map_injective i
    have h_eq3 := h_inj _ _ h_eq2
    have h_pos : k - i > 0 := by omega
    have h_lt : k - i < m0 := by omega
    exact hm0_min (k - i) h_pos h_lt h_eq3

  have h_neq_g_j_f_k (j : ℕ) (hj_pos : 0 < j) (hj : j < 1000) : g^[j] 64 ≠ A006368_map^[k] 64 := by
    intro h_eq
    have h_eq2 : A006368_map^[j] (g^[j] 64) = A006368_map^[j] (A006368_map^[k] 64) := by rw [h_eq]
    rw [h_f_g_iterate] at h_eq2
    rw [← iterate_add_apply A006368_map j k 64] at h_eq2
    have h_pos : j + k > 0 := by omega
    have h_lt : j + k < m0 := by omega
    exact hm0_min (j + k) h_pos h_lt h_eq2.symm

  have h_fk_eq_g1000 : A006368_map^[k] 64 = g^[1000] 64 := by
    have h_m0 : A006368_map^[1000] (A006368_map^[k] 64) = 64 := by
      rw [← iterate_add_apply A006368_map 1000 k 64, show 1000 + k = m0 by omega]
      exact hm0.2
    have h_m0_g : g^[1000] 64 = g^[1000] (A006368_map^[1000] (A006368_map^[k] 64)) := by rw [h_m0]
    rw [h_g_f_iterate] at h_m0_g
    exact h_m0_g.symm

  have h_iterate_eq_k : (h k)^[k] 64 = A006368_map^[k] 64 := by
    apply h_iterate_eq k k (by omega)
    intro j hj
    exact h_neq_f_i_f_k j hj

  have h_g_iterate_1000 : (h k)^[1000] (g^[1000] 64) = 64 := by
    rw [show 1000 = 1 + 999 by omega, iterate_add_apply (h k) 1 999 (g^[1000] 64)]
    rw [show g^[1000] 64 = g^[999 + 1] 64 by rfl]
    have h_offset : (h k)^[999] (g^[999 + 1] 64) = g^[1] 64 := by
      apply h_g_iterate_offset k 999 1 (by omega)
      intro m hm_pos hm_le
      exact h_neq_g_j_f_k m (by omega) (by omega)
    rw [h_offset]
    change h k (g^[1] 64) = 64
    rw [h_def]
    have h_mem : g^[1] 64 ∈ S k := mem_S_of_lt_g k 1 (by omega)
    have h_neq : g^[1] 64 ≠ A006368_map^[k] 64 := h_neq_g_j_f_k 1 (by omega) (by omega)
    rw [if_pos ⟨h_mem, h_neq⟩]
    rw [show g^[1] 64 = g 64 by rfl, f_g]

  have h_eq_final : (h k)^[k + 1000] 64 = 64 := by
    rw [show k + 1000 = 1000 + k by omega, iterate_add_apply (h k) 1000 k 64]
    rw [h_iterate_eq_k, h_fk_eq_g1000, h_g_iterate_1000]

  have h_m0_eq : k + 1000 = m0 := by omega
  rw [h_m0_eq] at h_eq_final

  have h_m0_neq : (h k)^[m0] 64 ≠ 64 := by
    rw [show m0 = (1000 - 1) + (k + 1) by omega, iterate_add_apply (h k) (1000 - 1) (k + 1) 64]
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
    omega

  exact h_m0_neq h_eq_final




