import FormalConjectures.Util.ProblemImports

open List Nat Function Set

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps

def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def ca_step_global (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  let next_config_long := List.zipWith Nat.add base_masses received_masses
  trim_trailing_zeros next_config_long

def config_step (C : ℕ → ℕ) : ℕ → ℕ := fun j =>
  if j = 0 then
    (C 0 + 1) / 2
  else
    (C j + 1) / 2 + C (j - 1) / 2

lemma getD_zero_list (B : List ℕ) (hB : ∀ x ∈ B, x = 0) (j : ℕ) :
  B[j]?.getD 0 = 0 := by
  induction' B with y ys ih generalizing j
  · rfl
  · have hy : y = 0 := hB y (by simp)
    have hys : ∀ x ∈ ys, x = 0 := fun x hx => hB x (by simp [hx])
    subst hy
    cases j
    · rfl
    · exact ih hys _

lemma getD_append_zero_list (A B : List ℕ) (hB : ∀ x ∈ B, x = 0) (j : ℕ) :
  (A ++ B)[j]?.getD 0 = A[j]?.getD 0 := by
  induction' A with x xs ih generalizing j
  · dsimp
    exact getD_zero_list B hB j
  · dsimp
    cases j
    · rfl
    · exact ih _

lemma takeWhile_append_dropWhile {α : Type _} (p : α → Bool) (l : List α) :
  l.takeWhile p ++ l.dropWhile p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.takeWhile, List.dropWhile]
    split
    · dsimp
      rw [ih]
    · rfl

lemma trim_trailing_zeros_append (l : List ℕ) :
  (trim_trailing_zeros l) ++ (l.reverse.takeWhile (fun y => y = 0)).reverse = l := by
  have h := takeWhile_append_dropWhile (fun y => y = 0) l.reverse
  have h_rev := congr_arg List.reverse h
  rw [List.reverse_append, List.reverse_reverse] at h_rev
  exact h_rev

lemma B_all_zero (l : List ℕ) (x : ℕ) (hx : x ∈ (l.reverse.takeWhile (fun y => y = 0)).reverse) :
  x = 0 := by
  rw [List.mem_reverse] at hx
  have h_dec := List.mem_takeWhile_imp hx
  exact of_decide_eq_true h_dec

lemma getD_trim_trailing_zeros (l : List ℕ) (j : ℕ) :
  (trim_trailing_zeros l)[j]?.getD 0 = l[j]?.getD 0 := by
  have h_eq := trim_trailing_zeros_append l
  nth_rw 2 [← h_eq]
  rw [getD_append_zero_list _ _ (B_all_zero l)]

lemma getD_zipWith_add (A B : List ℕ) (h : A.length = B.length) (j : ℕ) :
  (List.zipWith Nat.add A B)[j]?.getD 0 = A[j]?.getD 0 + B[j]?.getD 0 := by
  induction' A with x xs ih generalizing B j
  · dsimp at h
    have : B = [] := by cases B <;> [rfl; contradiction]
    subst this
    rfl
  · cases B with
    | nil => contradiction
    | cons y ys =>
      dsimp at h
      have hlen : xs.length = ys.length := by omega
      cases j with
      | zero => rfl
      | succ j =>
        dsimp
        exact ih ys hlen j

lemma getD_concat_zero (A : List ℕ) (j : ℕ) :
  (A ++ [0])[j]?.getD 0 = A[j]?.getD 0 := by
  induction' A with x xs ih generalizing j
  · cases j <;> rfl
  · dsimp
    cases j
    · rfl
    · exact ih _

lemma getD_map_zero {α β : Type _} (f : α → β) (dα : α) (dβ : β) (h_f : f dα = dβ) (L : List α) (j : ℕ) :
  (L.map f)[j]?.getD dβ = f (L[j]?.getD dα) := by
  induction' L with x xs ih generalizing j
  · dsimp
    rw [h_f]
  · cases j
    · rfl
    · exact ih _

lemma ca_step_global_eq_config_step (L : List ℕ) (j : ℕ) :
  (ca_step_global L)[j]?.getD 0 = config_step (fun x => L[x]?.getD 0) j := by
  unfold ca_step_global config_step
  dsimp
  rw [getD_trim_trailing_zeros]
  have hlen : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by
    simp
  rw [getD_zipWith_add _ _ hlen j]
  rw [getD_concat_zero]
  have h_ceil : half_ceil 0 = 0 := rfl
  have h_floor : half_floor 0 = 0 := rfl
  rw [getD_map_zero half_ceil 0 0 h_ceil]
  cases j
  · dsimp
    rfl
  · dsimp [getD]
    rw [getD_map_zero half_floor 0 0 h_floor]
    rfl

def S_global (n : ℕ) (t : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step_global acc) [n]

def S_func : ℕ → ℕ → ℕ → ℕ
  | n, 0 => fun j => if j = 0 then n else 0
  | n, t + 1 => config_step (S_func n t)

lemma S_global_succ (n t : ℕ) : S_global n (t + 1) = ca_step_global (S_global n t) := by
  unfold S_global
  rw [List.range_succ, List.foldl_append]
  rfl

lemma S_global_eq_S_func (n t : ℕ) (j : ℕ) :
  (S_global n t)[j]?.getD 0 = S_func n t j := by
  induction' t with t ih generalizing j
  · dsimp [S_global, S_func]
    cases j
    · rfl
    · rfl
  · rw [S_global_succ, ca_step_global_eq_config_step]
    have h_fun : (fun x => (S_global n t)[x]?.getD 0) = S_func n t := by
      ext x
      exact ih x
    rw [h_fun]
    rfl

lemma config_step_mono (C1 C2 : ℕ → ℕ) (h : ∀ j, C1 j ≤ C2 j) :
  ∀ j, config_step C1 j ≤ config_step C2 j := by
  intro j
  unfold config_step
  split_ifs
  · have h0 := h 0
    omega
  · have h1 := h j
    have h2 := h (j - 1)
    omega

lemma config_step_add_one_explicit (C : ℕ → ℕ) (p : ℕ) :
  config_step (fun j => C j + (if j = p then 1 else 0)) =
       fun j => config_step C j + (if j = if C p % 2 = 0 then p else p + 1 then 1 else 0) := by
  ext j
  unfold config_step
  dsimp
  split_ifs <;> (try subst_vars) <;> omega

lemma config_step_add_one (C : ℕ → ℕ) (p : ℕ) :
  ∃ p', config_step (fun j => C j + (if j = p then 1 else 0)) =
       fun j => config_step C j + (if j = p' then 1 else 0) := by
  use (if C p % 2 = 0 then p else p + 1)
  exact config_step_add_one_explicit C p

lemma S_func_add_one (n : ℕ) (t : ℕ) :
  ∃ p, S_func (n + 1) t = fun j => S_func n t j + (if j = p then 1 else 0) := by
  induction' t with t ih
  · use 0
    ext j
    dsimp [S_func]
    split_ifs <;> omega
  · rcases ih with ⟨p, hp⟩
    dsimp [S_func]
    rw [hp]
    exact config_step_add_one (S_func n t) p

lemma config_step_stable (n : ℕ) :
  config_step (fun j => if j < n then 1 else 0) = fun j => if j < n then 1 else 0 := by
  ext j
  unfold config_step
  dsimp
  split_ifs <;> omega

def initial_segment (C : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → C j > 0 → C i > 0

lemma initial_segment_step (C : ℕ → ℕ) (hC : initial_segment C) :
  initial_segment (config_step C) := by
  intro i j hij hj
  unfold config_step at hj ⊢
  split_ifs at hj ⊢ <;> (try subst_vars) <;> (try omega)
  · -- j > 0, i = 0
    have h_or : C j > 0 ∨ C (j - 1) > 0 := by
      by_contra! h_and
      have h1 : C j = 0 := by omega
      have h2 : C (j - 1) = 0 := by omega
      rw [h1, h2] at hj
      revert hj
      decide
    have hk : ∃ k, (k = j ∨ k = j - 1) ∧ C k > 0 := by
      rcases h_or with h1 | h2
      · use j; omega
      · use j - 1; omega
    rcases hk with ⟨k, hk_eq, hk_gt⟩
    have hC0 : C 0 > 0 := by
      rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
      · exact hk_gt
      · exact hC 0 k hk_pos hk_gt
    generalize hC0_val : C 0 = x at hC0 ⊢
    omega
  · -- j > 0, i > 0
    have h_or : C j > 0 ∨ C (j - 1) > 0 := by
      by_contra! h_and
      have h1 : C j = 0 := by omega
      have h2 : C (j - 1) = 0 := by omega
      rw [h1, h2] at hj
      revert hj
      decide
    have hk : ∃ k, (k = j ∨ k = j - 1) ∧ C k > 0 := by
      rcases h_or with h1 | h2
      · use j; omega
      · use j - 1; omega
    rcases hk with ⟨k, hk_eq, hk_gt⟩
    have hC_i : C i > 0 := by
      rcases lt_or_ge i k with hik | h_ge
      · exact hC i k hik hk_gt
      · have : i = k := by omega
        subst this
        exact hk_gt
    generalize hC_val : C i = x at hC_i ⊢
    omega

lemma S_func_initial_segment (n t : ℕ) :
  initial_segment (S_func n t) := by
  induction' t with t ih
  · dsimp [S_func, initial_segment]
    intro i j hij hj
    split_ifs at hj ⊢ <;> (try subst_vars) <;> omega
  · exact initial_segment_step (S_func n t) ih

lemma sum_ge_getD (L : List ℕ) (j : ℕ) : L.sum ≥ L[j]?.getD 0 := by
  induction' L with x xs ih generalizing j
  · rfl
  · cases j with
    | zero =>
      change x + xs.sum ≥ x
      omega
    | succ r =>
      change x + xs.sum ≥ xs[r]?.getD 0
      have := ih r
      omega

lemma sum_ge_of_ge_one (L : List ℕ) (n : ℕ) (h : ∀ j < n, L[j]?.getD 0 ≥ 1) : L.sum ≥ n := by
  induction' L with x xs ih generalizing n
  · by_cases hn : n = 0
    · subst hn; rfl
    · have h0 : ([] : List ℕ)[0]?.getD 0 ≥ 1 := h 0 (by omega)
      dsimp at h0
      omega
  · cases n with
    | zero => omega
    | succ s =>
      dsimp
      have hx : x ≥ 1 := h 0 (by omega)
      have h_xs : ∀ j < s, xs[j]?.getD 0 ≥ 1 := by
        intro j hj
        have h_j1 := h (j + 1) (by omega)
        exact h_j1
      have ih_s := ih s h_xs
      omega

lemma sum_gt_of_extra_gt (L : List ℕ) (n : ℕ) (h : ∀ j < n, L[j]?.getD 0 ≥ 1)
  (j : ℕ) (hj : j ≥ n) (hj2 : L[j]?.getD 0 ≥ 1) : L.sum ≥ n + 1 := by
  induction' L with x xs ih generalizing n j
  · have h0 : ([] : List ℕ)[j]?.getD 0 ≥ 1 := hj2
    dsimp at h0
    omega
  · cases n with
    | zero =>
      have h_sum_ge := sum_ge_getD (x :: xs) j
      omega
    | succ s =>
      cases j with
      | zero => omega
      | succ r =>
        change x + xs.sum ≥ s + 2
        have hx : x ≥ 1 := h 0 (by omega)
        have h_xs : ∀ j < s, xs[j]?.getD 0 ≥ 1 := by
          intro j hj
          have h_j1 := h (j + 1) (by omega)
          exact h_j1
        have hj_r : r ≥ s := by omega
        have hj2_r : xs[r]?.getD 0 ≥ 1 := by
          change (x :: xs)[r + 1]?.getD 0 ≥ 1 at hj2
          exact hj2
        have ih_s := ih s h_xs r hj_r hj2_r
        omega

lemma sum_gt_of_any_gt (L : List ℕ) (n : ℕ) (h : ∀ j < n, L[j]?.getD 0 ≥ 1)
  (k : ℕ) (hk : k < n) (hk2 : L[k]?.getD 0 ≥ 2) : L.sum ≥ n + 1 := by
  induction' L with x xs ih generalizing n k
  · have h0 : ([] : List ℕ)[k]?.getD 0 ≥ 2 := hk2
    dsimp at h0
    omega
  · cases n with
    | zero => omega
    | succ s =>
      dsimp
      cases k with
      | zero =>
        have hx : x ≥ 2 := hk2
        have h_xs : ∀ j < s, xs[j]?.getD 0 ≥ 1 := by
          intro j hj
          have h_j1 := h (j + 1) (by omega)
          exact h_j1
        have h_xs_sum := sum_ge_of_ge_one xs s h_xs
        omega
      | succ r =>
        have hx : x ≥ 1 := h 0 (by omega)
        have h_xs : ∀ j < s, xs[j]?.getD 0 ≥ 1 := by
          intro j hj
          have h_j1 := h (j + 1) (by omega)
          exact h_j1
        have h_xs_gt : xs[r]?.getD 0 ≥ 2 := hk2
        have h_xs_sum := ih s h_xs r (by omega) h_xs_gt
        omega

lemma sum_zero_list (B : List ℕ) (hB : ∀ x ∈ B, x = 0) : B.sum = 0 := by
  induction' B with y ys ih
  · rfl
  · have hy : y = 0 := hB y (by simp)
    have hys : ∀ x ∈ ys, x = 0 := fun x hx => hB x (by simp [hx])
    subst hy
    dsimp
    have := ih hys
    omega

lemma sum_append_zero_list (A B : List ℕ) (hB : ∀ x ∈ B, x = 0) :
  (A ++ B).sum = A.sum := by
  rw [List.sum_append, sum_zero_list B hB]
  omega

lemma trim_trailing_zeros_sum (l : List ℕ) : (trim_trailing_zeros l).sum = l.sum := by
  have h_eq := trim_trailing_zeros_append l
  nth_rw 2 [← h_eq]
  rw [sum_append_zero_list _ _ (B_all_zero l)]

lemma sum_zipWith_add (A B : List ℕ) (h : A.length = B.length) :
  (List.zipWith Nat.add A B).sum = A.sum + B.sum := by
  induction' A with x xs ih generalizing B
  · dsimp at h
    have : B = [] := by cases B <;> [rfl; contradiction]
    subst this
    rfl
  · cases B with
    | nil => contradiction
    | cons y ys =>
      dsimp at h
      have hlen : xs.length = ys.length := by omega
      dsimp
      rw [ih ys hlen]
      omega

lemma sum_map_ceil_floor (L : List ℕ) :
  (L.map half_ceil).sum + (L.map half_floor).sum = L.sum := by
  induction' L with x xs ih
  · rfl
  · dsimp
    have h_ceil_floor : half_ceil x + half_floor x = x := by
      unfold half_ceil half_floor
      omega
    omega

lemma ca_step_global_sum (L : List ℕ) : (ca_step_global L).sum = L.sum := by
  unfold ca_step_global
  rw [trim_trailing_zeros_sum]
  have hlen : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by
    simp
  rw [sum_zipWith_add _ _ hlen]
  have h1 := sum_map_ceil_floor L
  simp
  omega

lemma S_global_sum (n t : ℕ) : (S_global n t).sum = n := by
  induction' t with t ih
  · dsimp [S_global]
  · rw [S_global_succ, ca_step_global_sum, ih]

lemma eq_zero_of_sum_and_ge (L : List ℕ) (n : ℕ) (h_sum : L.sum = n) (h : ∀ j < n, L[j]?.getD 0 ≥ 1) :
  ∀ j ≥ n, L[j]?.getD 0 = 0 := by
  intro j hj
  by_contra h_ne
  have h_gt : L[j]?.getD 0 ≥ 1 := by omega
  have h_sum_gt := sum_gt_of_extra_gt L n h j hj h_gt
  omega

lemma eq_one_of_sum_and_ge (L : List ℕ) (n : ℕ) (h_sum : L.sum = n) (h : ∀ j < n, L[j]?.getD 0 ≥ 1) :
  ∀ j < n, L[j]?.getD 0 = 1 := by
  intro j hj
  by_contra h_ne
  have hj_ge := h j hj
  have h_gt : L[j]?.getD 0 ≥ 2 := by omega
  have h_sum_gt := sum_gt_of_any_gt L n h j hj h_gt
  omega

lemma a_mono_helper (n t : ℕ) (p : ℕ)
  (h_eq : ∀ j, S_func n t j + (if j = p then 1 else 0) = if j < n + 1 then 1 else 0) :
  S_func n t n = 0 := by
  by_contra h_gt
  have h_gt0 : S_func n t n > 0 := by omega
  have h_p_ge : p ≥ n := by
    by_contra h_lt
    have hp_lt : p < n := by omega
    have h_pos : S_func n t p > 0 := S_func_initial_segment n t p n hp_lt h_gt0
    have h_eq_p := h_eq p
    split_ifs at h_eq_p <;> omega
  have hp_eq : p = n := by
    by_contra hp_ne
    have hp_gt : p > n := by omega
    have h_eq_p := h_eq p
    split_ifs at h_eq_p <;> omega
  have h_eq_n := h_eq n
  split_ifs at h_eq_n <;> omega

lemma a_mono_helper_2 (n t : ℕ) (p : ℕ)
  (h_eq : ∀ j, S_func n t j + (if j = p then 1 else 0) = if j < n + 1 then 1 else 0)
  (h_sn_n : S_func n t n = 0) :
  p = n ∧ S_func n t = fun j => if j < n then 1 else 0 := by
  have hp_eq : p = n := by
    have h_eq_n := h_eq n
    split_ifs at h_eq_n <;> omega
  constructor
  · exact hp_eq
  · ext j
    have h_eq_j := h_eq j
    split_ifs at h_eq_j ⊢ <;> omega

/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k}$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/
lemma S_func_stable_ind (n : ℕ) (k : ℕ) (hk : S_func n k = fun j => if j < n then 1 else 0)
  (p : ℕ) (hp_eq : S_func (n + 1) k = fun j => (if j < n then 1 else 0) + (if j = p then 1 else 0))
  (hp_le : p ≤ n) (d : ℕ) :
  S_func (n + 1) (k + d) = fun j => (if j < n then 1 else 0) + (if j = if p + d < n then p + d else n then 1 else 0) := by
  induction' d with d ih
  · dsimp
    have h_p : (if p < n then p else n) = p := by split_ifs <;> omega
    rw [h_p]
    exact hp_eq
  · have h_succ : k + (d + 1) = (k + d) + 1 := by omega
    rw [h_succ]
    change config_step (S_func (n + 1) (k + d)) = _
    rw [ih]
    ext j
    unfold config_step
    dsimp
    split_ifs <;> (try subst_vars) <;> omega


lemma dropWhile_eq_self_head_ne_zero {α : Type _} (p : α → Bool) (l : List α) (hl : l.dropWhile p = l) (h_nil : l ≠ []) :
  ¬ p (l.head h_nil) := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    dsimp [List.dropWhile] at hl
    by_cases h : p x
    · rw [h] at hl
      have h_len := congr_arg List.length hl
      dsimp [List.length] at h_len
      have h_le := List.length_dropWhile_le p xs
      omega
    · exact h

lemma last_ne_zero_of_trimmed (L : List ℕ) (h_trim : trim_trailing_zeros L = L) (hL : L ≠ []) :
  have : L.length > 0 := by cases L <;> [contradiction; simp]
  L[L.length - 1]'(by omega) ≠ 0 := by
  have h_len : L.length > 0 := by cases L <;> [contradiction; simp]
  have h_rev : L.reverse = L.reverse.dropWhile (fun x => x = 0) := by
    unfold trim_trailing_zeros at h_trim
    have h_rev_rev := congr_arg List.reverse h_trim
    simp only [List.reverse_reverse] at h_rev_rev
    exact h_rev_rev.symm
  have h_rev_nil : L.reverse ≠ [] := by
    intro hc
    have : L = [] := by
      have h_rev_rev_L := congr_arg List.reverse hc
      simp only [List.reverse_reverse] at h_rev_rev_L
      exact h_rev_rev_L
    contradiction
  have h_head := dropWhile_eq_self_head_ne_zero (fun x => x = 0) L.reverse h_rev.symm h_rev_nil
  have h_head_eq : L.reverse.head h_rev_nil = L[L.length - 1]'(by omega) := by
    rw [← List.getLast_eq_head_reverse hL]
    rw [List.getLast_eq_getElem]
  rw [h_head_eq] at h_head
  simp only [decide_eq_true_iff] at h_head
  exact h_head

lemma length_eq_of_getD (L : List ℕ) (n : ℕ) (h_trim : trim_trailing_zeros L = L)
  (h_eq : ∀ j, L[j]?.getD 0 = if j < n then 1 else 0) : L.length = n := by
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · have h_spec := h_eq L.length
    have h_none : L[L.length]? = none := List.getElem?_eq_none (by omega)
    rw [h_none] at h_spec
    dsimp at h_spec
    split_ifs at h_spec
  · have h_nz : L.length > 0 := by omega
    have h_L_ne : L ≠ [] := by
      intro hc
      subst hc
      dsimp at h_nz
      omega
    have h_last := last_ne_zero_of_trimmed L h_trim h_L_ne
    have h_spec := h_eq (L.length - 1)
    have h_get : L[L.length - 1]? = some (L[L.length - 1]'(by omega)) := by
      rw [List.getElem?_eq_getElem (by omega)]
    rw [h_get] at h_spec
    dsimp at h_spec
    split_ifs at h_spec <;> omega

lemma eq_replicate_of_getD (L : List ℕ) (n : ℕ) (h_trim : trim_trailing_zeros L = L)
  (h_eq : ∀ j, L[j]?.getD 0 = if j < n then 1 else 0) : L = List.replicate n 1 := by
  have h_len := length_eq_of_getD L n h_trim h_eq
  refine List.ext_get ?_ ?_
  · rw [h_len, List.length_replicate]
  · intro j hj1 hj2
    simp only [List.get_eq_getElem]
    rw [List.getElem_replicate]
    have h_get : L[j]? = some (L[j]'(hj1)) := List.getElem?_eq_getElem hj1
    have h_spec := h_eq j
    rw [h_get] at h_spec
    dsimp at h_spec
    split_ifs at h_spec with hj
    · exact h_spec
    · omega



/--
Conjecture A300997: The finite difference of this sequence only contains 1's and 2's.
Specifically, $\forall n \ge 1, a(n+1) - a(n) \in \{1, 2\}$.
It is also conjectured that $a(n) = 2n - \sum_{k=1}^{n} I(k}$ where $I(n)$ is the indicator function of some other sequence (A305992).
-/

lemma a_def (n : ℕ) (hn : 1 ≤ n) : a n = sInf {k | S_global n k = List.replicate n 1} := by
  unfold a
  split_ifs with h
  · omega
  · rfl



lemma getD_replicate_one (n : ℕ) (j : ℕ) : (List.replicate n 1)[j]?.getD 0 = if j < n then 1 else 0 := by
  by_cases h : j < n
  · rw [getElem?_replicate_of_lt h]
    dsimp
    rw [if_pos h]
  · have h_ge : (List.replicate n 1).length ≤ j := by simp; omega
    have h_none : (List.replicate n 1)[j]? = none := List.getElem?_eq_none h_ge
    rw [h_none]
    dsimp
    rw [if_neg h]



lemma a_one_zero : a 1 = 0 := by
  rw [a_def 1 (by omega)]
  have h_zero : S_global 1 0 = List.replicate 1 1 := by
    dsimp [S_global]
  have h_mem : 0 ∈ {k | S_global 1 k = List.replicate 1 1} := h_zero
  have h_le := Nat.sInf_le h_mem
  omega

lemma a_two_one : a 2 = 1 := by
  rw [a_def 2 (by omega)]
  have h_one : S_global 2 1 = List.replicate 2 1 := rfl
  have h_mem : 1 ∈ {k | S_global 2 k = List.replicate 2 1} := h_one
  have h_le := Nat.sInf_le h_mem
  have h_not : 0 ∉ {k | S_global 2 k = List.replicate 2 1} := by
    intro hc
    nomatch hc
  have h_ne : {k | S_global 2 k = List.replicate 2 1}.Nonempty := ⟨1, h_mem⟩
  have h_mem_inf := Nat.sInf_mem h_ne
  have h_inf_ne : sInf {k | S_global 2 k = List.replicate 2 1} ≠ 0 := by
    intro hc
    rw [hc] at h_mem_inf
    exact h_not h_mem_inf
  omega

lemma a_three_three : a 3 = 3 := by
  rw [a_def 3 (by omega)]
  have h_three : S_global 3 3 = List.replicate 3 1 := rfl
  have h_mem : 3 ∈ {k | S_global 3 k = List.replicate 3 1} := h_three
  have h_le := Nat.sInf_le h_mem
  have h_not_0 : 0 ∉ {k | S_global 3 k = List.replicate 3 1} := fun hc => by nomatch hc
  have h_not_1 : 1 ∉ {k | S_global 3 k = List.replicate 3 1} := fun hc => by nomatch hc
  have h_not_2 : 2 ∉ {k | S_global 3 k = List.replicate 3 1} := fun hc => by nomatch hc
  have h_ne : {k | S_global 3 k = List.replicate 3 1}.Nonempty := ⟨3, h_mem⟩
  have h_mem_inf := Nat.sInf_mem h_ne
  have h_inf_ne_0 : sInf {k | S_global 3 k = List.replicate 3 1} ≠ 0 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_0 h_mem_inf
  have h_inf_ne_1 : sInf {k | S_global 3 k = List.replicate 3 1} ≠ 1 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_1 h_mem_inf
  have h_inf_ne_2 : sInf {k | S_global 3 k = List.replicate 3 1} ≠ 2 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_2 h_mem_inf
  omega

lemma a_four_four : a 4 = 4 := by
  rw [a_def 4 (by omega)]
  have h_four : S_global 4 4 = List.replicate 4 1 := rfl
  have h_mem : 4 ∈ {k | S_global 4 k = List.replicate 4 1} := h_four
  have h_le := Nat.sInf_le h_mem
  have h_not_0 : 0 ∉ {k | S_global 4 k = List.replicate 4 1} := fun hc => by nomatch hc
  have h_not_1 : 1 ∉ {k | S_global 4 k = List.replicate 4 1} := fun hc => by nomatch hc
  have h_not_2 : 2 ∉ {k | S_global 4 k = List.replicate 4 1} := fun hc => by nomatch hc
  have h_not_3 : 3 ∉ {k | S_global 4 k = List.replicate 4 1} := fun hc => by nomatch hc
  have h_ne : {k | S_global 4 k = List.replicate 4 1}.Nonempty := ⟨4, h_mem⟩
  have h_mem_inf := Nat.sInf_mem h_ne
  have h_inf_ne_0 : sInf {k | S_global 4 k = List.replicate 4 1} ≠ 0 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_0 h_mem_inf
  have h_inf_ne_1 : sInf {k | S_global 4 k = List.replicate 4 1} ≠ 1 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_1 h_mem_inf
  have h_inf_ne_2 : sInf {k | S_global 4 k = List.replicate 4 1} ≠ 2 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_2 h_mem_inf
  have h_inf_ne_3 : sInf {k | S_global 4 k = List.replicate 4 1} ≠ 3 := by
    intro hc; rw [hc] at h_mem_inf; exact h_not_3 h_mem_inf
  omega


lemma S_func_at_n_zero (n : ℕ) (t : ℕ) : S_func n t n = 0 := by
  by_contra h_nz
  have h_gt : S_func n t n > 0 := by omega
  have h_is := S_func_initial_segment n t
  have h_all : ∀ i < n, (S_global n t)[i]?.getD 0 ≥ 1 := by
    intro i hi
    have h_si := h_is i n hi h_gt
    rw [S_global_eq_S_func]
    omega
  have h_extra : (S_global n t)[n]?.getD 0 ≥ 1 := by
    rw [S_global_eq_S_func]
    omega
  have h_sum_gt := sum_gt_of_extra_gt (S_global n t) n h_all n (by omega) h_extra
  have h_sum_eq := S_global_sum n t
  omega

lemma trim_trailing_zeros_id (l : List ℕ) :
  trim_trailing_zeros (trim_trailing_zeros l) = trim_trailing_zeros l := by
  unfold trim_trailing_zeros
  simp only [List.reverse_reverse]
  rw [List.dropWhile_idempotent]

lemma ca_step_global_trimmed (config : List ℕ) :
  trim_trailing_zeros (ca_step_global config) = ca_step_global config := by
  unfold ca_step_global
  exact trim_trailing_zeros_id _

lemma S_global_trimmed (n : ℕ) (t : ℕ) :
  trim_trailing_zeros (S_global (n + 1) t) = S_global (n + 1) t := by
  induction' t with t ih
  · dsimp [S_global]
    unfold trim_trailing_zeros
    simp
  · rw [S_global_succ]
    exact ca_step_global_trimmed _

lemma stable_steps_nonempty (n : ℕ) (hn : 1 ≤ n) : ({k | S_global n k = List.replicate n 1} : Set ℕ).Nonempty := by
  induction' n with n ih
  · contradiction
  · by_cases hn1 : n = 0
    · subst hn1
      use 0
      dsimp [S_global]
    · have hn_ge : 1 ≤ n := by omega
      rcases ih hn_ge with ⟨k, hk⟩
      -- S_global n k = List.replicate n 1
      -- So S_func n k = fun j => if j < n then 1 else 0
      have h_func_eq : S_func n k = fun j => if j < n then 1 else 0 := by
        ext j
        rw [← S_global_eq_S_func]
        rw [hk]
        exact getD_replicate_one n j
      rcases S_func_add_one n k with ⟨p, hp_eq⟩
      rw [h_func_eq] at hp_eq
      have hp_le : p ≤ n := by
        by_contra! hp_gt
        have h_is := S_func_initial_segment (n + 1) k
        have h_spec := h_is n p hp_gt
        have h_pos : S_func (n + 1) k p > 0 := by
          rw [hp_eq]
          dsimp
          split_ifs <;> omega
        have h_zero : S_func (n + 1) k n = 0 := by
          rw [hp_eq]
          dsimp
          split_ifs <;> omega
        have h_congr := h_spec h_pos
        omega
      have h_stable := S_func_stable_ind n k h_func_eq p hp_eq hp_le (n - p)
      use k + (n - p)
      dsimp
      apply eq_replicate_of_getD
      · exact S_global_trimmed _ _
      · intro j
        rw [S_global_eq_S_func]
        rw [h_stable]
        dsimp
        split_ifs <;> omega

lemma config_step_add_one_ge (C : ℕ → ℕ) (p : ℕ) (p' : ℕ)
  (hp' : config_step (fun j => C j + (if j = p then 1 else 0)) = fun j => config_step C j + (if j = p' then 1 else 0)) :
  p ≤ p' := by
  by_contra! h_lt
  have h_j := congr_fun hp' p'
  unfold config_step at h_j
  dsimp at h_j
  split_ifs at h_j <;> omega

lemma a_le_plus_two_helper (n : ℕ) (hn : 1 ≤ n) : ∃ p ≤ n, a (n + 1) ≤ a n + (n - p) := by
  have hn_pos : 1 ≤ n + 1 := by omega
  have h_ne : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn
  have hk : S_global n (a n) = List.replicate n 1 := by
    rw [a_def n hn]
    exact Nat.sInf_mem h_ne
  let k := a n
  have h_func_eq : S_func n k = fun j => if j < n then 1 else 0 := by
    ext j
    rw [← S_global_eq_S_func]
    rw [hk]
    exact getD_replicate_one n j
  rcases S_func_add_one n k with ⟨p, hp_eq⟩
  rw [h_func_eq] at hp_eq
  have hp_le : p ≤ n := by
    by_contra! hp_gt
    have h_is := S_func_initial_segment (n + 1) k
    have h_spec := h_is n p hp_gt
    have h_pos : S_func (n + 1) k p > 0 := by
      rw [hp_eq]
      dsimp
      split_ifs <;> omega
    have h_zero : S_func (n + 1) k n = 0 := by
      rw [hp_eq]
      dsimp
      split_ifs <;> omega
    have h_congr := h_spec h_pos
    omega
  use p
  constructor
  · exact hp_le
  · have h_stable := S_func_stable_ind n k h_func_eq p hp_eq hp_le (n - p)
    have h_step : S_global (n + 1) (k + (n - p)) = List.replicate (n + 1) 1 := by
      apply eq_replicate_of_getD
      · exact S_global_trimmed _ _
      · intro j
        rw [S_global_eq_S_func]
        rw [h_stable]
        dsimp
        split_ifs <;> omega
    rw [a_def (n + 1) hn_pos]
    apply Nat.sInf_le
    exact h_step

lemma eq_replicate_of_sum_and_ge (L : List ℕ) (n : ℕ) (h_trim : trim_trailing_zeros L = L)
  (h_sum : L.sum = n) (h : ∀ j < n, L[j]?.getD 0 ≥ 1) : L = List.replicate n 1 := by
  apply eq_replicate_of_getD _ n h_trim
  intro j
  by_cases hj : j < n
  · rw [if_pos hj]
    exact eq_one_of_sum_and_ge L n h_sum h j hj
  · rw [if_neg hj]
    exact eq_zero_of_sum_and_ge L n h_sum h j (by omega)

lemma getD_last_zero_of_not_stable (L : List ℕ) (n : ℕ) (hn : 1 ≤ n) (h_trim : trim_trailing_zeros L = L)
  (h_sum : L.sum = n) (h_is : initial_segment (fun j => L[j]?.getD 0)) (h_ne : L ≠ List.replicate n 1) :
  L[n - 1]?.getD 0 = 0 := by
  by_contra! h_nz
  have h_nz_gt : (fun j => L[j]?.getD 0) (n - 1) > 0 := by
    dsimp
    omega
  have h_ge1 : L[n - 1]?.getD 0 ≥ 1 := by omega
  have h_all : ∀ j < n, L[j]?.getD 0 ≥ 1 := by
    intro j hj
    by_cases hj_eq : j = n - 1
    · subst hj_eq; exact h_ge1
    · have hj_lt : j < n - 1 := by omega
      have h_pos := h_is j (n - 1) hj_lt h_nz_gt
      dsimp at h_pos
      omega
  have h_repl := eq_replicate_of_sum_and_ge L n h_trim h_sum h_all
  contradiction

lemma S_func_last_zero (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t < a n) :
  S_func n t (n - 1) = 0 := by
  have h_ne : S_global n t ≠ List.replicate n 1 := by
    intro hc
    have h_stable : t ∈ {k | S_global n k = List.replicate n 1} := hc
    have h_le := Nat.sInf_le h_stable
    rw [← a_def n hn] at h_le
    omega
  have h_trim : trim_trailing_zeros (S_global n t) = S_global n t := by
    rcases eq_or_lt_of_le hn with rfl | hn_ge
    · dsimp [S_global]
      have ht_zero : t = 0 := by
        rw [a_one_zero] at ht
        omega
      subst ht_zero
      unfold trim_trailing_zeros
      rfl
    · have h_eq_n : n = (n - 1) + 1 := by omega
      have h_trim_trimmed := S_global_trimmed (n - 1) t
      rw [← h_eq_n] at h_trim_trimmed
      exact h_trim_trimmed
  have h_sum := S_global_sum n t
  have h_is : initial_segment (fun j => (S_global n t)[j]?.getD 0) := by
    intro i j hij hj
    dsimp at hj ⊢
    rw [S_global_eq_S_func] at hj ⊢
    exact S_func_initial_segment n t i j hij hj
  have h_zero := getD_last_zero_of_not_stable (S_global n t) n hn h_trim h_sum h_is h_ne
  rw [S_global_eq_S_func] at h_zero
  exact h_zero

noncomputable def p_seq (n : ℕ) (t : ℕ) : ℕ := Classical.choose (S_func_add_one n t)

lemma hp_seq (n : ℕ) (t : ℕ) : S_func (n + 1) t = fun j => S_func n t j + (if j = p_seq n t then 1 else 0) := by
  ext j
  exact congr_fun (Classical.choose_spec (S_func_add_one n t)) j

lemma p_seq_zero (n : ℕ) : p_seq n 0 = 0 := by
  have h := hp_seq n 0
  have h_j := congr_fun h 0
  dsimp [S_func] at h_j
  split_ifs at h_j <;> omega

lemma p_seq_transition (n : ℕ) (t : ℕ) :
  p_seq n (t + 1) = if S_func n t (p_seq n t) % 2 = 0 then p_seq n t else p_seq n t + 1 := by
  generalize hP : (if S_func n t (p_seq n t) % 2 = 0 then p_seq n t else p_seq n t + 1) = P
  have h_s1 : S_func (n + 1) (t + 1) = fun j => S_func n (t + 1) j + (if j = p_seq n (t + 1) then 1 else 0) := hp_seq n (t + 1)
  have h_s2 : S_func (n + 1) (t + 1) = fun j => S_func n (t + 1) j + (if j = P then 1 else 0) := by
    ext j
    change config_step (S_func (n + 1) t) j = _
    rw [hp_seq n t]
    rw [config_step_add_one_explicit]
    rw [hP]
    rfl
  have h_eq_j (j : ℕ) : (if j = p_seq n (t + 1) then (1 : ℕ) else 0) = if j = P then 1 else 0 := by
    have h1 := congr_fun h_s1 j
    have h2 := congr_fun h_s2 j
    omega
  have h_spec := h_eq_j (p_seq n (t + 1))
  have h_spec2 := h_eq_j P
  split_ifs at h_spec h_spec2 <;> omega

lemma S_func_np1_zero_at_n_plus_two (n : ℕ) (hn : 3 ≤ n) (p : ℕ) (hp : p ≤ n - 3)
  (h_stable : S_func n (a n) = fun j => if j < n then 1 else 0)
  (hp_eq : S_func (n + 1) (a n) = fun j => S_func n (a n) j + (if j = p then 1 else 0)) :
  S_func (n + 1) (a n + 2) n = 0 := by
  have hp_eq_rewritten : S_func (n + 1) (a n) = fun j => (if j < n then 1 else 0) + (if j = p then 1 else 0) := by
    rw [hp_eq, h_stable]
  have h_func_2 := S_func_stable_ind n (a n) h_stable p hp_eq_rewritten (by omega) 2
  have h_n := congr_fun h_func_2 n
  rw [h_n]
  have h_cond : p + 2 < n := by omega
  rw [if_pos h_cond]
  split_ifs <;> omega

lemma p_seq_lt_n (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t ≤ a n) : p_seq n t < n := by
  induction' t with t ih
  · rw [p_seq_zero]
    omega
  · have ht_lt : t < a n := by omega
    have ht_le : t ≤ a n := by omega
    have ih_t := ih ht_le
    rw [p_seq_transition]
    have h_zero := S_func_last_zero n hn t ht_lt
    split_ifs with h_if
    · exact ih_t
    · by_cases h_eq : p_seq n t = n - 1
      · rw [h_eq] at h_if
        rw [h_zero] at h_if
        contradiction
      · omega

lemma a_strict_mono (n : ℕ) (hn : 1 ≤ n) : a n < a (n + 1) := by
  by_contra! h_le
  have h_an_pos : 1 ≤ n + 1 := by omega
  have h_stable_np1 : S_global (n + 1) (a (n + 1)) = List.replicate (n + 1) 1 := by
    have h_ne : {k | S_global (n + 1) k = List.replicate (n + 1) 1}.Nonempty := stable_steps_nonempty (n + 1) h_an_pos
    rw [a_def (n+1) h_an_pos]
    exact Nat.sInf_mem h_ne
  have h_func : S_func (n + 1) (a (n + 1)) = fun j => if j < n + 1 then 1 else 0 := by
    ext j
    rw [← S_global_eq_S_func]
    rw [h_stable_np1]
    exact getD_replicate_one (n + 1) j
  have h_p_seq_lt := p_seq_lt_n n hn (a (n + 1)) h_le
  have h_zero := S_func_at_n_zero n (a (n + 1))
  have h_eq_n := congr_fun (hp_seq n (a (n + 1))) n
  have h_func_n := congr_fun h_func n
  rw [if_pos (by omega)] at h_func_n
  split_ifs at h_eq_n with hn_eq
  · omega
  · omega

lemma a_pos (n : ℕ) (hn : 2 ≤ n) : a n > 0 := by
  have hn1 : 1 ≤ n := by omega
  have h_ne : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn1
  by_contra! h_zero
  have hk_an : S_global n (a n) = List.replicate n 1 := by
    rw [a_def n hn1]
    exact Nat.sInf_mem h_ne
  have ht_zero : a n = 0 := by omega
  rw [ht_zero] at hk_an
  dsimp [S_global] at hk_an
  have h_len := congr_arg List.length hk_an
  simp at h_len
  omega

lemma a_eq_a_n_add_n_sub_p (n : ℕ) (hn : 1 ≤ n) :
  a (n + 1) = a n + (n - p_seq n (a n)) := by
  let p := p_seq n (a n)
  let k := a n
  have hn_pos : 1 ≤ n + 1 := by omega
  have h_ne : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn
  have hk : S_global n (a n) = List.replicate n 1 := by
    rw [a_def n hn]
    exact Nat.sInf_mem h_ne
  have hk_k : S_global n k = List.replicate n 1 := hk
  have h_func_eq : S_func n k = fun j => if j < n then 1 else 0 := by
    ext j
    rw [← S_global_eq_S_func]
    rw [hk_k]
    exact getD_replicate_one n j
  have hp_eq : S_func (n + 1) k = fun j => S_func n k j + (if j = p then 1 else 0) := hp_seq n k
  have hp_le : p ≤ n := by
    change p_seq n (a n) ≤ n
    have h_lt := p_seq_lt_n n hn (a n) (by omega)
    omega
  have h_le : a (n + 1) ≤ a n + (n - p) := by
    have hp_eq_rewritten : S_func (n + 1) k = fun j => (if j < n then 1 else 0) + (if j = p then 1 else 0) := by
      rw [hp_eq, h_func_eq]
    have h_stable := S_func_stable_ind n k h_func_eq p hp_eq_rewritten hp_le (n - p)
    have h_step : S_global (n + 1) (k + (n - p)) = List.replicate (n + 1) 1 := by
      apply eq_replicate_of_getD
      · exact S_global_trimmed _ _
      · intro j
        rw [S_global_eq_S_func]
        rw [h_stable]
        dsimp
        split_ifs <;> omega
    rw [a_def (n + 1) hn_pos]
    apply Nat.sInf_le
    exact h_step
  have h_ge : a (n + 1) ≥ a n + (n - p) := by
    by_contra! h_lt
    have h_mono : a n < a (n + 1) := a_strict_mono n hn
    let d := a (n + 1) - a n
    have hd_lt : d < n - p := by omega
    have h_sum : a (n + 1) = a n + d := by omega
    have h_stable_np1 : S_global (n + 1) (a (n + 1)) = List.replicate (n + 1) 1 := by
      have h_ne_np1 : {k | S_global (n + 1) k = List.replicate (n + 1) 1}.Nonempty := stable_steps_nonempty (n + 1) (by omega)
      rw [a_def (n + 1) (by omega)]
      exact Nat.sInf_mem h_ne_np1
    have h_func_np1 : S_func (n + 1) (a (n + 1)) n = 1 := by
      rw [← S_global_eq_S_func]
      rw [h_stable_np1]
      rw [getD_replicate_one]
      simp
    have hp_eq_rewritten : S_func (n + 1) k = fun j => (if j < n then 1 else 0) + (if j = p then 1 else 0) := by
      rw [hp_eq, h_func_eq]
    have h_stable_ind := S_func_stable_ind n k h_func_eq p hp_eq_rewritten hp_le d
    rw [← h_sum] at h_stable_ind
    have h_val := congr_fun h_stable_ind n
    rw [h_func_np1] at h_val
    simp at h_val
    have h_cond : p + d < n := by omega
    have hn_eq := h_val h_cond
    omega
  omega


lemma S_func_mono (n : ℕ) (t j : ℕ) : S_func n t j ≤ S_func (n+1) t j := by
  rw [hp_seq n t]
  dsimp
  omega

lemma S_func_stable_ge (n : ℕ) (hn : 1 ≤ n) (d : ℕ) :
  S_func n (a n + d) = fun j => if j < n then 1 else 0 := by
  induction' d with d ih
  · have h_ne : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn
    have hk : S_global n (a n) = List.replicate n 1 := by
      rw [a_def n hn]
      exact Nat.sInf_mem h_ne
    ext j
    rw [← S_global_eq_S_func]
    rw [Nat.add_zero]
    rw [hk]
    exact getD_replicate_one n j
  · rw [show a n + (d + 1) = (a n + d) + 1 by omega]
    change config_step (S_func n (a n + d)) = _
    rw [ih]
    ext j
    unfold config_step
    dsimp
    split_ifs <;> omega


lemma S_func_last_segment_value (n : ℕ) (hn : 2 ≤ n) : S_func n (a n - 1) (n - 2) ≥ 2 := by
  have hn1 : 1 ≤ n := by omega
  have h_ne : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn1
  have hk : S_global n (a n) = List.replicate n 1 := by
    rw [a_def n hn1]
    exact Nat.sInf_mem h_ne
  have h_func_eq : S_func n (a n) (n - 1) = 1 := by
    rw [← S_global_eq_S_func]
    rw [hk]
    rw [getD_replicate_one]
    rw [if_pos (by omega)]
  have h_mono : a n > 0 := by
    by_contra! h_zero
    have ht_zero : a n = 0 := by omega
    rw [ht_zero] at hk
    dsimp [S_global] at hk
    have h_len := congr_arg List.length hk
    simp at h_len
    omega
  have h_succ : a n = (a n - 1) + 1 := by omega
  rw [h_succ] at h_func_eq
  change config_step (S_func n (a n - 1)) (n - 1) = 1 at h_func_eq
  unfold config_step at h_func_eq
  have h_last_zero := S_func_last_zero n hn1 (a n - 1) (by omega)
  have h_cond : n - 1 ≠ 0 := by omega
  rw [if_neg h_cond] at h_func_eq
  rw [h_last_zero] at h_func_eq
  have h_sub_eq : n - 1 - 1 = n - 2 := by omega
  rw [h_sub_eq] at h_func_eq
  have h_eq : (0 + 1)/2 + S_func n (a n - 1) (n - 2)/2 = 1 := h_func_eq
  have h_div : S_func n (a n - 1) (n - 2)/2 = 1 := by omega
  omega



lemma sum_helper_aux (xs : List ℕ) (m : ℕ) (h : ∀ j < m, xs[j]?.getD 0 ≥ 1)
  (h2 : xs[m]?.getD 0 ≥ 2) : xs.sum ≥ m + 2 := by
  induction' xs with y ys ih generalizing m
  · dsimp at h2
    omega
  · cases m with
    | zero =>
      dsimp
      have hy : y ≥ 2 := h2
      have h_ys_sum := ys.sum.zero_le
      omega
    | succ r =>
      dsimp
      have hy : y ≥ 1 := h 0 (by omega)
      have h_ys : ∀ j < r, ys[j]?.getD 0 ≥ 1 := by
        intro j hj
        have := h (j + 1) (by omega)
        exact this
      have h2_ys : ys[r]?.getD 0 ≥ 2 := h2
      have ih_s := ih r h_ys h2_ys
      omega

lemma sum_gt_helper_last (L : List ℕ) (n : ℕ) (h : ∀ j < n - 2, L[j]?.getD 0 ≥ 1)
  (h2 : L[n - 2]?.getD 0 ≥ 3) (hn : 3 ≤ n) : L.sum ≥ n + 1 := by
  induction' L with x xs ih generalizing n
  · dsimp at h2
    omega
  · cases n with
    | zero => omega
    | succ s =>
      dsimp
      cases s with
      | zero => omega
      | succ r =>
        cases r with
        | zero => omega
        | succ m =>
          have hx : x ≥ 1 := h 0 (by omega)
          have h_xs : ∀ j < m, xs[j]?.getD 0 ≥ 1 := by
            intro j hj
            have h_j1 := h (j + 1) (by omega)
            exact h_j1
          have h2_xs : xs[m]?.getD 0 ≥ 3 := h2
          by_cases hm : 3 ≤ m + 2
          · have ih_s := ih (m + 2) h_xs h2_xs hm
            clear h h2 h_xs h2_xs ih
            omega
          · have h_xs_sum := sum_ge_getD xs 0
            have hm_eq : m = 0 := by omega
            rw [hm_eq] at h2_xs
            clear h h2 h_xs ih
            omega

lemma sum_gt_helper_any (L : List ℕ) (n : ℕ) (h : ∀ j < n - 2, L[j]?.getD 0 ≥ 1)
  (h2 : L[n - 2]?.getD 0 ≥ 2) (k : ℕ) (hk : k < n - 2) (hk2 : L[k]?.getD 0 ≥ 2) (hn : 3 ≤ n) :
  L.sum ≥ n + 1 := by
  induction' L with x xs ih generalizing n k
  · dsimp at hk2
    omega
  · cases n with
    | zero => omega
    | succ s =>
      dsimp
      cases s with
      | zero => omega
      | succ r =>
        cases r with
        | zero => omega
        | succ m =>
          cases k with
          | zero =>
            have hx : x ≥ 2 := hk2
            have h_xs : ∀ j < m, xs[j]?.getD 0 ≥ 1 := by
              intro j hj
              have := h (j + 1) (by omega)
              exact this
            have h2_xs : xs[m]?.getD 0 ≥ 2 := h2
            have h_xs_sum := sum_helper_aux xs m h_xs h2_xs
            clear h h2 hk2 h_xs h2_xs
            omega
          | succ l =>
            have hx : x ≥ 1 := h 0 (by omega)
            have h_xs : ∀ j < m, xs[j]?.getD 0 ≥ 1 := by
              intro j hj
              have h_j1 := h (j + 1) (by omega)
              exact h_j1
            have h2_xs : xs[m]?.getD 0 ≥ 2 := h2
            have h_k_xs : xs[l]?.getD 0 ≥ 2 := hk2
            by_cases hm : 3 ≤ m + 2
            · have ih_s := ih (m + 2) h_xs h2_xs l (by omega) h_k_xs hm
              clear h h2 hk2 h_xs h2_xs h_k_xs ih
              omega
            · omega

lemma S_func_ge_n_zero (n : ℕ) (t : ℕ) (j : ℕ) (hj : j ≥ n) : S_func n t j = 0 := by
  by_contra h_nz
  have h_gt : S_func n t j > 0 := by omega
  rcases eq_or_lt_of_le hj with rfl | h_lt
  · have := S_func_at_n_zero n t
    omega
  · have h_pos := S_func_initial_segment n t n j h_lt h_gt
    have := S_func_at_n_zero n t
    omega

lemma S_func_ge_n_sub_one_zero (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t < a n) (j : ℕ) (hj : j ≥ n - 1) :
  S_func n t j = 0 := by
  rcases eq_or_lt_of_le hj with rfl | h_lt
  · exact S_func_last_zero n hn t ht
  · have hj_ge_n : j ≥ n := by omega
    exact S_func_ge_n_zero n t j hj_ge_n

lemma S_func_last_segment_exact (n : ℕ) (hn : 4 ≤ n) :
  (∀ j < n - 2, S_func n (a n - 1) j = 1) ∧ S_func n (a n - 1) (n - 2) = 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have h_sum := S_global_sum n (a n - 1)
  have h_val := S_func_last_segment_value n hn2
  have h_ne_np1 : {k | S_global n k = List.replicate n 1}.Nonempty := stable_steps_nonempty n hn1
  have h_an_pos : a n > 0 := by
    by_contra! h_zero
    have ht_zero : a n = 0 := by omega
    have hk_an : S_global n (a n) = List.replicate n 1 := by
      rw [a_def n hn1]
      exact Nat.sInf_mem h_ne_np1
    rw [ht_zero] at hk_an
    dsimp [S_global] at hk_an
    have h_len := congr_arg List.length hk_an
    simp at h_len
    omega
  have h_zero : ∀ j ≥ n - 1, S_func n (a n - 1) j = 0 := by
    intro j hj
    have ht : a n - 1 < a n := by omega
    exact S_func_ge_n_sub_one_zero n hn1 (a n - 1) ht j hj
  have h_ge_one : ∀ j < n - 2, S_func n (a n - 1) j ≥ 1 := by
    intro j hj
    have h_seg := S_func_initial_segment n (a n - 1) j (n - 2) hj
    have h_pos : S_func n (a n - 1) (n - 2) > 0 := by omega
    have := h_seg h_pos
    omega
  let L := S_global n (a n - 1)
  have hL_get (j : ℕ) : L[j]?.getD 0 = S_func n (a n - 1) j := S_global_eq_S_func n (a n - 1) j
  have h_L_sum : L.sum = n := h_sum
  have h_L_ge_one : ∀ j < n - 2, L[j]?.getD 0 ≥ 1 := by
    intro j hj
    rw [hL_get]
    exact h_ge_one j hj
  have h_L_ge_two : L[n - 2]?.getD 0 ≥ 2 := by
    rw [hL_get]
    exact h_val
  constructor
  · intro j hj
    by_contra h_ne
    have hj_gt : L[j]?.getD 0 ≥ 2 := by
      have := h_L_ge_one j hj
      rw [← hL_get j] at h_ne
      omega
    have h_gt := sum_gt_helper_any L n h_L_ge_one h_L_ge_two j hj hj_gt hn3
    omega
  · by_contra h_ne
    have h_L_ge_three : L[n - 2]?.getD 0 ≥ 3 := by
      rw [← hL_get (n - 2)] at h_ne
      omega
    have h_gt := sum_gt_helper_last L n h_L_ge_one h_L_ge_three hn3
    omega


lemma p_seq_mono (n : ℕ) (t : ℕ) : p_seq n t ≤ p_seq n (t + 1) := by
  rw [p_seq_transition]
  split_ifs <;> omega


lemma p_seq_step_ge_an (n : ℕ) (hn : 1 ≤ n) (t : ℕ) (ht : t ≥ a n) (hp : p_seq n t < n) : p_seq n (t + 1) = p_seq n t + 1 := by
  have h_trans := p_seq_transition n t
  have h_stable : S_func n t = fun j => if j < n then 1 else 0 := by
    let d := t - a n
    have h_eq := S_func_stable_ge n hn d
    have h_sub : a n + d = t := by omega
    rw [h_sub] at h_eq
    exact h_eq
  have h_val : S_func n t (p_seq n t) = 1 := by
    rw [h_stable]
    dsimp
    rw [if_pos hp]
  rw [h_val] at h_trans
  exact h_trans


lemma p_seq_at_stable_plus (n : ℕ) (hn : 1 ≤ n) (d : ℕ) (h_lt : p_seq n (a n) + d < n) :
  p_seq n (a n + d) = p_seq n (a n) + d := by
  induction d with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ d ih =>
    have h_lt_succ : p_seq n (a n) + d < n := by omega
    have ih_val := ih h_lt_succ
    have h_add_succ : a n + (d + 1) = (a n + d) + 1 := by omega
    rw [h_add_succ]
    rw [p_seq_step_ge_an n hn (a n + d) (by omega)]
    · rw [ih_val]
      omega
    · rw [ih_val]
      omega



lemma S_func_np1_last_zero (n : ℕ) (hn : 4 ≤ n) (hp_lt : p_seq n (a n - 1) < n - 1) : S_func (n + 1) (a n - 1) (n - 1) = 0 := by
  have hn1 : 1 ≤ n := by omega
  rw [hp_seq n (a n - 1)]
  dsimp
  have ht_lt : a n - 1 < a n := by
    have h_an_pos : a n > 0 := a_pos n (by omega)
    omega
  have h_n1 : S_func n (a n - 1) (n - 1) = 0 := S_func_last_zero n hn1 (a n - 1) ht_lt
  rw [h_n1]
  split_ifs <;> omega

lemma S_func_np1_an2_n_eq (n : ℕ) (hn : 4 ≤ n) (hp_lt : p_seq n (a n - 1) < n - 1) :
  S_func (n + 1) (a n + 2) n = if p_seq n (a n - 1) ≥ n - 3 then 1 else 0 := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have h_exact := S_func_last_segment_exact n hn
  have h_n2 := h_exact.2
  have h_n3 := h_exact.1 (n - 3) (by omega)
  have ht_lt : a n - 1 < a n := by
    have h_an_pos : a n > 0 := a_pos n hn2
    omega
  have h_n1 : S_func n (a n - 1) (n - 1) = 0 := S_func_last_zero n hn1 (a n - 1) ht_lt
  have h_n : S_func n (a n - 1) n = 0 := S_func_ge_n_zero n (a n - 1) n (by omega)
  let p' := p_seq n (a n - 1)
  have hp' : p' < n - 1 := hp_lt
  have h_p' : S_func (n + 1) (a n - 1) = fun j => S_func n (a n - 1) j + (if j = p' then 1 else 0) := hp_seq n (a n - 1)

  -- Step a n
  have h_an : a n = (a n - 1) + 1 := by omega
  have h_an_step (j : ℕ) : S_func (n + 1) (a n) j = config_step (S_func (n + 1) (a n - 1)) j := by
    nth_rw 1 [h_an]
    rfl
  have h_val_n1 : S_func (n + 1) (a n - 1) (n - 1) = 0 := by
    rw [h_p']
    dsimp
    rw [h_n1]
    split_ifs <;> omega
  have h_val_n : S_func (n + 1) (a n - 1) n = 0 := by
    rw [h_p']
    dsimp
    rw [h_n]
    split_ifs <;> omega

  have h_step_n1 : S_func (n + 1) (a n) (n - 1) = 1 := by
    rw [h_an_step]
    unfold config_step
    have h_cond : n - 1 ≠ 0 := by omega
    rw [if_neg h_cond]
    rw [h_val_n1]
    have h_val_n2_term : S_func (n + 1) (a n - 1) (n - 2) = 2 + (if n - 2 = p' then 1 else 0) := by
      rw [h_p']
      dsimp
      rw [h_n2]
    have h_sub_eq : n - 1 - 1 = n - 2 := by omega
    rw [h_sub_eq]
    rw [h_val_n2_term]
    split_ifs <;> omega
  have h_step_n : S_func (n + 1) (a n) n = 0 := by
    rw [h_an_step]
    unfold config_step
    have h_cond : n ≠ 0 := by omega
    rw [if_neg h_cond]
    rw [h_val_n, h_val_n1]

  -- Step a n + 1
  have h_an1_step (j : ℕ) : S_func (n + 1) (a n + 1) j = config_step (S_func (n + 1) (a n)) j := rfl
  have h_step1_n : S_func (n + 1) (a n + 1) n = 0 := by
    rw [h_an1_step]
    unfold config_step
    have h_cond : n ≠ 0 := by omega
    rw [if_neg h_cond]
    rw [h_step_n, h_step_n1]

  have h_step_n2 : S_func (n + 1) (a n) (n - 2) = if p' ≥ n - 3 then 2 else 1 := by
    rw [h_an_step]
    unfold config_step
    have h_cond : n - 2 ≠ 0 := by omega
    rw [if_neg h_cond]
    have h_val_n2_term : S_func (n + 1) (a n - 1) (n - 2) = 2 + (if n - 2 = p' then 1 else 0) := by
      rw [h_p']
      dsimp
      rw [h_n2]
    have h_val_n3_term : S_func (n + 1) (a n - 1) (n - 3) = 1 + (if n - 3 = p' then 1 else 0) := by
      rw [h_p']
      dsimp
      rw [h_n3]
    have h_sub_eq2 : n - 2 - 1 = n - 3 := by omega
    rw [h_sub_eq2]
    rw [h_val_n2_term, h_val_n3_term]
    split_ifs <;> omega

  have h_step1_n1 : S_func (n + 1) (a n + 1) (n - 1) = if p' ≥ n - 3 then 2 else 1 := by
    rw [h_an1_step]
    unfold config_step
    have h_cond : n - 1 ≠ 0 := by omega
    rw [if_neg h_cond]
    have h_sub3 : n - 1 - 1 = n - 2 := by omega
    rw [h_sub3]
    rw [h_step_n1, h_step_n2]
    split_ifs <;> omega

  -- Step a n + 2
  have h_an2_step (j : ℕ) : S_func (n + 1) (a n + 2) j = config_step (S_func (n + 1) (a n + 1)) j := by
    have : a n + 2 = (a n + 1) + 1 := by omega
    rw [this]
    rfl
  rw [h_an2_step]
  unfold config_step
  have h_cond_n : n ≠ 0 := by omega
  rw [if_neg h_cond_n]
  rw [h_step1_n, h_step1_n1]
  split_ifs <;> omega


lemma p_seq_mono_ge (n : ℕ) (t1 t2 : ℕ) (h : t1 ≤ t2) : p_seq n t1 ≤ p_seq n t2 := by
  have h_eq : t2 = t1 + (t2 - t1) := by omega
  rw [h_eq]
  generalize t2 - t1 = d
  induction' d with d ih
  · dsimp
    omega
  · have h_step : t1 + (d + 1) = (t1 + d) + 1 := by omega
    rw [h_step]
    have h_mono := p_seq_mono n (t1 + d)
    omega

lemma p_seq_step_eq (n : ℕ) (hn : 4 ≤ n) (t : ℕ) (ht : t ≥ a (n - 1))
  (hp : p_seq n t < p_seq (n - 1) (a (n - 1))) :
  p_seq n (t + 1) = p_seq n t + 1 := by
  have hn_prev : 1 ≤ n - 1 := by omega
  have h_stable := S_func_stable_ge (n - 1) hn_prev (t - a (n - 1))
  have h_add_sub : a (n - 1) + (t - a (n - 1)) = t := by omega
  rw [h_add_sub] at h_stable
  have h_trans := p_seq_transition n t
  have hp_seq_val : S_func n t (p_seq n t) = S_func (n - 1) t (p_seq n t) + (if p_seq n t = p_seq (n - 1) t then 1 else 0) := by
    have h_n : n = n - 1 + 1 := by omega
    have h_seq := congr_fun (hp_seq (n - 1) t) (p_seq n t)
    rw [← h_n] at h_seq
    exact h_seq
  have h_mono_prev := p_seq_mono_ge (n - 1) (a (n - 1)) t ht
  have h_lt_prev : p_seq n t < p_seq (n - 1) t := by omega
  have h_ne_prev : p_seq n t ≠ p_seq (n - 1) t := by omega
  rw [if_neg h_ne_prev] at hp_seq_val
  have h_lt_n1 : p_seq n t < n - 1 := by
    have h_lt_prev_n1 := p_seq_lt_n (n - 1) hn_prev (a (n - 1)) (by omega)
    omega
  have h_val_n1 : S_func (n - 1) t (p_seq n t) = 1 := by
    rw [h_stable]
    dsimp
    rw [if_pos h_lt_n1]
  rw [h_val_n1] at hp_seq_val
  have h_odd : S_func n t (p_seq n t) % 2 = 1 := by
    rw [hp_seq_val]
  rw [h_trans]
  have h_not_even : ¬(S_func n t (p_seq n t) % 2 = 0) := by omega
  rw [if_neg h_not_even]


lemma p_minus_q_ge (n : ℕ) (q p : ℕ) (hp : p = p_seq (n - 1) (a (n - 1)))
  (h_prev : p = n - 2 ∨ p = n - 3) (h_lt : q + 1 < p) :
  n - 1 - p ≤ p - q := by
  rcases h_prev with rfl | rfl
  · omega
  · omega

lemma p_seq_induction (n : ℕ) (hn : 4 ≤ n) (q p : ℕ) (hq : q = p_seq n (a (n - 1))) (hp : p = p_seq (n - 1) (a (n - 1)))
  (h_lt : q + 1 < p) (i : ℕ) (hi : i ≤ p - q) :
  p_seq n (a (n - 1) + i) = q + i := by
  induction' i with i ih
  · rw [Nat.add_zero, Nat.add_zero]
    exact hq.symm
  · have hi_le : i < p - q := by omega
    have hi_le2 : i ≤ p - q := by omega
    have ih_val := ih hi_le2
    have h_step : a (n - 1) + (i + 1) = (a (n - 1) + i) + 1 := by omega
    rw [h_step]
    have h_lt_p : p_seq n (a (n - 1) + i) < p := by
      rw [ih_val]
      omega
    have h_step_eq := p_seq_step_eq n hn (a (n - 1) + i) (by omega) (by rw [← hp]; exact h_lt_p)
    rw [h_step_eq, ih_val]
    omega


lemma p_seq_transition_bound (n : ℕ) (hn : 4 ≤ n)
  (h_prev : p_seq (n - 1) (a (n - 1)) = n - 2 ∨ p_seq (n - 1) (a (n - 1)) = n - 3)
  (h_lt : p_seq n (a (n - 1)) + 1 < p_seq (n - 1) (a (n - 1))) :
  p_seq n (a n) < n - 2 := by
  let q := p_seq n (a (n - 1))
  let p := p_seq (n - 1) (a (n - 1))
  have h_minus_ge := p_minus_q_ge n q p rfl h_prev h_lt
  have h_ind := p_seq_induction n hn q p rfl rfl h_lt (n - 1 - p) h_minus_ge
  have h_eq_an : a n = a (n - 1) + (n - 1 - p) := by
    have h_eq_prev_a_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
    have h_n_sub_1_add_1 : n - 1 + 1 = n := by omega
    rw [← h_n_sub_1_add_1]
    exact h_eq_prev_a_raw
  rw [h_eq_an]
  rw [h_ind]
  omega

lemma p_seq_ge_n_sub_two_from_n_sub_three_helper (n : ℕ) (hn : 4 ≤ n)
  (h_ge : p_seq n (a n - 1) ≥ n - 3) : p_seq n (a n) ≥ n - 2 := by
  have hn1 : 1 ≤ n := by omega
  by_cases h_cases : p_seq n (a n - 1) < n - 1
  · have h_lt := p_seq_lt_n n hn1 (a n - 1) (by omega)
    rcases eq_or_lt_of_le h_ge with heq | hgt
    · -- p_seq n (a n - 1) = n - 3
      have h_trans := p_seq_transition n (a n - 1)
      have h_eq : a n = (a n - 1) + 1 := by
        have h_an_pos : a n > 0 := a_pos n (by omega)
        omega
      rw [← h_eq] at h_trans
      rw [h_trans]
      have h_odd : S_func n (a n - 1) (n - 3) = 1 := by
        have h_exact := S_func_last_segment_exact n hn
        exact h_exact.1 (n - 3) (by omega)
      rw [heq] at h_odd
      rw [h_odd]
      dsimp
      omega
    · -- p_seq n (a n - 1) > n - 3, so >= n - 2
      have h_mono := p_seq_mono n (a n - 1)
      have h_eq : a n = (a n - 1) + 1 := by
        have h_an_pos : a n > 0 := a_pos n (by omega)
        omega
      rw [← h_eq] at h_mono
      omega
  · have h_ge : p_seq n (a n - 1) ≥ n - 1 := by omega
    have h_mono := p_seq_mono n (a n - 1)
    have h_eq : a n = (a n - 1) + 1 := by
      have h_an_pos : a n > 0 := a_pos n (by omega)
      omega
    rw [← h_eq] at h_mono
    omega


lemma p_seq_transition_eq_of_n_sub_four (n : ℕ) (hn : 4 ≤ n)
  (h_prev : p_seq (n - 1) (a (n - 1)) = n - 3)
  (h_eq : p_seq n (a (n - 1)) = n - 4) :
  p_seq n (a (n - 1) + 1) = n - 3 := by
  have hn_prev : 1 ≤ n - 1 := by omega
  have h_trans := p_seq_transition n (a (n - 1))
  have hp_seq_val : S_func n (a (n - 1)) (n - 4) = S_func (n - 1) (a (n - 1)) (n - 4) + (if n - 4 = p_seq (n - 1) (a (n - 1)) then 1 else 0) := by
    have h_n : n = n - 1 + 1 := by omega
    have h_seq := hp_seq (n - 1) (a (n - 1))
    rw [← h_n] at h_seq
    exact congr_fun h_seq (n - 4)
  have h_ne_prev : n - 4 ≠ p_seq (n - 1) (a (n - 1)) := by
    rw [h_prev]
    omega
  rw [if_neg h_ne_prev] at hp_seq_val
  have h_stable := S_func_stable_ge (n - 1) hn_prev 0
  rw [Nat.add_zero] at h_stable
  have h_val_n1 : S_func (n - 1) (a (n - 1)) (n - 4) = 1 := by
    rw [h_stable]
    dsimp
    rw [if_pos (by omega)]
  rw [h_val_n1] at hp_seq_val
  have h_odd : S_func n (a (n - 1)) (n - 4) % 2 = 1 := by
    rw [hp_seq_val]
  rw [h_eq] at h_trans
  rw [h_odd] at h_trans
  have h_ne : ¬(1 = 0) := by decide
  rw [if_neg h_ne] at h_trans
  omega


lemma S_func_np1_zero_at_t_plus_two (n : ℕ) (hn : 3 ≤ n) (p : ℕ) (hp : p ≤ n - 3) (t : ℕ)
  (h_stable : S_func n t = fun j => if j < n then 1 else 0)
  (hp_eq : S_func (n + 1) t = fun j => S_func n t j + (if j = p then 1 else 0)) :
  S_func (n + 1) (t + 2) n = 0 := by
  have hp_eq_rewritten : S_func (n + 1) t = fun j => (if j < n then 1 else 0) + (if j = p then 1 else 0) := by
    rw [hp_eq, h_stable]
  have h_func_2 := S_func_stable_ind n t h_stable p hp_eq_rewritten (by omega) 2
  have h_n := congr_fun h_func_2 n
  rw [h_n]
  have h_cond : p + 2 < n := by omega
  rw [if_pos h_cond]
  split_ifs <;> omega


lemma S_func_step_two_n_sub_one (n : ℕ) (hn : 5 ≤ n) (p : ℕ) (hp : p = n - 2 ∨ p = n - 3)
  (h_stable : S_func (n - 1) (a (n - 1)) = fun j => if j < n - 1 then 1 else 0)
  (hp_eq : S_func n (a (n - 1)) = fun j => S_func (n - 1) (a (n - 1)) j + (if j = p then 1 else 0)) :
  S_func n (a (n - 1) + 2) (n - 1) = 1 := by
  have h1 : S_func n (a (n - 1) + 1) = config_step (S_func n (a (n - 1))) := rfl
  have h2 : S_func n (a (n - 1) + 2) = config_step (S_func n (a (n - 1) + 1)) := by
    have : a (n - 1) + 2 = a (n - 1) + 1 + 1 := by omega
    rw [this]
    rfl
  rw [h2]
  unfold config_step
  have h_cond : n - 1 ≠ 0 := by omega
  rw [if_neg h_cond]
  rw [h1]
  have h_step1_n1 : config_step (S_func n (a (n - 1))) (n - 1) = if p = n - 2 then 1 else 0 := by
    unfold config_step
    rw [if_neg h_cond]
    have h_n1 : S_func n (a (n - 1)) (n - 1) = 0 := by
      rw [hp_eq, h_stable]
      dsimp
      have h_lt1 : ¬(n - 1 < n - 1) := by omega
      rw [if_neg h_lt1]
      rcases hp with rfl | rfl <;> (split_ifs <;> omega)
    have h_n2 : S_func n (a (n - 1)) (n - 2) = if p = n - 2 then 2 else 1 := by
      rw [hp_eq, h_stable]
      dsimp
      have h_lt2 : n - 2 < n - 1 := by omega
      rw [if_pos h_lt2]
      rcases hp with rfl | rfl <;> (split_ifs <;> omega)
    have h_sub_eq : n - 1 - 1 = n - 2 := by omega
    rw [h_sub_eq]
    rcases hp with rfl | rfl
    · rw [h_n1, h_n2]
      split_ifs <;> omega
    · rw [h_n1, h_n2]
      split_ifs <;> omega
  have h_step1_n2 : config_step (S_func n (a (n - 1))) (n - 2) = if p = n - 3 then 2 else 1 := by
    unfold config_step
    have h_cond2 : n - 2 ≠ 0 := by omega
    rw [if_neg h_cond2]
    have h_n2 : S_func n (a (n - 1)) (n - 2) = if p = n - 2 then 2 else 1 := by
      rw [hp_eq, h_stable]
      dsimp
      have h_lt2 : n - 2 < n - 1 := by omega
      rw [if_pos h_lt2]
      rcases hp with rfl | rfl <;> (split_ifs <;> omega)
    have h_n3 : S_func n (a (n - 1)) (n - 3) = if p = n - 3 then 2 else 1 := by
      rw [hp_eq, h_stable]
      dsimp
      have h_lt3 : n - 3 < n - 1 := by omega
      rw [if_pos h_lt3]
      rcases hp with rfl | rfl <;> (split_ifs <;> omega)
    have h_sub_eq2 : n - 2 - 1 = n - 3 := by omega
    rw [h_sub_eq2]
    rcases hp with rfl | rfl
    · rw [h_n2, h_n3]
      split_ifs <;> omega
    · rw [h_n2, h_n3]
      split_ifs <;> omega
  have h_sub_eq3 : n - 1 - 1 = n - 2 := by omega
  rw [h_sub_eq3]
  rw [h_step1_n1, h_step1_n2]
  rcases hp with rfl | rfl
  · split_ifs <;> omega
  · split_ifs <;> omega

lemma main_induction (n : ℕ) (hn : 4 ≤ n) :
  (p_seq n (a n - 1) ≥ n - 3) ∧ (p_seq n (a n) ≥ n - 2) ∧
  (n ≥ 5 → p_seq n (a (n - 1)) + 1 ≥ p_seq (n - 1) (a (n - 1))) := by
  induction' n using Nat.strong_induction_on with n ih
  have h_cases : n = 4 ∨ n > 4 := by omega
  rcases h_cases with rfl | hn_gt
  · constructor
    · have h0 : p_seq 4 0 = 0 := p_seq_zero 4
      have h1 : p_seq 4 1 = 0 := by
        rw [p_seq_transition 4 0, h0]
        have h_val : S_func 4 0 0 = 4 := rfl
        rw [h_val]
        rfl
      have h2 : p_seq 4 2 = 0 := by
        rw [p_seq_transition 4 1, h1]
        have h_val : S_func 4 1 0 = 2 := rfl
        rw [h_val]
        rfl
      have h3 : p_seq 4 3 = 1 := by
        rw [p_seq_transition 4 2, h2]
        have h_val : S_func 4 2 0 = 1 := rfl
        rw [h_val]
        rfl
      have h_a4 : a 4 = 4 := a_four_four
      rw [h_a4, h3]
    · constructor
      · have h0 : p_seq 4 0 = 0 := p_seq_zero 4
        have h1 : p_seq 4 1 = 0 := by
          rw [p_seq_transition 4 0, h0]
          have h_val : S_func 4 0 0 = 4 := rfl
          rw [h_val]
          rfl
        have h2 : p_seq 4 2 = 0 := by
          rw [p_seq_transition 4 1, h1]
          have h_val : S_func 4 1 0 = 2 := rfl
          rw [h_val]
          rfl
        have h3 : p_seq 4 3 = 1 := by
          rw [p_seq_transition 4 2, h2]
          have h_val : S_func 4 2 0 = 1 := rfl
          rw [h_val]
          rfl
        have h4 : p_seq 4 4 = 2 := by
          rw [p_seq_transition 4 3, h3]
          have h_val : S_func 4 3 1 = 1 := rfl
          rw [h_val]
          rfl
        have h_a4 : a 4 = 4 := a_four_four
        rw [h_a4, h4]
      · intro h_contra
        omega
  · have hn_prev : 4 ≤ n - 1 := by omega
    have ih_val := ih (n - 1) (by omega) hn_prev
    have h_ge_prev_3 := ih_val.1
    have h_ge_prev := ih_val.2.1
    have hn1_prev : 1 ≤ n - 1 := by omega
    have h_eq_prev_a_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
    have h_n_sub_1_add_1 : n - 1 + 1 = n := by omega
    have h_eq_prev_a : a n = a (n - 1) + ((n - 1) - p_seq (n - 1) (a (n - 1))) := by
      rw [← h_n_sub_1_add_1]
      exact h_eq_prev_a_raw
    have h_lt_prev_a := p_seq_lt_n (n - 1) (by omega) (a (n - 1)) (by omega)
    have h_fd_prev : a n = a (n - 1) + 1 ∨ a n = a (n - 1) + 2 := by
      rcases eq_or_lt_of_le h_ge_prev with heq_prev | hgt_prev
      · have : (n - 1) - p_seq (n - 1) (a (n - 1)) = 2 := by omega
        rw [this] at h_eq_prev_a
        right
        exact h_eq_prev_a
      · have : p_seq (n - 1) (a (n - 1)) = n - 2 := by omega
        have : (n - 1) - p_seq (n - 1) (a (n - 1)) = 1 := by omega
        rw [this] at h_eq_prev_a
        left
        exact h_eq_prev_a


lemma p_seq_le_n (n : ℕ) (t : ℕ) : p_seq n t ≤ n := by
  by_contra! h_gt
  have hp_eq := hp_seq n t
  have h_is := S_func_initial_segment (n + 1) t
  have h_spec := h_is n (p_seq n t) h_gt
  have h_pos : S_func (n + 1) t (p_seq n t) > 0 := by
    rw [hp_eq]
    dsimp
    omega
  have h_zero : S_func (n + 1) t n = 0 := by
    rw [hp_eq]
    dsimp
    have : n ≠ p_seq n t := by omega
    rw [if_neg this]
    exact S_func_at_n_zero n t
  have h_congr := h_spec h_pos
  omega

lemma p_seq_lt_n_of_lt_anp1 (n : ℕ) (hn : 4 ≤ n) (t : ℕ) (ht : t < a (n + 1)) : p_seq n t < n := by
  have h_zero : S_func (n + 1) t n = 0 := S_func_last_zero (n + 1) (by omega) t ht
  have h_seq := congr_fun (hp_seq n t) n
  have h_n_zero := S_func_at_n_zero n t
  rw [h_zero, h_n_zero] at h_seq
  dsimp at h_seq
  have h_le := p_seq_le_n n t
  by_contra! h_ge
  have h_eq : n = p_seq n t := by omega
  rw [if_pos h_eq] at h_seq
  omega

    have h_ge_prev_at_stable : p_seq n (a (n - 1)) + 1 ≥ p_seq (n - 1) (a (n - 1)) := by
      have h_prev_or : p_seq (n - 1) (a (n - 1)) = n - 2 ∨ p_seq (n - 1) (a (n - 1)) = n - 3 := by
        have h_lt_prev := p_seq_lt_n (n - 1) (by omega) (a (n - 1)) (by omega)
        omega
      rcases h_prev_or with h_cases | h_cases
      · by_contra! h_lt
        let q := p_seq n (a (n - 1))
        let p := p_seq (n - 1) (a (n - 1))
        have h_qp : q + 1 < p := by omega
        have h_eq_an : a n = a (n - 1) + 1 := by
          have h_eq_prev_a_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_n_sub_1_add_1 : n - 1 + 1 = n := by omega
          rw [← h_n_sub_1_add_1]
          rw [h_cases] at h_eq_prev_a_raw
          have : n - 1 - (n - 2) = 1 := by omega
          rw [this] at h_eq_prev_a_raw
          exact h_eq_prev_a_raw
        have hn_pos : 1 ≤ n := by omega
        have h_stable_at_an : S_func n (a n) (n - 1) = 1 := by
          have h_stable := S_func_stable_ge n hn_pos 0
          have h_val := congr_fun h_stable (n - 1)
          rw [Nat.add_zero] at h_val
          rw [h_val]
          have : n - 1 < n := by omega
          rw [if_pos this]
        have h_p_seq_an : p_seq n (a n) = q + 1 := by
          have h_ind := p_seq_induction n hn q p rfl rfl h_qp 1 (by omega)
          rw [h_eq_an]
          exact h_ind
        have h_func_np1_an : S_func (n + 1) (a n) (n - 1) = 1 := by
          have hp_eq_an := hp_seq n (a n)
          have h_val := congr_fun hp_eq_an (n - 1)
          rw [h_p_seq_an] at h_val
          have h_ne : n - 1 ≠ q + 1 := by omega
          rw [if_neg h_ne] at h_val
          rw [h_stable_at_an] at h_val
          exact h_val
        have h_func_np1_an_step : S_func (n + 1) (a n) (n - 1) = config_step (S_func (n + 1) (a (n - 1))) (n - 1) := by
          rw [h_eq_an]
          rfl
        have h_stable_n1 : S_func (n - 1) (a (n - 1)) = fun j => if j < n - 1 then 1 else 0 := S_func_stable_ge (n - 1) (by omega) 0
        have hp_eq_n1 : S_func n (a (n - 1)) = fun j => S_func (n - 1) (a (n - 1)) j + (if j = p_seq (n - 1) (a (n - 1)) then 1 else 0) := by
          have h_n : n - 1 + 1 = n := by omega
          have h_seq := hp_seq (n - 1) (a (n - 1))
          rw [h_n] at h_seq
          exact h_seq
        have h_val_n1 : S_func (n + 1) (a (n - 1)) (n - 1) = 0 := by
          have hp_eq_n := hp_seq n (a (n - 1))
          have h_val := congr_fun hp_eq_n (n - 1)
          have h_ne : n - 1 ≠ q := by omega
          rw [if_neg h_ne] at h_val
          have h_val2 := congr_fun hp_eq_n1 (n - 1)
          have h_ne2 : n - 1 ≠ p := by omega
          rw [if_neg h_ne2] at h_val2
          rw [h_stable_n1] at h_val2
          dsimp at h_val2
          have : ¬(n - 1 < n - 1) := by omega
          rw [if_neg this] at h_val2
          rw [h_val2] at h_val
          exact h_val
        have h_val_n2 : S_func (n + 1) (a (n - 1)) (n - 2) = 2 := by
          have hp_eq_n := hp_seq n (a (n - 1))
          have h_val := congr_fun hp_eq_n (n - 2)
          have h_ne : n - 2 ≠ q := by omega
          rw [if_neg h_ne] at h_val
          have h_val2 := congr_fun hp_eq_n1 (n - 2)
          have h_eq2 : n - 2 = p := by omega
          rw [if_pos h_eq2] at h_val2
          rw [h_stable_n1] at h_val2
          dsimp at h_val2
          have : n - 2 < n - 1 := by omega
          rw [if_pos this] at h_val2
          rw [h_val2] at h_val
          exact h_val
        have h_eq_anp1 : a (n + 1) = a (n - 1) + p - q + 2 := by
          have h_eq1 := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_eq2 := a_eq_a_n_add_n_sub_p n (by omega)
          rw [h_p_seq_an] at h_eq2
          omega
        have h_stable_np1 : S_func (n + 1) (a (n + 1)) n = 1 := by
          have h_stable := S_func_stable_ge (n + 1) (by omega) 0
          have h_val := congr_fun h_stable n
          have h_eq : a (n + 1) + 0 = a (n + 1) := by omega
          rw [h_eq] at h_val
          rw [h_val]
          have : n < n + 1 := by omega
          rw [if_pos this]
        have h_func_step : S_func (n + 1) (a (n + 1)) n = config_step (S_func (n + 1) (a (n + 1) - 1)) n := by
          have h_eq : a (n + 1) = (a (n + 1) - 1) + 1 := by omega
          rw [h_eq]
          rfl
        have h_an_sub1_eq : a (n + 1) - 1 = a (n - 1) + p - q + 1 := by omega
        have h_p_seq_induction1 : p_seq n (a (n - 1) + p - q) = p := by
          have h_ind := p_seq_induction n hn q p rfl rfl h_qp (p - q) (by omega)
          have h_eq1 : a (n - 1) + (p - q) = a (n - 1) + p - q := by omega
          have h_eq2 : q + (p - q) = p := by omega
          rw [h_eq1] at h_ind
          rw [h_eq2] at h_ind
          exact h_ind
        have h_p_seq_t : p_seq n (a (n - 1) + p - q + 1) = n - 1 := by
          have h_trans := p_seq_transition n (a (n - 1) + p - q)
          have h_t0_stable : S_func n (a (n - 1) + p - q) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q - a n)
            have h_add : a n + (a (n - 1) + p - q - a n) = a (n - 1) + p - q := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_t0 : S_func n (a (n - 1) + p - q) (p_seq n (a (n - 1) + p - q)) = 1 := by
            rw [h_p_seq_induction1]
            rw [h_t0_stable]
            dsimp
            have : p < n := by omega
            rw [if_pos this]
          rw [h_val_t0] at h_trans
          have h_not_even : ¬(1 % 2 = 0) := by decide
          rw [if_neg h_not_even] at h_trans
          rw [h_p_seq_induction1] at h_trans
          have h_p_plus_1 : p + 1 = n - 1 := by omega
          rw [h_p_plus_1] at h_trans
          exact h_trans
        have h_val_np1_sub1_n : S_func (n + 1) (a (n + 1) - 1) n = 0 := by
          rw [h_an_sub1_eq]
          have h_seq := congr_fun (hp_seq n (a (n - 1) + p - q + 1)) n
          rw [h_seq]
          have h_stable : S_func n (a (n - 1) + p - q + 1) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q + 1 ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q + 1 - a n)
            have h_add : a n + (a (n - 1) + p - q + 1 - a n) = a (n - 1) + p - q + 1 := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_n : S_func n (a (n - 1) + p - q + 1) n = 0 := by
            rw [h_stable]
            dsimp
            have : ¬(n < n) := by omega
            rw [if_neg this]
          rw [h_val_n]
          rw [h_p_seq_t]
          have h_ne : n ≠ n - 1 := by omega
          rw [if_neg h_ne]
        have h_val_np1_sub1_n1 : S_func (n + 1) (a (n + 1) - 1) (n - 1) = 2 := by
          rw [h_an_sub1_eq]
          have h_seq := congr_fun (hp_seq n (a (n - 1) + p - q + 1)) (n - 1)
          rw [h_seq]
          have h_stable : S_func n (a (n - 1) + p - q + 1) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q + 1 ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q + 1 - a n)
            have h_add : a n + (a (n - 1) + p - q + 1 - a n) = a (n - 1) + p - q + 1 := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_n1 : S_func n (a (n - 1) + p - q + 1) (n - 1) = 1 := by
            rw [h_stable]
            dsimp
            have : n - 1 < n := by omega
            rw [if_pos this]
          rw [h_val_n1]
          rw [h_p_seq_t]
          have h_eq : n - 1 = n - 1 := rfl
          rw [if_pos h_eq]
        have h_trans2 := p_seq_transition n (a (n - 1) + p - q + 1)
        have h_stable2 : S_func n (a (n - 1) + p - q + 1) = fun j => if j < n then 1 else 0 := by
          have h_ge : a (n - 1) + p - q + 1 ≥ a n := by
            have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
            omega
          have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q + 1 - a n)
          have h_add : a n + (a (n - 1) + p - q + 1 - a n) = a (n - 1) + p - q + 1 := by omega
          rw [h_add] at h_stable
          exact h_stable
        have h_val_n2 : S_func n (a (n - 1) + p - q + 1) (n - 1) = 1 := by
          rw [h_stable2]
          dsimp
          have : n - 1 < n := by omega
          rw [if_pos this]
        rw [h_p_seq_t, h_val_n2] at h_trans2
        have h_not_even : ¬(1 % 2 = 0) := by decide
        rw [if_neg h_not_even] at h_trans2
        have h_ge_an : a (n + 1) ≥ a n := by
          have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          omega
        have h_lt_anp1 : p_seq n (a (n + 1)) < n := by
          exact p_seq_lt_n n hn_pos (a (n + 1)) h_ge_an
        rw [← h_eq_anp1] at h_trans2
        omega
      · by_contra! h_lt
        let q := p_seq n (a (n - 1))
        let p := p_seq (n - 1) (a (n - 1))
        have h_qp : q + 1 < p := by omega
        have h_eq_an : a n = a (n - 1) + 2 := by
          have h_eq_prev_a_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_n_sub_1_add_1 : n - 1 + 1 = n := by omega
          rw [← h_n_sub_1_add_1]
          rw [h_cases] at h_eq_prev_a_raw
          have : n - 1 - (n - 3) = 2 := by omega
          rw [this] at h_eq_prev_a_raw
          exact h_eq_prev_a_raw
        have hn_pos : 1 ≤ n := by omega
        have h_p_seq_induction1 : p_seq n (a (n - 1) + p - q) = p := by
          have h_ind := p_seq_induction n hn q p rfl rfl h_qp (p - q) (by omega)
          have h_eq1 : a (n - 1) + (p - q) = a (n - 1) + p - q := by omega
          have h_eq2 : q + (p - q) = p := by omega
          rw [h_eq1] at h_ind
          rw [h_eq2] at h_ind
          exact h_ind
        have h_p_seq_t1 : p_seq n (a (n - 1) + p - q + 1) = n - 2 := by
          have h_trans := p_seq_transition n (a (n - 1) + p - q)
          have h_t0_stable : S_func n (a (n - 1) + p - q) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q - a n)
            have h_add : a n + (a (n - 1) + p - q - a n) = a (n - 1) + p - q := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_t0 : S_func n (a (n - 1) + p - q) (p_seq n (a (n - 1) + p - q)) = 1 := by
            rw [h_p_seq_induction1]
            rw [h_t0_stable]
            dsimp
            have : p < n := by omega
            rw [if_pos this]
          rw [h_val_t0] at h_trans
          have h_not_even : ¬(1 % 2 = 0) := by decide
          rw [if_neg h_not_even] at h_trans
          rw [h_p_seq_induction1] at h_trans
          have h_p_plus_1 : p + 1 = n - 2 := by omega
          rw [h_p_plus_1] at h_trans
          exact h_trans
        have h_p_seq_t2 : p_seq n (a (n - 1) + p - q + 2) = n - 1 := by
          have h_trans := p_seq_transition n (a (n - 1) + p - q + 1)
          have h_t1_stable : S_func n (a (n - 1) + p - q + 1) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q + 1 ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q + 1 - a n)
            have h_add : a n + (a (n - 1) + p - q + 1 - a n) = a (n - 1) + p - q + 1 := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_t1 : S_func n (a (n - 1) + p - q + 1) (p_seq n (a (n - 1) + p - q + 1)) = 1 := by
            rw [h_p_seq_t1]
            rw [h_t1_stable]
            dsimp
            have : n - 2 < n := by omega
            rw [if_pos this]
          rw [h_val_t1] at h_trans
          have h_not_even : ¬(1 % 2 = 0) := by decide
          rw [if_neg h_not_even] at h_trans
          rw [h_p_seq_t1] at h_trans
          have h_n_sub_2_plus_1 : n - 2 + 1 = n - 1 := by omega
          rw [h_n_sub_2_plus_1] at h_trans
          exact h_trans
        have h_p_seq_t3 : p_seq n (a (n - 1) + p - q + 3) = n := by
          have h_trans := p_seq_transition n (a (n - 1) + p - q + 2)
          have h_t2_stable : S_func n (a (n - 1) + p - q + 2) = fun j => if j < n then 1 else 0 := by
            have h_ge : a (n - 1) + p - q + 2 ≥ a n := by
              have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
              omega
            have h_stable := S_func_stable_ge n hn_pos (a (n - 1) + p - q + 2 - a n)
            have h_add : a n + (a (n - 1) + p - q + 2 - a n) = a (n - 1) + p - q + 2 := by omega
            rw [h_add] at h_stable
            exact h_stable
          have h_val_t2 : S_func n (a (n - 1) + p - q + 2) (p_seq n (a (n - 1) + p - q + 2)) = 1 := by
            rw [h_p_seq_t2]
            rw [h_t2_stable]
            dsimp
            have : n - 1 < n := by omega
            rw [if_pos this]
          rw [h_val_t2] at h_trans
          have h_not_even : ¬(1 % 2 = 0) := by decide
          rw [if_neg h_not_even] at h_trans
          rw [h_p_seq_t2] at h_trans
          have h_n_sub_1_plus_1 : n - 1 + 1 = n := by omega
          rw [h_n_sub_1_plus_1] at h_trans
          exact h_trans
        have h_eq_anp1 : a (n + 1) = a (n - 1) + p - q + 3 := by
          have h_eq1 := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_eq2 := a_eq_a_n_add_n_sub_p n (by omega)
          have h_p_seq_an : p_seq n (a n) = q + 2 := by
            have h_ind := p_seq_induction n hn q p rfl rfl h_qp 2 (by omega)
            exact h_ind
          rw [h_p_seq_an] at h_eq2
          omega
        have h_lt_anp1 : p_seq n (a (n + 1)) < n := by
          have h_ge_an : a (n + 1) ≥ a n := by
            have h_eq_an_raw := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
            omega
          exact p_seq_lt_n n hn_pos (a (n + 1)) h_ge_an
        rw [h_eq_anp1] at h_lt_anp1
        rw [h_p_seq_t3] at h_lt_anp1
        omega

    have h_ge_n_sub_3 : p_seq n (a n - 1) ≥ n - 3 := by
      rcases h_fd_prev with h_case1 | h_case2
      · have h_prev_val : p_seq (n - 1) (a (n - 1)) = n - 2 := by
          have h_eq_prev := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_lt_prev := p_seq_lt_n (n - 1) (by omega) (a (n - 1)) (by omega)
          omega
        have h_prop : p_seq n (a (n - 1)) ≥ n - 3 ∨ ¬(p_seq n (a (n - 1)) ≥ n - 3) := Classical.em _
        have h_or : p_seq n (a (n - 1)) ≥ n - 3 ∨ p_seq n (a (n - 1)) < n - 3 := by omega
        have h_an_sub : a n - 1 = a (n - 1) := by omega
        rcases h_or with h_ge | h_lt
        · rw [h_an_sub]
          exact h_ge
        · exfalso
          have h_lt_transition : p_seq n (a (n - 1)) + 1 < p_seq (n - 1) (a (n - 1)) := by omega
          have h_bound : p_seq n (a n) < n - 2 := p_seq_transition_bound n hn (Or.inl h_prev_val) h_lt_transition
          have h_ge_prev_stable := h_ge_prev_at_stable
          rw [h_prev_val] at h_ge_prev_stable
          rw [h_prev_val] at h_lt_transition
          omega
      · have h_prev_val : p_seq (n - 1) (a (n - 1)) = n - 3 := by
          have h_eq_prev := a_eq_a_n_add_n_sub_p (n - 1) (by omega)
          have h_lt_prev := p_seq_lt_n (n - 1) (by omega) (a (n - 1)) (by omega)
          omega
        have h_an_eq : a n - 1 = a (n - 1) + 1 := by omega
        have h_or : p_seq n (a (n - 1)) ≥ n - 3 ∨ p_seq n (a (n - 1)) = n - 4 ∨ p_seq n (a (n - 1)) < n - 4 := by omega
        rcases h_or with h_ge | h_eq | h_lt
        · have h_mono : p_seq n (a n - 1) ≥ p_seq n (a (n - 1)) := by
            rw [h_an_eq]
            exact p_seq_mono n (a (n - 1))
          exact (by omega)
        · have h_trans := p_seq_transition_eq_of_n_sub_four n hn h_prev_val h_eq
          rw [h_an_eq]
          omega
        · exfalso
          have h_lt_transition : p_seq n (a (n - 1)) + 1 < p_seq (n - 1) (a (n - 1)) := by omega
          have h_bound : p_seq n (a n) < n - 2 := p_seq_transition_bound n hn (Or.inr h_prev_val) h_lt_transition
          have h_ge_prev_stable := h_ge_prev_at_stable
          rw [h_prev_val] at h_ge_prev_stable
          rw [h_prev_val] at h_lt_transition
          omega
    constructor
    · exact h_ge_n_sub_3
    · constructor
      · exact p_seq_ge_n_sub_two_from_n_sub_three_helper n hn h_ge_n_sub_3
      · intro _
        exact h_ge_prev_at_stable


lemma p_seq_ge_prev_at_stable (n : ℕ) (hn : 5 ≤ n) : p_seq n (a (n - 1)) + 1 ≥ p_seq (n - 1) (a (n - 1)) :=
  (main_induction n (by omega)).2.2 hn

lemma p_seq_ge_n_sub_three (n : ℕ) (hn : 4 ≤ n) : p_seq n (a n - 1) ≥ n - 3 :=
  (main_induction n hn).1

lemma p_seq_ge_n_sub_two_from_n_sub_three (n : ℕ) (hn : 4 ≤ n) : p_seq n (a n) ≥ n - 2 :=
  (main_induction n hn).2.1

theorem oeis_a300997_finite_difference_is_one_or_two (n : ℕ) (hn : 1 ≤ n) : a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  rcases eq_or_lt_of_le hn with rfl | hn_ge
  · rw [a_one_zero, a_two_one]
    omega
  · have hn2 : 2 ≤ n := by omega
    rcases eq_or_lt_of_le hn2 with rfl | hn_ge2
    · rw [a_two_one, a_three_three]
      omega
    · have hn3 : 3 ≤ n := by omega
      rcases eq_or_lt_of_le hn3 with rfl | hn_ge3
      · rw [a_three_three, a_four_four]
        omega
      · have hn4 : 4 ≤ n := hn_ge3
        have h_eq := a_eq_a_n_add_n_sub_p n (by omega)
        have h_ge := p_seq_ge_n_sub_two_from_n_sub_three n hn4
        have h_lt := p_seq_lt_n n (by omega) (a n) (by omega)
        omega


#print axioms oeis_a300997_finite_difference_is_one_or_two
