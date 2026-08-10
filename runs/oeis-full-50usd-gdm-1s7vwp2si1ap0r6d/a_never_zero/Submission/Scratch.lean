import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

open List Finset

-- Let's import the definition of a from Spec.lean
-- Actually, let's just copy the definition of a to Scratch.lean so we don't have to import it and cause cycle.

noncomputable def a' : ℕ → ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf (fun n IH =>
    if h0 : n = 0 then 1
    else
      let target : ℕ := n
      let a_prev (k : ℕ) (hk : k < n) : ℕ := IH k hk
      let prefix_list : List ℕ := List.ofFn (fun k : Fin n => a_prev k.val k.is_lt)
      let max_contiguous_length : ℕ :=
        Finset.sup (Finset.range n) fun i =>
          Finset.sup (Finset.range n) fun j =>
            if h : i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                sublist.countP (· ≠ 0)
              else 0
            else 0
      max_contiguous_length
  )

theorem a'_eq (m : ℕ) : a' m = if h0 : m = 0 then 1 else
      let target : ℕ := m
      let prefix_list : List ℕ := List.ofFn (fun k : Fin m => a' k.val)
      let max_contiguous_length : ℕ :=
        Finset.sup (Finset.range m) fun i =>
          Finset.sup (Finset.range m) fun j =>
            if h : i ≤ j then
              let sublist_len := j - i + 1
              let sublist := prefix_list.drop i |>.take sublist_len
              if sublist.sum = target then
                sublist.countP (· ≠ 0)
              else 0
            else 0
      max_contiguous_length := by
  rw [a']
  rw [WellFounded.fix_eq]


#check Finset.le_sup

#check List.take_add

theorem a'_never_zero (n : ℕ) : a' n ≠ 0 := by
  induction' n using Nat.strong_induction_on with n IH
  by_cases h0 : n = 0
  · subst h0
    rw [a']
    rw [WellFounded.fix_eq]
    simp
  · rw [a']
    rw [WellFounded.fix_eq]
    rw [dif_neg h0]
    by_contra! h_zero
    simp at h_zero
    have h_pos : ∀ x ∈ List.ofFn (fun k : Fin n => a' k.val), x > 0 := by
      intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨k, rfl⟩ := hx
      have hk : k.val < n := k.is_lt
      have h_nz := IH k.val hk
      omega
    have h_sum : ∀ x y, x ≤ y → x < n → y < n → ((List.ofFn (fun k : Fin n => a' k.val)).drop x |>.take (y - x + 1)).sum ≠ n := by
      intro x y hxy hx hy h_eq
      -- Unfold and simplify h_eq so it matches h_zero exactly
      unfold a' at h_eq
      simp at h_eq
      have h_zero_xy := h_zero x hx y hy hxy h_eq
      -- now h_zero_xy is: ∀ a ∈ sublist, a = 0
      -- Let's prove the sublist is non-empty
      set sublist := ((List.ofFn (fun k : Fin n => a' k.val)).drop x |>.take (y - x + 1)) with h_sub'
      have h_sub := h_sub'
      unfold a' at h_sub
      simp at h_sub
      have h_len : sublist.length = y - x + 1 := by
        rw [h_sub']
        rw [List.length_take]
        rw [List.length_drop]
        rw [List.length_ofFn]
        omega
      have h_len_pos : sublist.length > 0 := by
        rw [h_len]
        omega
      obtain ⟨z, hz⟩ : ∃ z, z ∈ sublist := by
        cases' h_sub_eq : sublist with z ts
        · -- nil case, sublist is []
          -- so sublist.length = 0
          have h_zero_len : sublist.length = 0 := by rw [h_sub_eq]; rfl
          omega
        · -- cons case, z :: ts
          exact ⟨z, by simp⟩
      have hz_in : z ∈ List.ofFn (fun k : Fin n => a' k.val) := by
        apply List.mem_of_mem_drop
        have hz' : z ∈ ((List.ofFn (fun k : Fin n => a' k.val)).drop x |>.take (y - x + 1)) := by
          rwa [← h_sub']
        exact List.mem_of_mem_take hz'
      rw [h_sub] at hz
      have hz_zero := h_zero_xy z hz
      have hz_gt_0 := h_pos z hz_in
      omega

    let S (m : ℕ) : ℕ := ((List.ofFn (fun k : Fin n => a' k.val)).take m).sum
    have S_zero : S 0 = 0 := by rfl
    have S_step (m : ℕ) (hm : m < n) : S (m + 1) = S m + a' m := by
      dsimp [S]
      have hm_len : m < (List.ofFn (fun k : Fin n => a' k.val)).length := by
        rw [List.length_ofFn]
        exact hm
      rw [List.sum_take_succ _ m hm_len]
      simp
    have S_sum (x y : ℕ) (hxy : x ≤ y) (hy : y < n) : S (y + 1) = S x + ((List.ofFn (fun k : Fin n => a' k.val)).drop x |>.take (y - x + 1)).sum := by
      dsimp [S]
      have h_eq_add : y + 1 = x + (y - x + 1) := by omega
      nth_rw 1 [h_eq_add]
      rw [List.take_add]
      rw [List.sum_append]
    have h_S_diff : ∀ x y, x ≤ y → x < n → y < n → S (y + 1) - S x ≠ n := by
      intro x y hxy hx hy h_eq
      have h_sum_xy := h_sum x y hxy hx hy
      have h_sum_val := S_sum x y hxy hy
      omega
    have h_no_pair : ∀ i j, i < j → j ≤ n → S j - S i ≠ n := by
      intro i j hij hj
      have hxy : i ≤ j - 1 := by omega
      have hy : j - 1 < n := by omega
      have hx : i < n := by omega
      have h_diff := h_S_diff i (j - 1) hxy hx hy
      have h_eq_j : j - 1 + 1 = j := by omega
      rw [h_eq_j] at h_diff
      exact h_diff
    have S_ge (m : ℕ) (hm : m ≤ n) : S m ≥ m := by
      induction m with
      | zero =>
        rw [S_zero]
      | succ m ih =>
        have hm_lt : m < n := by omega
        have h_step := S_step m hm_lt
        have h_am_nz := IH m hm_lt
        have h_am_ge : a' m ≥ 1 := by omega
        have h_ih := ih (by omega)
        omega

    have h_exists_S_ge : ∃ m, S m ≥ n := ⟨n, S_ge n (by omega)⟩
    let k := Nat.find h_exists_S_ge
    have hk_spec : S k ≥ n := Nat.find_spec h_exists_S_ge
    have hk_least : ∀ m < k, S m < n := by
      intro m hm
      have h_not := Nat.find_min h_exists_S_ge hm
      omega
    have hk_gt_zero : k > 0 := by
      by_contra! h_k
      have h_k_zero : k = 0 := by omega
      rw [h_k_zero] at hk_spec
      rw [S_zero] at hk_spec
      omega
    have hk_le_n : k ≤ n := by
      have h_n := Nat.find_min' h_exists_S_ge (S_ge n (by omega))
      exact h_n
    have hd3 : d ≥ 3 := by
      by_contra! hd_lt_3
      interval_cases d
      · omega
      · have : i_d = 0 := by omega
        exact hi_d_zero this
      · have hi1 : i_d = 1 := by omega
        have hj1 : j_d = 1 := by omega
        rw [hi1, hj1] at hd_sum_eq
        have h_sum_val : ((List.ofFn (fun k : Fin 2 => a' k.val)).drop 1 |>.take 1).sum = a' 1 := rfl
        rw [h_sum_val, a'_one] at hd_sum_eq
        omega
    sorry

theorem a'_zero : a' 0 = 1 := by
  rw [a'_eq 0]
  simp

theorem a'_one : a' 1 = 1 := by
  rw [a'_eq 1]
  simp [a'_zero]

theorem a'_two : a' 2 = 2 := by
  rw [a'_eq 2]
  simp [a'_zero, a'_one]
  decide

theorem a'_three : a' 3 = 2 := by
  rw [a'_eq 3]
  simp [a'_zero, a'_one, a'_two]
  decide

theorem a'_four : a' 4 = 3 := by
  rw [a'_eq 4]
  simp [a'_zero, a'_one, a'_two, a'_three]
  decide

theorem a'_five : a' 5 = 3 := by
  rw [a'_eq 5]
  simp [a'_zero, a'_one, a'_two, a'_three, a'_four]
  decide

