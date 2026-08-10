import FormalConjectures.Util.ProblemImports

open List Nat Function Filter Asymptotics

def a_aux (n : ℕ) (a_prev : ∀ m < n, ℕ) : ℕ :=
  if h : n < 2 then
    n
  else
    let history : List ℕ := List.ofFn (fun i : Fin n => a_prev i i.is_lt)
    have hn_one : n - 1 < n := by omega
    have hn_two : n - 2 < n := by omega
    let an_minus_1 : ℕ := a_prev (n - 1) hn_one
    let an_minus_2 : ℕ := a_prev (n - 2) hn_two
    let freq_nm1 := history.count an_minus_1
    let freq_nm2 := history.count an_minus_2
    freq_nm1 + freq_nm2

noncomputable def a (n : ℕ) : ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf a_aux n

theorem a_eq (n : ℕ) : a n = a_aux n (fun m _ => a m) := by
  rw [a]
  exact WellFounded.fix_eq Nat.lt_wfRel.wf a_aux n

theorem a_le_two_n (n : ℕ) : a n ≤ 2 * n := by
  induction' n using Nat.strong_induction_on with n ih
  rw [a_eq n]
  unfold a_aux
  split_ifs with h
  · omega
  · dsimp only
    have h1 : (List.ofFn (fun i : Fin n => a i)).count (a (n - 1)) ≤ n := by
      have hle := List.count_le_length (l := List.ofFn (fun i : Fin n => a i)) (a := a (n - 1))
      rw [List.length_ofFn] at hle
      exact hle
    have h2 : (List.ofFn (fun i : Fin n => a i)).count (a (n - 2)) ≤ n := by
      have hle := List.count_le_length (l := List.ofFn (fun i : Fin n => a i)) (a := a (n - 2))
      rw [List.length_ofFn] at hle
      exact hle
    omega

lemma history_succ (n : ℕ) : List.ofFn (fun i : Fin (n + 1) => a i) = (List.ofFn (fun i : Fin n => a i)) ++ [a n] := by
  ext i
  by_cases hi : i < n
  · rw [List.getElem?_append]
    split_ifs with h_cond
    · rw [List.getElem?_ofFn, List.getElem?_ofFn]
      have h1 : i < n := hi
      have h2 : i < n + 1 := by omega
      rw [dif_pos h1, dif_pos h2]
    · simp [List.length_ofFn] at h_cond
      omega
  · have hn_le : n ≤ i := by omega
    by_cases h_eq : i = n
    · rw [h_eq]
      have h1 : n < n + 1 := by omega
      have h_lhs : (List.ofFn (fun i : Fin (n + 1) => a i))[n]? = some (a n) := by
        rw [List.getElem?_ofFn]
        rw [dif_pos h1]
      have h_rhs : ((List.ofFn (fun i : Fin n => a i)) ++ [a n])[n]? = some (a n) := by
        rw [List.getElem?_append_right (by simp [List.length_ofFn])]
        simp [List.length_ofFn]
      rw [h_lhs, h_rhs]
    · have hn1_le : n + 1 ≤ i := by omega
      rw [List.getElem?_eq_none (by simp [List.length_ofFn]; omega)]
      rw [List.getElem?_eq_none (by simp [List.length_ofFn]; omega)]

noncomputable def a_count (x : ℕ) (n : ℕ) : ℕ := (List.ofFn (fun i : Fin n => a i)).count x

lemma a_count_succ (x n : ℕ) : a_count x (n + 1) = a_count x n + (if a n = x then 1 else 0) := by
  unfold a_count
  rw [history_succ n]
  rw [List.count_append]
  by_cases h : a n = x
  · rw [if_pos h]
    subst h
    simp [List.count]
  · rw [if_neg h]
    have : x ∉ [a n] := by
      simp
      exact Ne.symm h
    rw [List.count_eq_zero_of_not_mem this]

lemma count_add_count_le {α : Type*} [DecidableEq α] (u v : α) (huv : u ≠ v) (L : List α) :
  L.count u + L.count v ≤ L.length := by
  induction' L with x L ih
  · simp
  · simp only [List.count_cons, List.length_cons]
    split_ifs with hu hv
    · rw [beq_iff_eq] at hu hv
      subst hu; subst hv; exact (huv rfl).elim
    · omega
    · omega
    · omega

lemma a_formula (k : ℕ) (hk : 2 ≤ k) :
  a k = (List.ofFn (fun i : Fin k => a i)).count (a (k - 1)) + (List.ofFn (fun i : Fin k => a i)).count (a (k - 2)) := by
  rw [a_eq k]
  unfold a_aux
  have h_not : ¬ k < 2 := by omega
  rw [dif_neg h_not]

lemma a_zero : a 0 = 0 := by
  rw [a_eq 0]
  rfl

lemma a_one : a 1 = 1 := by
  rw [a_eq 1]
  rfl

def a_list : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let L := a_list n
    if n = 0 then [0]
    else if n = 1 then [0, 1]
    else
      let u := L.getD (n - 1) 0
      let v := L.getD (n - 2) 0
      L ++ [L.count u + L.count v]

lemma a_list_eq (n : ℕ) : a_list n = List.ofFn (fun i : Fin n => a i) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | (_ | (_ | n))
  · rfl
  · rw [history_succ 0]
    simp [a_zero]
    rfl
  · rw [history_succ 1]
    simp [a_zero, a_one]
    rfl
  · have h_ih1 := ih (n + 2) (by omega)
    unfold a_list
    rw [h_ih1]
    have h_not1 : n + 2 = 0 → False := by omega
    have h_not2 : n + 2 = 1 → False := by omega
    rw [if_neg h_not1, if_neg h_not2]
    change (List.ofFn (fun i : Fin (n + 2) => a i)) ++
      [List.count ((List.ofFn (fun i : Fin (n + 2) => a i)).getD (n + 1) 0) (List.ofFn (fun i : Fin (n + 2) => a i)) +
       List.count ((List.ofFn (fun i : Fin (n + 2) => a i)).getD n 0) (List.ofFn (fun i : Fin (n + 2) => a i))] =
      List.ofFn (fun i : Fin (n + 3) => a i)
    have h_len : (List.ofFn (fun i : Fin (n + 2) => a i)).length = n + 2 := by simp [List.length_ofFn]
    have h_get1 : (List.ofFn (fun i : Fin (n + 2) => a i)).getD (n + 1) 0 = a (n + 1) := by
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_ofFn]
      have : n + 1 < n + 2 := by omega
      rw [dif_pos this]
      rfl
    have h_get2 : (List.ofFn (fun i : Fin (n + 2) => a i)).getD n 0 = a n := by
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_ofFn]
      have : n < n + 2 := by omega
      rw [dif_pos this]
      rfl
    rw [h_get1, h_get2]
    have h_form := a_formula (n + 2) (by omega)
    have h_form' : a (n + 2) = (List.ofFn (fun i : Fin (n + 2) => a i)).count (a (n + 1)) + (List.ofFn (fun i : Fin (n + 2) => a i)).count (a n) := by
      exact h_form
    rw [← h_form']
    rw [← history_succ (n + 2)]

lemma a_eq_a_list (n : ℕ) : a n = (a_list (n + 1)).getD n 0 := by
  rw [a_list_eq]
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_ofFn]
  have : n < n + 1 := by omega
  rw [dif_pos this]
  rfl

lemma count_invariants_of_decidable (k : ℕ)
  (h_hist : ∀ x ∈ List.ofFn (fun i : Fin k => a i), a_count x k * x ≤ 2 * k ∧ a_count x k * (a_count x k - 1) ≤ 2 * k)
  (h_ak : a k ≤ k + 1) :
  (∀ x, a_count x k * x ≤ 2 * k ∧ a_count x k * (a_count x k - 1) ≤ 2 * k) ∧ a k ≤ k + 1 := by
  refine ⟨fun x => ?_, h_ak⟩
  by_cases hx : x ∈ List.ofFn (fun i : Fin k => a i)
  · exact h_hist x hx
  · have : a_count x k = 0 := by
      unfold a_count
      exact List.count_eq_zero_of_not_mem hx
    rw [this]
    simp

lemma count_add_self_le (n : ℕ) (x : ℕ) (H : ∀ i < n, a i ≤ i + 1) (hx : a_count x n > 0) :
  a_count x n + x ≤ n + 1 := by
  induction' n with n ih
  · unfold a_count at hx
    simp at hx
  · rw [a_count_succ]
    have H_n : ∀ i < n, a i ≤ i + 1 := fun i hi => H i (by omega)
    have H_an : a n ≤ n + 1 := H n (by omega)
    split_ifs with h
    · -- a n = x
      subst h
      by_cases hx0 : a_count (a n) n = 0
      · rw [hx0]
        omega
      · have hx_gt : a_count (a n) n > 0 := by omega
        have ih_n := ih H_n hx_gt
        omega
    · -- a n ≠ x
      have hx_gt : a_count x n > 0 := by
        rw [a_count_succ] at hx
        rw [if_neg h] at hx
        omega
      have ih_n := ih H_n hx_gt
      omega

lemma square_gt_eight_n_minus_eight (n : ℕ) (hn : 9 ≤ n) : 8 * n - 8 < n * n := by
  have : 8 * n < n * n := by
    calc 8 * n < 9 * n := by omega
    _ ≤ n * n := Nat.mul_le_mul_right n hn
  omega

lemma a_le_n_plus_one_of_lt_9 (n : ℕ) (h : n < 9) : a n ≤ n + 1 := by
  interval_cases n
  all_goals
    rw [a_eq_a_list]
    decide


