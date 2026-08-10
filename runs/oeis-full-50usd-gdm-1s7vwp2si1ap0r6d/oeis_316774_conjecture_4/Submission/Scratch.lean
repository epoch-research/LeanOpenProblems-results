import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000

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

def a (n : ℕ) : ℕ :=
  WellFounded.fix Nat.lt_wfRel.wf a_aux n

theorem a_eq (n : ℕ) : a n = a_aux n (fun m _ => a m) := by
  rw [a]
  exact WellFounded.fix_eq Nat.lt_wfRel.wf a_aux n

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

lemma a_formula (k : ℕ) (hk : 2 ≤ k) :
  a k = (List.ofFn (fun i : Fin k => a i)).count (a (k - 1)) + (List.ofFn (fun i : Fin k => a i)).count (a (k - 2)) := by
  rw [a_eq k]
  unfold a_aux
  have h_not : ¬ k < 2 := by omega
  rw [dif_neg h_not]

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
    simp [a_zero : a 0 = 0]
    rfl
  · rw [history_succ 1]
    simp [a_zero : a 0 = 0, a_one : a 1 = 1]
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

lemma a_le_three_sqrt_le_199 (n : ℕ) (hn : n < 200) : a n ≤ 3 * Nat.sqrt n := by
  interval_cases n
  all_goals
    try rw [a_eq_a_list]
    decide
#print axioms oeis_316774_conjecture_4_linear
