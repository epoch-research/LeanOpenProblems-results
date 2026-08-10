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

lemma a_le_three_sqrt (n : ℕ) : a n ≤ 3 * Nat.sqrt n := by
  induction' n using Nat.strong_induction_on with n ih
  rw [a_eq n]
  unfold a_aux
  split_ifs with h
  · rcases n with _ | (_ | n)
    · simp
    · simp
    · omega
  · sorry

lemma history_take (i j : ℕ) (hij : i ≤ j) :
  (List.ofFn (fun k : Fin j => a k)).take i = List.ofFn (fun k : Fin i => a k) := by
  rw [← Fin.ofFn_take_eq_take_ofFn hij]
  rfl

theorem oeis_316774_conjecture_4_test : (fun n : ℕ => (a n : ℝ)) =O[atTop] fun n : ℕ => Real.sqrt (n : ℝ) :=
  answer(sorry)











