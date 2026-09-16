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

lemma a_bound : ∃ C : ℝ, ∀ n : ℕ, (a n : ℝ) ≤ C * Real.sqrt (n : ℝ) := sorry

theorem oeis_316774_conjecture_4 : (fun n : ℕ => (a n : ℝ)) =O[atTop] fun n : ℕ => Real.sqrt (n : ℝ) := by
  rcases a_bound with ⟨C, hC⟩
  refine Asymptotics.IsBigO.of_bound (|C|) ?_
  filter_upwards
  intro n
  have h1 : (a n : ℝ) ≤ C * Real.sqrt (n : ℝ) := hC n
  have h2 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg (n : ℝ)
  have h3 : 0 ≤ (a n : ℝ) := Nat.cast_nonneg (a n)
  calc
    ‖(a n : ℝ)‖ = (a n : ℝ) := abs_of_nonneg h3
    _ ≤ C * Real.sqrt (n : ℝ) := h1
    _ ≤ |C| * Real.sqrt (n : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ = |C| * ‖Real.sqrt (n : ℝ)‖ := by rw [abs_of_nonneg h2]

theorem oeis_316774_conjecture_4.disproof : ¬ (type_of% @oeis_316774_conjecture_4) := by
  intro h
  sorry
