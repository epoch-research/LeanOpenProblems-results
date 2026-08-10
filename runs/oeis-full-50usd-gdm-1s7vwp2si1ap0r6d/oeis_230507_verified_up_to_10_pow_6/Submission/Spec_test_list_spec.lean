import FormalConjectures.Util.ProblemImports

def S_condition (m : ℕ) : Prop := m = 1 ∨ m = 2 ∨ m = 5

theorem S_condition_C_1 : S_condition 1 := by simp [S_condition]
theorem S_condition_C_2 : S_condition 2 := by simp [S_condition]
theorem S_condition_C_5 : S_condition 5 := by simp [S_condition]

def C_list : List ℕ := [1, 2, 5]

theorem spec_of_mem_cons {x : ℕ} {xs : List ℕ} (hx : S_condition x) (h_tail : ∀ y ∈ xs, S_condition y) :
    ∀ y ∈ x :: xs, S_condition y := by
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact h_tail y hy

theorem spec_of_mem_nil : ∀ y ∈ ([] : List ℕ), S_condition y := by
  intro y hy
  nomatch hy

theorem CustomS_spec_mem : ∀ y ∈ C_list, S_condition y :=
  spec_of_mem_cons S_condition_C_1 (spec_of_mem_cons S_condition_C_2 (spec_of_mem_cons S_condition_C_5 spec_of_mem_nil))

def CustomS (m : ℕ) : Bool := decide (m ∈ C_list)

theorem CustomS_spec (m : ℕ) (h : CustomS m = true) : S_condition m := by
  have h_mem : m ∈ C_list := of_decide_eq_true h
  exact CustomS_spec_mem m h_mem
