import FormalConjectures.Util.ProblemImports

open Classical

noncomputable def get_bool (T : Type) : Bool :=
  if h : T = PUnit.{1} then true else false

theorem eq_punit_of_get_bool_true (α : Type) (h : get_bool α = true) : α = PUnit.{1} := by
  dsimp [get_bool] at h
  split_ifs at h with h_eq
  · exact h_eq
