import FormalConjectures.Util.ProblemImports

inductive IsBad : ℕ → Prop where
  | below_112 : ∀ x, x < 112 → IsBad x
  | step : ∀ x, IsBad (x + 1) → IsBad x

def IsGoodState (y : ℕ) : Prop :=
  y ≥ 112

mutual
theorem IsGoodState_closed {y : ℕ} (hy : IsGoodState y) : IsGoodState (y + 1) := by
  by_cases h : y < 200
  · unfold IsGoodState at *; omega
  · have h_bad : IsBad y := IsBad.below_112 y (by omega) -- dummy
    exact False.elim (not_IsBad_of_IsGoodState hy h_bad)

theorem not_IsBad_of_IsGoodState {y : ℕ} (hy : IsGoodState y) (h_bad : IsBad y) : False := by
  revert hy
  induction h_bad with
  | below_112 x hx =>
    intro hy
    unfold IsGoodState at hy
    omega
  | step x hx_bad ih =>
    intro hy
    have h_fx : IsGoodState (x + 1) := IsGoodState_closed hy
    exact ih h_fx
end
termination_by
  IsGoodState_closed y hy => 0
  not_IsBad_of_IsGoodState y hy h_bad => h_bad
