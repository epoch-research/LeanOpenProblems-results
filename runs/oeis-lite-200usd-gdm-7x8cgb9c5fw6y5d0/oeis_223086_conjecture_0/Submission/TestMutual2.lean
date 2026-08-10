import FormalConjectures.Util.ProblemImports

inductive IsBad : ℕ → Prop where
  | below_112 : ∀ x, x < 112 → IsBad x
  | step : ∀ x, IsBad (x + 1) → IsBad x

def G_list : List ℕ := [144]

def is_bad_dt_all (x : ℕ) : Bool := false

def IsGoodState (y : ℕ) : Prop :=
  (∃ x ∈ G_list, ∃ k, y = x + k) ∧ y ≥ 112 ∧ (y ≤ 200 → is_bad_dt_all y = false)

mutual
theorem IsGoodState_closed {y : ℕ} (hy : IsGoodState y) : IsGoodState (y + 1) := by
  rcases hy with ⟨⟨x, h_x_G, k, hk⟩, h1, h2⟩
  refine ⟨⟨x, h_x_G, k + 1, by omega⟩, by omega, by intro _; rfl⟩

theorem IsGoodState_iterate_mutual {y : ℕ} (hy : IsGoodState y) (k : ℕ) : IsGoodState (y + k) := by
  induction k with
  | zero => exact hy
  | succ k ih =>
    have : y + (k + 1) = (y + k) + 1 := by omega
    rw [this]
    exact IsGoodState_closed ih

theorem not_IsBad_of_mem_G_list {z : ℕ} (h_G : z ∈ G_list) : ¬ IsBad z := by
  intro h_bad
  have h_good : IsGoodState z := by
    refine ⟨⟨z, h_G, 0, by omega⟩, by omega, by intro _; rfl⟩
  have h_good_m := IsGoodState_iterate_mutual h_good 10
  exact h_bad
end
