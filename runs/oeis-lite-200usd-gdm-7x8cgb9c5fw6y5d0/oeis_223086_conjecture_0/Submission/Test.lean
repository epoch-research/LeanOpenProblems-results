import FormalConjectures.Util.ProblemImports

open Nat Classical

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

inductive IsBad : ℕ → Prop where
  | below_112 : ∀ x, x < 112 → IsBad x
  | step : ∀ x, IsBad (A006368_map x) → IsBad x

def H (x : ℕ) : Prop :=
  x ≥ 112 ∧ ¬ IsBad x

def B_200 : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 185, 186, 191, 193, 198, 199]

def B : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150]

def G_list : List ℕ := [114, 116, 120, 126, 128, 130, 136, 138, 140, 142, 144, 146, 148]

def is_bad_dt_all (x : ℕ) : Bool :=
  if x < 112 then true
  else decide (x ∈ B_200)

theorem H_closed {x : ℕ} (hx : H x) : H (A006368_map x) := sorry

def IsGoodState (y : ℕ) : Prop :=
  y = 144 ∨ H y

mutual
theorem IsGoodState_closed (y : ℕ) (hy : IsGoodState y) : IsGoodState (A006368_map y) := by
  rcases hy with rfl | hy
  · -- y = 144
    right
    refine ⟨by decide, ?_⟩
    intro h_bad_216
    have h_bad_144 : IsBad 144 := IsBad.step 144 h_bad_216
    exact not_IsBad_of_IsGoodState (Or.inl rfl) h_bad_144
  · -- H y
    right
    exact H_closed hy
termination_by 0

theorem not_IsBad_of_IsGoodState {y : ℕ} (hy : IsGoodState y) (h_bad : IsBad y) : False := by
  revert hy
  induction h_bad with
  | below_112 x hx =>
    intro hy
    rcases hy with rfl | hy
    · omega
    · exact hy.2 (IsBad.below_112 x hx)
  | step x hx_bad ih =>
    intro hy
    have h_fx : IsGoodState (A006368_map x) := IsGoodState_closed x hy
    exact ih h_fx
termination_by sizeOf h_bad
end

def S (n : ℕ) : Prop :=
  n ≥ 112 ∧ ∀ k : ℕ, Nat.iterate A006368_map k n ≥ 112

theorem IsGoodState_iterate {y : ℕ} (hy : IsGoodState y) (k : ℕ) : IsGoodState (A006368_map^[k] y) := by
  induction k with
  | zero => exact hy
  | succ k ih =>
    rw [Function.iterate_succ']
    exact IsGoodState_closed _ ih

theorem S_of_IsGoodState {y : ℕ} (h : IsGoodState y) : S y := by
  refine ⟨by
    rcases h with rfl | h
    · decide
    · exact h.1, ?_⟩
  intro k
  have h_it := IsGoodState_iterate h k
  rcases h_it with h_eq | h_it
  · rw [h_eq]
    decide
  · exact h_it.1
