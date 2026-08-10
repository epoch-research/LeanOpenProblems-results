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

def B_200 : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150, 151, 152, 153, 157, 159, 161, 163, 165, 167, 168, 169, 170, 175, 177, 179, 183, 185, 186, 191, 193, 198, 199]

def B : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150]

def G_list : List ℕ := [114, 116, 120, 126, 128, 130, 136, 138, 140, 142, 144, 146, 148]

def is_bad_dt_all (x : ℕ) : Bool :=
  if x < 112 then true
  else decide (x ∈ B_200)

theorem IsBad_of_is_bad_dt_all_true {z : ℕ} (h : is_bad_dt_all z = true) : IsBad z := by
  unfold is_bad_dt_all at h
  split_ifs at h with h1
  · exact IsBad.below_112 z h1
  · have h_mem : z ∈ B_200 := by
      rw [decide_eq_true_iff] at h
      exact h
    sorry -- we can sorry this for testing syntax

theorem IsBad_of_IsBad_iterate {x : ℕ} (k : ℕ) (h : IsBad (A006368_map^[k] x)) : IsBad x := by
  induction k generalizing x with
  | zero => exact h
  | succ k ih =>
    have h_eq : A006368_map^[k + 1] x = A006368_map^[k] (A006368_map x) :=
      congrFun (Function.iterate_succ A006368_map k) x
    rw [h_eq] at h
    have h_bad_fx : IsBad (A006368_map x) := ih h
    exact IsBad.step x h_bad_fx

theorem exists_mem_B_of_IsBad {y : ℕ} (h_bad : IsBad y) : y ≥ 112 → ∃ k, A006368_map^[k] y ∈ B := sorry

theorem B_spec (x : ℕ) (hb : x ∈ B) : ∃ k, A006368_map^[k] x < 112 := sorry

def IsGoodState (y : ℕ) : Prop :=
  (∃ x ∈ G_list, ∃ k, y = A006368_map^[k] x ∧ ¬ IsBad x) ∧ y ≥ 112 ∧ (y ≤ 200 → is_bad_dt_all y = false)

theorem IsGoodState_closed (y : ℕ) (hy : IsGoodState y) : IsGoodState (A006368_map y) := sorry

theorem IsGoodState_iterate {y : ℕ} (hy : IsGoodState y) (k : ℕ) : IsGoodState (A006368_map^[k] y) := by
  induction k with
  | zero => exact hy
  | succ k ih =>
    rw [Function.iterate_succ']
    exact IsGoodState_closed _ ih

def S (n : ℕ) : Prop :=
  n ≥ 112 ∧ ∀ k : ℕ, Nat.iterate A006368_map k n ≥ 112

theorem S_of_IsGoodState {y : ℕ} (h : IsGoodState y) : S y := by
  refine ⟨h.2.1, ?_⟩
  intro k
  exact (IsGoodState_iterate h k).2.1

mutual
theorem is_bad_dt_all_true_of_IsBad (y : ℕ) (h_bad : IsBad y) (hy_ge : y ≥ 112) (hy_le : y ≤ 200) : is_bad_dt_all y = true := by
  interval_cases y
  all_goals try (unfold is_bad_dt_all; decide)
  all_goals try (
    have h_not_bad := not_IsBad_of_mem_G_list _ (by decide)
    have h_gs : IsGoodState _ := ⟨⟨_, _, 0, rfl, h_not_bad⟩, by omega, by decide⟩
    have h_S := S_of_IsGoodState h_gs
    have h_ex := exists_mem_B_of_IsBad h_bad h_S.1
    rcases h_ex with ⟨k, hk⟩
    have h_drop := B_spec _ hk
    rcases h_drop with ⟨m, hm⟩
    have h_ge := h_S.2 (m + k)
    rw [Function.iterate_add_apply] at h_ge
    omega
  )
termination_by 0

theorem not_IsBad_of_mem_G_list (z : ℕ) (hz : z ∈ G_list) : ¬ IsBad z := by
  intro h_bad
  have h_true := is_bad_dt_all_true_of_IsBad z h_bad (by sorry) (by sorry)
  have h_false : is_bad_dt_all z = false := by sorry
  rw [h_false] at h_true
  contradiction
termination_by 0
end
