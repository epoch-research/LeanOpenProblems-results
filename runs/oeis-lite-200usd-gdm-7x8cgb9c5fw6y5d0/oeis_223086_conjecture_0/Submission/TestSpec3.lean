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

def B : List ℕ := [112, 113, 115, 117, 118, 119, 121, 122, 123, 124, 125, 127, 129, 131, 132, 133, 134, 135, 137, 139, 141, 143, 145, 147, 149, 150]

theorem H_closed {x : ℕ} (hx : H x) : H (A006368_map x) := by
  rcases hx with ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · by_contra h_lt
    push_neg at h_lt
    have h_bad_fx : IsBad (A006368_map x) := IsBad.below_112 (A006368_map x) h_lt
    have h_bad_x : IsBad x := IsBad.step x h_bad_fx
    exact h2 h_bad_x
  · intro h_bad_fx
    have h_bad_x : IsBad x := IsBad.step x h_bad_fx
    exact h2 h_bad_x

theorem ge_112_of_gt_150 (x : ℕ) (h : x > 150) : A006368_map x ≥ 112 := by
  unfold A006368_map
  split_ifs with h2 h4
  · omega
  · omega
  · omega

theorem mem_B_of_f_lt_112 (y : ℕ) (h1 : y ≥ 112) (h2 : y ≤ 150) (h3 : A006368_map y < 112) : y ∈ B := by
  interval_cases y <;> revert h3 <;> decide

def G_list : List ℕ := [114, 116, 120, 126, 128, 130, 136, 138, 140, 142, 144, 146, 148]

theorem G_list_ge_112 : ∀ x ∈ G_list, A006368_map x ≥ 112 := by decide

theorem not_mem_G_list_imp_mem_B : ∀ y, 112 ≤ y → y ≤ 150 → y ∉ G_list → y ∈ B := by decide

theorem B_spec (x : ℕ) (hb : x ∈ B) : ∃ k, A006368_map^[k] x < 112 := by
  simp only [B, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 13; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 3; decide
  · use 1; decide
  · use 1; decide
  · use 3; decide
  · use 1; decide
  · use 8; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 6; decide
  · use 1; decide
  · use 4; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 1; decide
  · use 14; decide
  · use 4; decide

theorem IsBad_of_exists_iterate_lt {x : ℕ} (h : ∃ k, A006368_map^[k] x < 112) : IsBad x := by
  rcases h with ⟨k, hk⟩
  induction k generalizing x with
  | zero =>
    exact IsBad.below_112 x hk
  | succ k ih =>
    have h_eq : A006368_map^[k + 1] x = A006368_map^[k] (A006368_map x) :=
      congrFun (Function.iterate_succ A006368_map k) x
    rw [h_eq] at hk
    have h_bad_fx : IsBad (A006368_map x) := ih hk
    exact IsBad.step x h_bad_fx

theorem IsBad_of_mem_B {x : ℕ} (h : x ∈ B) : IsBad x := by
  exact IsBad_of_exists_iterate_lt (B_spec x h)

def Good (x : ℕ) : Prop :=
  x ≥ 112 ∧ (x ≤ 150 → x ∈ G_list) ∧ (x > 150 → ¬ IsBad x)

mutual
theorem Good_closed {x : ℕ} (hx : Good x) : Good (A006368_map x) := by
  have h_hx := hx
  rcases hx with ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases hx_le : x ≤ 150
    · have h_mem := h2 hx_le
      exact G_list_ge_112 x h_mem
    · have hx_gt : x > 150 := by omega
      exact ge_112_of_gt_150 x (by omega)
  · intro h_fx_le
    by_cases hx_le : x ≤ 150
    · have h_mem := h2 hx_le
      have h_fx_gt : A006368_map x > 150 := by
        simp only [G_list, List.mem_cons, List.not_mem_nil, or_false] at h_mem
        rcases h_mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      omega
    · have hx_gt : x > 150 := by omega
      by_contra h_not_mem
      have h_mem_B : A006368_map x ∈ B := not_mem_G_list_imp_mem_B (A006368_map x) (ge_112_of_gt_150 x (by omega)) h_fx_le h_not_mem
      have h_bad_fx : IsBad (A006368_map x) := IsBad_of_mem_B h_mem_B
      have h_bad_x : IsBad x := IsBad.step x h_bad_fx
      exact h3 hx_gt h_bad_x
  · intro h_fx_gt h_bad_fx
    by_cases hx_le : x ≤ 150
    · have h_mem := h2 hx_le
      have h_ge : x ≥ 112 := by
        have h_ge_all : G_list.all (fun x => decide (x ≥ 112)) = true := by decide
        rw [List.all_eq_true] at h_ge_all
        have h_dec := h_ge_all x h_mem
        simp only [decide_eq_true_iff] at h_dec
        omega
      have h_bad_x : IsBad x := IsBad.step x h_bad_fx
      exact not_IsBad_of_Good_helper h_bad_x h_ge h_hx
    · have hx_gt : x > 150 := by omega
      have h_bad_x : IsBad x := IsBad.step x h_bad_fx
      exact h3 hx_gt h_bad_x
termination_by 0

theorem not_IsBad_of_Good_helper {x : ℕ} (h_bad : IsBad x) (hx_ge : x ≥ 112) (hx : Good x) : False := by
  induction h_bad with
  | below_112 z hz =>
    omega
  | step z hz_bad ih =>
    have h_fz_ge : A006368_map z ≥ 112 := by
      by_cases hz_le : z ≤ 150
      · have h_mem := hx.2.1 hz_le
        exact G_list_ge_112 z h_mem
      · exact ge_112_of_gt_150 z (by omega)
    exact ih h_fz_ge (Good_closed hx)
termination_by sizeOf h_bad
end
