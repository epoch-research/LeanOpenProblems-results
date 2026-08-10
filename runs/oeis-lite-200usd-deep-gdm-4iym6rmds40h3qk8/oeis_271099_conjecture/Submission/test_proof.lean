import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma sum_filter_le (c : Fin 19 → ℕ) (_hc_pos : ∀ i, c i > 0)
    (h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (d : ℕ) (hd : d ≤ 1023) :
    d ≤ Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c := by
  rcases (h_rep d hd) with ⟨y, hy_le1, hy_sum⟩
  have h_sub : ∀ j, y j = 1 → c j ≤ d := by
    intro j hj
    by_contra! h_gt
    have h_term : Finset.sum Finset.univ (fun m => c m * y m) ≥ c j * y j := by
      have h_eq : Finset.sum Finset.univ (fun m => c m * y m) = c j * y j + Finset.sum (Finset.univ.erase j) (fun m => c m * y m) := by
        exact (Finset.add_sum_erase Finset.univ (fun m => c m * y m) (Finset.mem_univ j)).symm
      omega
    rw [hj, Nat.mul_one] at h_term
    omega
  have h_zero : ∀ j ∉ Finset.filter (fun j => c j ≤ d) Finset.univ, c j * y j = 0 := by
    intro j hj
    have h_not : ¬ (c j ≤ d) := by
      intro h_le
      apply hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, h_le⟩
    have hj_y : y j = 0 := by
      by_contra! hj_ne
      have hj_eq1 : y j = 1 := by
        have := hy_le1 j
        omega
      have := h_sub j hj_eq1
      exact h_not this
    rw [hj_y, Nat.mul_zero]
  have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j) = Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) (fun j => c j * y j) := by
    rw [Finset.sum_subset (Finset.filter_subset (fun j => c j ≤ d) Finset.univ)]
    intro j _ hj
    exact h_zero j hj
  have h_first_le : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) (fun j => c j * y j) ≤ Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c := by
    refine Finset.sum_le_sum ?_
    intro j _
    have := hy_le1 j
    interval_cases y j <;> omega
  omega

lemma card_bound (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0)
    (h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (d : ℕ) (hd : d ≤ 1023) :
    d + (19 - (Finset.filter (fun j => c j ≤ d) Finset.univ).card) * (d + 1) ≤ 1079 := by
  have h_split : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c + Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ c = Finset.sum Finset.univ c := by
    exact Finset.sum_add_sum_compl _ _
  have h_compl_ge : ∀ j ∈ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ, c j ≥ d + 1 := by
    intro j hj
    rw [Finset.mem_compl] at hj
    have h_not : ¬ (c j ≤ d) := by
      intro h_le
      apply hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, h_le⟩
    omega
  have h_sum_compl_ge : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ c ≥ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card * (d + 1) := by
    have h_le : ∀ j ∈ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ, c j ≥ d + 1 := h_compl_ge
    have h_sum_le := Finset.sum_le_sum h_le
    rw [Finset.sum_const] at h_sum_le
    rw [smul_eq_mul] at h_sum_le
    exact h_sum_le
  have h_card_sum : (Finset.filter (fun j => c j ≤ d) Finset.univ).card + (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = 19 := by
    have h_eq : (Finset.filter (fun j => c j ≤ d) Finset.univ).card + (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = (Finset.univ : Finset (Fin 19)).card := Finset.card_add_card_compl _
    have h_univ_card : (Finset.univ : Finset (Fin 19)).card = 19 := by rfl
    rw [h_univ_card] at h_eq
    exact h_eq
  have h_card_compl_eq : (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = 19 - (Finset.filter (fun j => c j ≤ d) Finset.univ).card := by omega
  rw [h_card_compl_eq] at h_sum_compl_ge
  have h_sum_filter := sum_filter_le c hc_pos h_rep d hd
  omega



