import FormalConjectures.Util.ProblemImports
open Finset

lemma contradiction_of_small_sum (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (Y Z N M : ℕ)
    (h_N : N = 1024 * Y + Z)
    (h_rep_N : N ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)))
    (h_M : M = max Y Z)
    (h_small : (∑ i ∈ Finset.filter (fun j => c j ≤ M) Finset.univ, c i) < Y + Z)
    (h_Z_le : Z ≤ 1023)
    (h_N_lt : N < 59049) : False := by
  rcases h_rep_N with ⟨y, hy_sum⟩
  dsimp at hy_sum
  have hy_bound : ∀ i, y i ≤ 2 := by
    intro i
    by_contra! h_gt
    have hy_ge3 : y i ≥ 3 := h_gt
    have h_term_ge : c i * y i ^ 10 ≥ 59049 := by
      have hc : c i ≥ 1 := hc_pos i
      have h_pow : y i ^ 10 ≥ 3 ^ 10 := Nat.pow_le_pow_left hy_ge3 10
      calc c i * y i ^ 10 ≥ 1 * 3 ^ 10 := Nat.mul_le_mul hc h_pow
           _ = 59049 := by rfl
    have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j ^ 10) = c i * y i ^ 10 + Finset.sum (Finset.univ.erase i) (fun j => c j * y j ^ 10) := by
      exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j ^ 10) (Finset.mem_univ i)).symm
    rw [hy_sum] at h_sum_split
    omega
  let T2 := Finset.filter (fun i => y i = 2) Finset.univ
  let T1 := Finset.filter (fun i => y i = 1) Finset.univ
  have h_split_y : ∀ i, c i * y i ^ 10 = (if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0) := by
    intro i
    have h_T2 : i ∈ T2 ↔ y i = 2 := by simp [T2]
    have h_T1 : i ∈ T1 ↔ y i = 1 := by simp [T1]
    have hy_le := hy_bound i
    interval_cases y_i : y i
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
      ring
  have h_sum_eq_y : ∑ i, c i * y i ^ 10 = ∑ i, ((if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_split_y i
  have h_sum2_y : (∑ i, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
    have h_split_T2 := (Finset.sum_add_sum_compl T2 (fun i => if i ∈ T2 then 1024 * c i else 0)).symm
    rw [h_split_T2]
    have h_T2_term : (∑ i ∈ T2, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term_y : (∑ i ∈ T2ᶜ, if i ∈ T2 then 1024 * c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T2ᶜ, (if j ∈ T2 then 1024 * c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T2_term, h_compl_term_y, Nat.add_zero]
  have h_sum1_y : (∑ i, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
    have h_split_T1 := (Finset.sum_add_sum_compl T1 (fun i => if i ∈ T1 then c i else 0)).symm
    rw [h_split_T1]
    have h_T1_term : (∑ i ∈ T1, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term1_y : (∑ i ∈ T1ᶜ, if i ∈ T1 then c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T1ᶜ, (if j ∈ T1 then c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T1_term, h_compl_term1_y, Nat.add_zero]
  rw [Finset.sum_add_distrib] at h_sum_eq_y
  simp only [h_sum2_y, h_sum1_y] at h_sum_eq_y
  rw [← Finset.mul_sum] at h_sum_eq_y
  rw [h_sum_eq_y] at hy_sum
  have h_disj_y : Disjoint T2 T1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp [T2, T1]
    intro h2
    omega
  have h_union_le_y : (∑ i ∈ T2 ∪ T1, c i) ≤ ∑ i, c i := by
    have h_split_union := Finset.sum_add_sum_compl (T2 ∪ T1) c
    rw [← h_split_union]
    omega
  have h_sum_union_eq_y : (∑ i ∈ T2 ∪ T1, c i) = (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) := Finset.sum_union h_disj_y
  have h_sum_le_1079_y : (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) ≤ 1079 := by
    rw [← h_sum_union_eq_y]
    rw [h_sum] at h_union_le_y
    exact h_union_le_y
  have h_T2_nonneg : ∑ i ∈ T2, c i ≥ 0 := Finset.sum_nonneg (fun i _ => Nat.zero_le _)
  have h_T1_nonneg : ∑ i ∈ T1, c i ≥ 0 := Finset.sum_nonneg (fun i _ => Nat.zero_le _)
  have h_T2_eq : ∑ i ∈ T2, c i = Y := by omega
  have h_T1_eq : ∑ i ∈ T1, c i = Z := by omega
  have h_sub_filter : T2 ∪ T1 ⊆ Finset.filter (fun j => c j ≤ M) Finset.univ := by
    intro j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    rw [Finset.mem_union] at hj
    rcases hj with hj | hj
    · have h_le : c j ≤ ∑ i ∈ T2, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      rw [h_T2_eq] at h_le
      rw [h_M]
      exact h_le.trans (le_max_left Y Z)
    · have h_le : c j ≤ ∑ i ∈ T1, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      rw [h_T1_eq] at h_le
      rw [h_M]
      exact h_le.trans (le_max_right Y Z)
  have h_sum_sub := Finset.sum_le_sum_of_subset h_sub_filter
  rw [h_sum_union_eq_y, h_T2_eq, h_T1_eq] at h_sum_sub
  omega

