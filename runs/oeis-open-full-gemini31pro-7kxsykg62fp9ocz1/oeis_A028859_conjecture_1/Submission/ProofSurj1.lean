import Submission.ProofS3
import Submission.ProofNodupFinal
import Mathlib

def drop_last {L : ℕ} (x : Fin (L+1) → ℕ) : Fin L → ℕ := fun i => x (Fin.castSucc i)
def drop_last2 {L : ℕ} (x : Fin (L+2) → ℕ) : Fin L → ℕ := fun i => x (Fin.castSucc (Fin.castSucc i))
def shift_down {L : ℕ} (x : Fin L → ℕ) (c : ℕ) : Fin L → ℕ := fun i => x i - c

set_option linter.unusedVariables false

theorem end_2_implies_prev_1_local {L : ℕ} (x : Fin (L+2) → ℕ)
  (hx : isValid2 x) (hend : x (Fin.last (L+1)) = 2) :
  x ⟨L, by omega⟩ = 1 := by
  have h_cond : 1 ≤ 1 ∧ 1 ≤ Finset.sup Finset.univ x := by
    constructor
    · omega
    · have h0 : (Fin.last (L+1)) ∈ Finset.univ := Finset.mem_univ _
      have h_le := Finset.le_sup (f := x) h0
      omega
  have ⟨i, hi⟩ := hx.2.2.1 1 h_cond
  have h_i_bound : i.val = L := by
    by_contra h_neq
    have h_lt : i.val < L + 1 := by
      by_contra h_ge
      push_neg at h_ge
      have h_i_eq : i.val = L + 1 := by have := i.isLt; omega
      have h_eq2 : x i = x (Fin.last (L+1)) := congrArg x (Fin.ext h_i_eq)
      rw [h_eq2, hend] at hi
      omega
    have h_neq2 : (Fin.last (L+1) : Fin (L+2)).val ≠ i.val + 1 := by
      have h2 : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
      omega
    have h_lt2 : i.val < (Fin.last (L+1) : Fin (L+2)).val := by
      have h2 : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
      omega
    have := hx.2.2.2 i (Fin.last (L+1)) h_lt2 h_neq2
    rw [hi, hend] at this
    omega
  have : i = ⟨L, by omega⟩ := Fin.ext h_i_bound
  rw [←this]
  exact hi

theorem drop_last2_ge_2 {L : ℕ} (hL : L > 0) (x : Fin (L+2) → ℕ) (hx : isValid2 x)
  (hend : x (Fin.last (L+1)) = 2) : ∀ i : Fin L, drop_last2 x i ≥ 2 := by
  intro i
  have h_dl : drop_last2 x i = x (Fin.castSucc (Fin.castSucc i)) := rfl
  rw [h_dl]
  have h_lt : (Fin.castSucc (Fin.castSucc i) : Fin (L+2)) < Fin.last (L+1) := by
    have h1 : (Fin.castSucc (Fin.castSucc i) : Fin (L+2)).val = i.val := rfl
    have h2 : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
    omega
  have h_neq : (Fin.last (L+1) : Fin (L+2)).val ≠ (Fin.castSucc (Fin.castSucc i) : Fin (L+2)).val + 1 := by
    have h1 : (Fin.castSucc (Fin.castSucc i) : Fin (L+2)).val = i.val := rfl
    have h2 : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
    omega
  have h_ge := hx.2.2.2 (Fin.castSucc (Fin.castSucc i)) (Fin.last (L+1)) h_lt h_neq
  rw [hend] at h_ge
  exact h_ge

theorem drop_last2_max {L : ℕ} (hL : L > 0) (x : Fin (L+2) → ℕ) (hx : isValid2 x)
  (hend : x (Fin.last (L+1)) = 2) :
  Finset.sup Finset.univ (drop_last2 x) = Finset.sup Finset.univ x := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    have : drop_last2 x i = x (Fin.castSucc (Fin.castSucc i)) := rfl
    rw [this]
    exact Finset.le_sup (Finset.mem_univ _)
  · apply Finset.sup_le
    intro i _
    by_cases h1 : i = Fin.last (L+1)
    · rw [h1, hend]
      have h0 : (⟨0, hL⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
      have hge : drop_last2 x ⟨0, hL⟩ ≥ 2 := drop_last2_ge_2 hL x hx hend ⟨0, hL⟩
      have := Finset.le_sup (f := drop_last2 x) h0
      omega
    · by_cases h2 : i.val = L
      · have h_prev : x i = 1 := by
          have h_eq : i = ⟨L, by omega⟩ := Fin.ext h2
          rw [h_eq]
          exact end_2_implies_prev_1_local x hx hend
        rw [h_prev]
        have h0 : (⟨0, hL⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
        have hge : drop_last2 x ⟨0, hL⟩ ≥ 2 := drop_last2_ge_2 hL x hx hend ⟨0, hL⟩
        have := Finset.le_sup (f := drop_last2 x) h0
        omega
      · have h_lt : i.val < L := by
          have := i.isLt
          have h_last : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
          omega
        have : i = Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) := Fin.ext rfl
        rw [this]
        have h_dl : x (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) = drop_last2 x ⟨i.val, h_lt⟩ := rfl
        rw [h_dl]
        exact Finset.le_sup (Finset.mem_univ _)

theorem shift_drop_last2_max {L : ℕ} (hL : L > 0) (x : Fin (L+2) → ℕ) (hx : isValid2 x)
  (hend : x (Fin.last (L+1)) = 2) (c : ℕ) (hc : c ≤ 2) :
  Finset.sup Finset.univ (shift_down (drop_last2 x) c) = Finset.sup Finset.univ x - c := by
  have h_max := drop_last2_max hL x hx hend
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    have h1 : shift_down (drop_last2 x) c i = drop_last2 x i - c := rfl
    rw [h1]
    have := Finset.le_sup (f := drop_last2 x) (Finset.mem_univ i)
    rw [h_max] at this
    omega
  · have h_cond : 1 ≤ Finset.sup Finset.univ x ∧ Finset.sup Finset.univ x ≤ Finset.sup Finset.univ x := by
      constructor
      · have h0 : (⟨0, by omega⟩ : Fin (L+2)) ∈ Finset.univ := Finset.mem_univ _
        have h_pos := hx.2.1 ⟨0, by omega⟩
        have h_le := Finset.le_sup (f := x) h0
        omega
      · exact le_rfl
    have ⟨i, hi⟩ := hx.2.2.1 (Finset.sup Finset.univ x) h_cond
    by_cases h1 : i = Fin.last (L+1)
    · rw [h1, hend] at hi
      have h0 : (⟨0, hL⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
      have hge : drop_last2 x ⟨0, hL⟩ ≥ 2 := drop_last2_ge_2 hL x hx hend ⟨0, hL⟩
      have h_le := Finset.le_sup (f := shift_down (drop_last2 x) c) h0
      have h_eval : shift_down (drop_last2 x) c ⟨0, hL⟩ = drop_last2 x ⟨0, hL⟩ - c := rfl
      rw [h_eval] at h_le
      have h_max_x : Finset.sup Finset.univ x = 2 := by omega
      rw [h_max_x]
      omega
    · by_cases h2 : i.val = L
      · have h_prev : x i = 1 := by
          have h_eq : i = ⟨L, by omega⟩ := Fin.ext h2
          rw [h_eq]
          exact end_2_implies_prev_1_local x hx hend
        rw [h_prev] at hi
        have h0 : (⟨0, hL⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
        have hge : drop_last2 x ⟨0, hL⟩ ≥ 2 := drop_last2_ge_2 hL x hx hend ⟨0, hL⟩
        have h_le := Finset.le_sup (f := shift_down (drop_last2 x) c) h0
        have h_eval : shift_down (drop_last2 x) c ⟨0, hL⟩ = drop_last2 x ⟨0, hL⟩ - c := rfl
        rw [h_eval] at h_le
        have h_max_x : Finset.sup Finset.univ x = 1 := by omega
        rw [h_max_x]
        omega
      · have h_lt : i.val < L := by
          have := i.isLt
          have h_last : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
          omega
        have h_eq2 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)) = i := Fin.ext rfl
        rw [←h_eq2] at hi
        have h_mem : (⟨i.val, h_lt⟩ : Fin L) ∈ Finset.univ := Finset.mem_univ _
        have h_le := Finset.le_sup (f := shift_down (drop_last2 x) c) h_mem
        have h1 : shift_down (drop_last2 x) c ⟨i.val, h_lt⟩ = drop_last2 x ⟨i.val, h_lt⟩ - c := rfl
        rw [h1] at h_le
        have h_eval2 : drop_last2 x ⟨i.val, h_lt⟩ = x (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) := rfl
        rw [h_eval2, hi] at h_le
        exact h_le

theorem valid2_drop_last2_has_2 {L : ℕ} (hL : L > 0)
  (x : Fin (L+2) → ℕ) (hx : isValid2 x) (hend : x (Fin.last (L+1)) = 2)
  (h_has_2 : ∃ i : Fin L, drop_last2 x i = 2) :
  isValid2 (shift_down (drop_last2 x) 1) := by
  constructor
  · exact hL
  constructor
  · intro i
    have h_ge2 := drop_last2_ge_2 hL x hx hend i
    have : shift_down (drop_last2 x) 1 i = drop_last2 x i - 1 := rfl
    rw [this]
    omega
  constructor
  · intro k hk
    have h_max_eq := shift_drop_last2_max hL x hx hend 1 (by omega)
    rw [h_max_eq] at hk
    have h_cond : 1 ≤ k + 1 ∧ k + 1 ≤ Finset.sup Finset.univ x := by omega
    have ⟨i, hi⟩ := hx.2.2.1 (k + 1) h_cond
    by_cases h1 : i = Fin.last (L+1)
    · rw [h1, hend] at hi
      have h_k : k = 1 := by omega
      rw [h_k]
      rcases h_has_2 with ⟨j, hj⟩
      use j
      have : shift_down (drop_last2 x) 1 j = drop_last2 x j - 1 := rfl
      rw [this, hj]
    · by_cases h2 : i.val = L
      · have h_prev : x i = 1 := by
          have h_eq : i = ⟨L, by omega⟩ := Fin.ext h2
          rw [h_eq]
          exact end_2_implies_prev_1_local x hx hend
        rw [h_prev] at hi
        omega
      · have h_lt : i.val < L := by
          have := i.isLt
          have h_last : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
          omega
        use ⟨i.val, h_lt⟩
        have h_eq2 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)) = i := Fin.ext rfl
        have : shift_down (drop_last2 x) 1 ⟨i.val, h_lt⟩ = drop_last2 x ⟨i.val, h_lt⟩ - 1 := rfl
        rw [this]
        have : drop_last2 x ⟨i.val, h_lt⟩ = x i := by
          have : drop_last2 x ⟨i.val, h_lt⟩ = x (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) := rfl
          rw [this, h_eq2]
        rw [this, hi]
        omega
  · intro i j h_lt h_neq
    have h_lt2 : (Fin.castSucc (Fin.castSucc i) : Fin (L+2)) < Fin.castSucc (Fin.castSucc j) := h_lt
    have h_neq2 : (Fin.castSucc (Fin.castSucc j) : Fin (L+2)).val ≠ (Fin.castSucc (Fin.castSucc i) : Fin (L+2)).val + 1 := h_neq
    have h_ge := hx.2.2.2 (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc j)) h_lt2 h_neq2
    have h1 : shift_down (drop_last2 x) 1 i = drop_last2 x i - 1 := rfl
    have h2 : shift_down (drop_last2 x) 1 j = drop_last2 x j - 1 := rfl
    have h_dl_i : drop_last2 x i = x (Fin.castSucc (Fin.castSucc i)) := rfl
    have h_dl_j : drop_last2 x j = x (Fin.castSucc (Fin.castSucc j)) := rfl
    rw [h1, h2, h_dl_i, h_dl_j]
    have h_pos_j : x (Fin.castSucc (Fin.castSucc j)) ≥ 2 := by
      have : drop_last2 x j = x (Fin.castSucc (Fin.castSucc j)) := rfl
      rw [←this]
      exact drop_last2_ge_2 hL x hx hend j
    omega


theorem valid2_drop_last2_no_2 {L : ℕ} (hL : L > 0)
  (x : Fin (L+2) → ℕ) (hx : isValid2 x) (hend : x (Fin.last (L+1)) = 2)
  (h_no_2 : ¬∃ i : Fin L, drop_last2 x i = 2) :
  isValid2 (shift_down (drop_last2 x) 2) := by
  have h_ge3 : ∀ i, drop_last2 x i ≥ 3 := by
    intro i
    have h_ge2 := drop_last2_ge_2 hL x hx hend i
    have h_neq2 : drop_last2 x i ≠ 2 := by
      intro h_eq
      exact h_no_2 ⟨i, h_eq⟩
    omega
  constructor
  · exact hL
  constructor
  · intro i
    have h3 := h_ge3 i
    have : shift_down (drop_last2 x) 2 i = drop_last2 x i - 2 := rfl
    rw [this]
    omega
  constructor
  · intro k hk
    have h_max_eq := shift_drop_last2_max hL x hx hend 2 (by omega)
    rw [h_max_eq] at hk
    have h_cond : 1 ≤ k + 2 ∧ k + 2 ≤ Finset.sup Finset.univ x := by omega
    have ⟨i, hi⟩ := hx.2.2.1 (k + 2) h_cond
    by_cases h1 : i = Fin.last (L+1)
    · rw [h1, hend] at hi
      omega
    · by_cases h2 : i.val = L
      · have h_prev : x i = 1 := by
          have h_eq : i = ⟨L, by omega⟩ := Fin.ext h2
          rw [h_eq]
          exact end_2_implies_prev_1_local x hx hend
        rw [h_prev] at hi
        omega
      · have h_lt : i.val < L := by
          have := i.isLt
          have h_last : (Fin.last (L+1) : Fin (L+2)).val = L + 1 := rfl
          omega
        use ⟨i.val, h_lt⟩
        have h_eq2 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)) = i := Fin.ext rfl
        have : shift_down (drop_last2 x) 2 ⟨i.val, h_lt⟩ = drop_last2 x ⟨i.val, h_lt⟩ - 2 := rfl
        rw [this]
        have : drop_last2 x ⟨i.val, h_lt⟩ = x i := by
          have : drop_last2 x ⟨i.val, h_lt⟩ = x (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) := rfl
          rw [this, h_eq2]
        rw [this, hi]
        omega
  · intro i j h_lt h_neq
    have h_lt2 : (Fin.castSucc (Fin.castSucc i) : Fin (L+2)) < Fin.castSucc (Fin.castSucc j) := h_lt
    have h_neq2 : (Fin.castSucc (Fin.castSucc j) : Fin (L+2)).val ≠ (Fin.castSucc (Fin.castSucc i) : Fin (L+2)).val + 1 := h_neq
    have h_ge := hx.2.2.2 (Fin.castSucc (Fin.castSucc i)) (Fin.castSucc (Fin.castSucc j)) h_lt2 h_neq2
    have h1 : shift_down (drop_last2 x) 2 i = drop_last2 x i - 2 := rfl
    have h2 : shift_down (drop_last2 x) 2 j = drop_last2 x j - 2 := rfl
    have h_dl_i : drop_last2 x i = x (Fin.castSucc (Fin.castSucc i)) := rfl
    have h_dl_j : drop_last2 x j = x (Fin.castSucc (Fin.castSucc j)) := rfl
    rw [h1, h2, h_dl_i, h_dl_j]
    have h_pos_j : x (Fin.castSucc (Fin.castSucc j)) ≥ 3 := by
      have : drop_last2 x j = x (Fin.castSucc (Fin.castSucc j)) := rfl
      rw [←this]
      exact h_ge3 j
    omega

