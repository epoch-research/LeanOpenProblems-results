import Submission.ProofSurj1
import Submission.ProofNodupFinal
import Mathlib

set_option linter.unusedVariables false

theorem end_2_implies_prev_1 {L : ℕ} (x : Fin (L+2) → ℕ)
  (hx : isValid2 x) (hend : x ⟨L + 1, by omega⟩ = 2) :
  x ⟨L, by omega⟩ = 1 := by
  have h_last : x (Fin.last (L+1)) = 2 := by
    have : (Fin.last (L+1) : Fin (L+2)) = ⟨L+1, by omega⟩ := rfl
    rw [this]
    exact hend
  exact end_2_implies_prev_1_local x hx h_last

theorem x_eq_map2 {L : ℕ} (x : Fin (L+1) → ℕ) (hend : x (Fin.last L) = 1) :
  x = map2 (drop_last x) := by
  ext i
  unfold map2
  by_cases h_i : i.val = L
  · have h_eq : i = Fin.last L := Fin.ext h_i
    rw [h_eq, Fin.snoc_last]
    exact hend
  · have h_lt : i.val < L := by omega
    have h_eq : i = Fin.castSucc ⟨i.val, h_lt⟩ := Fin.ext rfl
    rw [h_eq, Fin.snoc_castSucc]
    rfl

theorem x_eq_map1 {L : ℕ} (x : Fin (L+1) → ℕ) (hx : isValid2 x) (hend : x (Fin.last L) = 1) :
  x = map1 (shift_down (drop_last x) 1) := by
  unfold map1 shift_seq shift_down
  ext i
  by_cases h_i : i.val = L
  · have h_eq : i = Fin.last L := Fin.ext h_i
    rw [h_eq]
    have h1 : (Fin.snoc (fun j => drop_last x j - 1 + 1) 1 : Fin (L+1) → ℕ) (Fin.last L) = 1 := by rw [Fin.snoc_last]
    rw [h1]
    exact hend
  · have h_lt : i.val < L := by omega
    have h_eq : i = Fin.castSucc ⟨i.val, h_lt⟩ := Fin.ext rfl
    rw [h_eq]
    have h1 : (Fin.snoc (fun j => drop_last x j - 1 + 1) 1 : Fin (L+1) → ℕ) (Fin.castSucc ⟨i.val, h_lt⟩) = drop_last x ⟨i.val, h_lt⟩ - 1 + 1 := by rw [Fin.snoc_castSucc]
    rw [h1]
    have : drop_last x ⟨i.val, h_lt⟩ ≥ 1 := hx.2.1 (Fin.castSucc ⟨i.val, h_lt⟩)
    have : drop_last x ⟨i.val, h_lt⟩ - 1 + 1 = drop_last x ⟨i.val, h_lt⟩ := by omega
    rw [this]
    rfl

theorem x_eq_map3 {L : ℕ} (x : Fin (L+2) → ℕ)
  (hx : isValid2 x) (hend : x ⟨L + 1, by omega⟩ = 2) :
  x = map3 (shift_down (drop_last2 x) 1) := by
  have h_prev : x ⟨L, by omega⟩ = 1 := end_2_implies_prev_1 x hx hend
  unfold map3 shift_seq shift_down
  ext i
  by_cases h_i : i.val = L + 1
  · have h_eq : i = ⟨L + 1, by omega⟩ := Fin.ext h_i
    rw [h_eq]
    have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 1 + 1) 1) 2 : Fin (L+2) → ℕ) ⟨L + 1, by omega⟩ = 2 := by
      have : (⟨L + 1, by omega⟩ : Fin (L+2)) = Fin.last (L+1) := rfl
      rw [this, Fin.snoc_last]
    rw [h1]
    exact hend
  · by_cases h_i2 : i.val = L
    · have h_eq : i = ⟨L, by omega⟩ := Fin.ext h_i2
      rw [h_eq]
      have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 1 + 1) 1) 2 : Fin (L+2) → ℕ) ⟨L, by omega⟩ = 1 := by
        have h_lt : L < L + 1 := by omega
        have : (⟨L, by omega⟩ : Fin (L+2)) = Fin.castSucc (⟨L, h_lt⟩ : Fin (L+1)) := rfl
        rw [this, Fin.snoc_castSucc]
        have : (⟨L, h_lt⟩ : Fin (L+1)) = Fin.last L := rfl
        rw [this, Fin.snoc_last]
      rw [h1]
      exact h_prev
    · have h_lt : i.val < L := by omega
      have h_eq : i = Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) := Fin.ext rfl
      rw [h_eq]
      have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 1 + 1) 1) 2 : Fin (L+2) → ℕ) (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) = drop_last2 x ⟨i.val, h_lt⟩ - 1 + 1 := by
        have h_lt1 : i.val < L + 1 := by omega
        have h_cast1 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)) = Fin.castSucc (⟨i.val, h_lt1⟩ : Fin (L+1)) := rfl
        rw [h_cast1, Fin.snoc_castSucc]
        have h_cast2 : (⟨i.val, h_lt1⟩ : Fin (L+1)) = Fin.castSucc ⟨i.val, h_lt⟩ := rfl
        rw [h_cast2, Fin.snoc_castSucc]
      rw [h1]
      have h_hij : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)).val < (⟨L + 1, by omega⟩ : Fin (L+2)).val := by
        have h1 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)).val = i.val := rfl
        have h2 : (⟨L + 1, by omega⟩ : Fin (L+2)).val = L + 1 := rfl
        omega
      have h_hneq : (⟨L + 1, by omega⟩ : Fin (L+2)).val ≠ (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)).val + 1 := by
        have h1 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)).val = i.val := rfl
        have h2 : (⟨L + 1, by omega⟩ : Fin (L+2)).val = L + 1 := rfl
        omega
      have := hx.2.2.2 (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) ⟨L + 1, by omega⟩ h_hij h_hneq
      rw [hend] at this
      have : drop_last2 x ⟨i.val, h_lt⟩ ≥ 2 := by
        have h_eq3 : drop_last2 x ⟨i.val, h_lt⟩ = x (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) := rfl
        rw [h_eq3]
        exact this
      have : drop_last2 x ⟨i.val, h_lt⟩ - 1 + 1 = drop_last2 x ⟨i.val, h_lt⟩ := by omega
      rw [this]
      rfl

theorem x_eq_map4 {L : ℕ} (x : Fin (L+2) → ℕ)
  (hx : isValid2 x) (hend : x ⟨L + 1, by omega⟩ = 2) :
  x = map4 (shift_down (drop_last2 x) 2) := by
  have h_prev : x ⟨L, by omega⟩ = 1 := end_2_implies_prev_1 x hx hend
  unfold map4 shift_seq shift_down
  ext i
  by_cases h_i : i.val = L + 1
  · have h_eq : i = ⟨L + 1, by omega⟩ := Fin.ext h_i
    rw [h_eq]
    have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 2 + 2) 1) 2 : Fin (L+2) → ℕ) ⟨L + 1, by omega⟩ = 2 := by
      have : (⟨L + 1, by omega⟩ : Fin (L+2)) = Fin.last (L+1) := rfl
      rw [this, Fin.snoc_last]
    rw [h1]
    exact hend
  · by_cases h_i2 : i.val = L
    · have h_eq : i = ⟨L, by omega⟩ := Fin.ext h_i2
      rw [h_eq]
      have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 2 + 2) 1) 2 : Fin (L+2) → ℕ) ⟨L, by omega⟩ = 1 := by
        have h_lt : L < L + 1 := by omega
        have : (⟨L, by omega⟩ : Fin (L+2)) = Fin.castSucc (⟨L, h_lt⟩ : Fin (L+1)) := rfl
        rw [this, Fin.snoc_castSucc]
        have : (⟨L, h_lt⟩ : Fin (L+1)) = Fin.last L := rfl
        rw [this, Fin.snoc_last]
      rw [h1]
      exact h_prev
    · have h_lt : i.val < L := by omega
      have h_eq : i = Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) := Fin.ext rfl
      rw [h_eq]
      have h1 : (Fin.snoc (Fin.snoc (fun j => drop_last2 x j - 2 + 2) 1) 2 : Fin (L+2) → ℕ) (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩)) = drop_last2 x ⟨i.val, h_lt⟩ - 2 + 2 := by
        have h_lt1 : i.val < L + 1 := by omega
        have h_cast1 : (Fin.castSucc (Fin.castSucc ⟨i.val, h_lt⟩) : Fin (L+2)) = Fin.castSucc (⟨i.val, h_lt1⟩ : Fin (L+1)) := rfl
        rw [h_cast1, Fin.snoc_castSucc]
        have h_cast2 : (⟨i.val, h_lt1⟩ : Fin (L+1)) = Fin.castSucc ⟨i.val, h_lt⟩ := rfl
        rw [h_cast2, Fin.snoc_castSucc]
      rw [h1]
      have h_last : x (Fin.last (L+1)) = 2 := by
        have : (Fin.last (L+1) : Fin (L+2)) = ⟨L+1, by omega⟩ := rfl
        rw [this]
        exact hend
      have h_ge2 : drop_last2 x ⟨i.val, h_lt⟩ ≥ 2 := drop_last2_ge_2 (by omega) x hx h_last ⟨i.val, h_lt⟩
      have : drop_last2 x ⟨i.val, h_lt⟩ - 2 + 2 = drop_last2 x ⟨i.val, h_lt⟩ := by omega
      rw [this]
      rfl

theorem surj_gen_impl (L : ℕ) : ∀ x, isValid2 x → (L > 0 → x ∈ gen L) := by
  induction' L using Nat.strongRecOn with L ih
  rcases L with _ | _ | _ | L
  · intro x hx hL
    omega
  · intro x hx hL
    rw [gen.eq_2]
    simp
    have : x 0 = 1 := by
      have h_cond : 1 ≤ 1 ∧ 1 ≤ Finset.sup Finset.univ x := by
        constructor
        · omega
        · have h0 : (⟨0, by omega⟩ : Fin 1) ∈ Finset.univ := Finset.mem_univ _
          have h_le := Finset.le_sup (f := x) h0
          have h_pos := hx.2.1 ⟨0, by omega⟩
          omega
      have ⟨i, hi⟩ := hx.2.2.1 1 h_cond
      have h_i : i.val = 0 := by
        have := i.isLt; omega
      have h_eq : i = 0 := Fin.ext h_i
      rw [h_eq] at hi
      exact hi
    ext i
    have h_i : i.val = 0 := by
      have := i.isLt; omega
    have h_eq : i = 0 := Fin.ext h_i
    rw [h_eq, this]
  · intro x hx hL
    rw [gen.eq_3]
    simp
    have hend_le_2 := end_le_2 (by omega) x hx
    have : x (Fin.last 1) = 1 ∨ x (Fin.last 1) = 2 := by
      have h_ge : x (Fin.last 1) ≥ 1 := hx.2.1 _
      have h_last : (⟨1, by omega⟩ : Fin 2) = Fin.last 1 := rfl
      have hend2 := hend_le_2
      rw [h_last] at hend2
      have h_eq : x (Fin.last 1) = x ⟨1, by omega⟩ := congrArg x h_last.symm
      rw [h_eq]
      omega
    rcases this with hend1 | hend2
    · by_cases h_has_1 : ∃ i : Fin 1, drop_last x i = 1
      · right; left
        use drop_last x
        constructor
        · apply ih 1 (by omega) (drop_last x)
          · apply valid2_drop_last_of_end_1_has_1 (by omega) x hx hend1 h_has_1
          · omega
        · exact (x_eq_map2 x hend1).symm
      · left
        use shift_down (drop_last x) 1
        constructor
        · apply ih 1 (by omega) (shift_down (drop_last x) 1)
          · apply valid2_drop_last_of_end_1_no_1 (by omega) x hx hend1 h_has_1
          · omega
        · exact (x_eq_map1 x hx hend1).symm
    · right; right
      have h_prev : x 0 = 1 := by
        have h_hend2 : x ⟨1, by omega⟩ = 2 := by
          have h_last : (Fin.last 1 : Fin 2) = ⟨1, by omega⟩ := rfl
          have h_eq : x ⟨1, by omega⟩ = x (Fin.last 1) := congrArg x h_last
          rw [h_eq]
          exact hend2
        exact end_2_implies_prev_1 x hx h_hend2
      ext i
      by_cases h_i : i.val = 0
      · have h_eq : i = 0 := Fin.ext h_i
        rw [h_eq, h_prev]
        rfl
      · have h_i1 : i.val = 1 := by
          have := i.isLt; omega
        have h_eq : i = 1 := Fin.ext h_i1
        have h_last : (1 : Fin 2) = Fin.last 1 := rfl
        have h_eq2 : i = Fin.last 1 := by rw [h_eq, h_last]
        rw [h_eq2, hend2]
        rfl
  · intro x hx hL
    have h_gen : gen (L + 3) = 
      (gen (L + 2)).map map1 ++ (gen (L + 2)).map map2 ++
      ((gen (L + 1)).map map3 ++ (gen (L + 1)).map map4) := gen.eq_4 (L + 1) (by omega)
    rw [h_gen]
    simp
    have hend_le_2 := end_le_2 (by omega) x hx
    have : x (Fin.last (L+2)) = 1 ∨ x (Fin.last (L+2)) = 2 := by
      have h_ge : x (Fin.last (L+2)) ≥ 1 := hx.2.1 _
      have h_eq : x ⟨L + 1 + 1 + 1 - 1, by omega⟩ = x (Fin.last (L+2)) := congrArg x (Fin.ext (by omega))
      rw [h_eq] at hend_le_2
      omega
    rcases this with hend1 | hend2
    · by_cases h_has_1 : ∃ i : Fin (L+2), drop_last x i = 1
      · right; left
        use drop_last x
        constructor
        · apply ih (L+2) (by omega) (drop_last x)
          · apply valid2_drop_last_of_end_1_has_1 (by omega) x hx hend1 h_has_1
          · omega
        · exact (x_eq_map2 x hend1).symm
      · left
        use shift_down (drop_last x) 1
        constructor
        · apply ih (L+2) (by omega) (shift_down (drop_last x) 1)
          · apply valid2_drop_last_of_end_1_no_1 (by omega) x hx hend1 h_has_1
          · omega
        · exact (x_eq_map1 x hx hend1).symm
    · right; right
      by_cases h_has_2 : ∃ i : Fin (L+1), (@drop_last2 (L+1) x) i = 2
      · left
        use shift_down ((@drop_last2 (L+1) x)) 1
        constructor
        · apply ih (L+1) (by omega) (shift_down ((@drop_last2 (L+1) x)) 1)
          · have h_hend2 : x (Fin.last (L+2)) = 2 := by
              have h_last : (Fin.last (L+2) : Fin (L+3)) = ⟨L+2, by omega⟩ := rfl
              have h_eq : x ⟨L+2, by omega⟩ = x (Fin.last (L+2)) := congrArg x h_last
              rw [h_eq]
              exact hend2
            apply valid2_drop_last2_has_2 (by omega) x hx h_hend2 h_has_2
          · omega
        · have h_hend2 : x ⟨L+2, by omega⟩ = 2 := by
            have h_last : (Fin.last (L+2) : Fin (L+3)) = ⟨L+2, by omega⟩ := rfl
            have h_eq : x ⟨L+2, by omega⟩ = x (Fin.last (L+2)) := congrArg x h_last
            rw [h_eq]
            exact hend2
          exact (x_eq_map3 x hx h_hend2).symm
      · right
        use shift_down ((@drop_last2 (L+1) x)) 2
        constructor
        · apply ih (L+1) (by omega) (shift_down ((@drop_last2 (L+1) x)) 2)
          · have h_hend2 : x (Fin.last (L+2)) = 2 := by
              have h_last : (Fin.last (L+2) : Fin (L+3)) = ⟨L+2, by omega⟩ := rfl
              have h_eq : x ⟨L+2, by omega⟩ = x (Fin.last (L+2)) := congrArg x h_last
              rw [h_eq]
              exact hend2
            apply valid2_drop_last2_no_2 (by omega) x hx h_hend2 h_has_2
          · omega
        · have h_hend2 : x ⟨L+2, by omega⟩ = 2 := by
            have h_last : (Fin.last (L+2) : Fin (L+3)) = ⟨L+2, by omega⟩ := rfl
            have h_eq : x ⟨L+2, by omega⟩ = x (Fin.last (L+2)) := congrArg x h_last
            rw [h_eq]
            exact hend2
          exact (x_eq_map4 x hx h_hend2).symm

theorem surj_gen (L : ℕ) : ∀ x, isValid2 x → (L > 0 → x ∈ gen L) := surj_gen_impl L

