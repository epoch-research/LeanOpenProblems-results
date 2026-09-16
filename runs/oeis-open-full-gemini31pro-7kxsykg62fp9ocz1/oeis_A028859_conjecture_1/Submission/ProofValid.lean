import Submission.ProofLength
import Mathlib


theorem valid_map1 {L : ℕ} {x : Fin L → ℕ} (hx : ValidGen x) : ValidGen (map1 x) := by
  constructor
  · intro i
    by_cases h : i.val < L
    · have h1 : i = Fin.castSucc ⟨i.val, h⟩ := Fin.ext rfl
      rw [h1, map1, Fin.snoc_castSucc]
      change x ⟨i.val, h⟩ + 1 > 0
      have hx_pos := hx.1 ⟨i.val, h⟩
      omega
    · have h1 : i = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
      rw [h1, map1, Fin.snoc_last]
      omega
  · use Fin.last L
    rw [map1, Fin.snoc_last]

theorem valid_map2 {L : ℕ} {x : Fin L → ℕ} (hx : ValidGen x) : ValidGen (map2 x) := by
  constructor
  · intro i
    by_cases h : i.val < L
    · have h1 : i = Fin.castSucc ⟨i.val, h⟩ := Fin.ext rfl
      rw [h1, map2, Fin.snoc_castSucc]
      have hx_pos := hx.1 ⟨i.val, h⟩
      omega
    · have h1 : i = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
      rw [h1, map2, Fin.snoc_last]
      omega
  · use Fin.last L
    rw [map2, Fin.snoc_last]

theorem valid_map3 {L : ℕ} {x : Fin L → ℕ} (hx : ValidGen x) : ValidGen (map3 x) := by
  constructor
  · intro i
    by_cases h : i.val < L + 1
    · have h1 : i = Fin.castSucc ⟨i.val, h⟩ := Fin.ext rfl
      rw [h1, map3, Fin.snoc_castSucc]
      by_cases h2 : (⟨i.val, h⟩ : Fin (L + 1)).val < L
      · have h3 : (⟨i.val, h⟩ : Fin (L + 1)) = Fin.castSucc ⟨i.val, h2⟩ := Fin.ext rfl
        rw [h3, Fin.snoc_castSucc]
        change x ⟨i.val, h2⟩ + 1 > 0
        have hx_pos := hx.1 ⟨i.val, h2⟩
        omega
      · have h3 : (⟨i.val, h⟩ : Fin (L + 1)) = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
        rw [h3, Fin.snoc_last]
        omega
    · have h1 : i = Fin.last (L + 1) := Fin.ext (by have : (Fin.last (L + 1)).val = L + 1 := rfl; omega)
      rw [h1, map3, Fin.snoc_last]
      omega
  · use Fin.castSucc (Fin.last L)
    rw [map3, Fin.snoc_castSucc, Fin.snoc_last]

theorem valid_map4 {L : ℕ} {x : Fin L → ℕ} (hx : ValidGen x) : ValidGen (map4 x) := by
  constructor
  · intro i
    by_cases h : i.val < L + 1
    · have h1 : i = Fin.castSucc ⟨i.val, h⟩ := Fin.ext rfl
      rw [h1, map4, Fin.snoc_castSucc]
      by_cases h2 : (⟨i.val, h⟩ : Fin (L + 1)).val < L
      · have h3 : (⟨i.val, h⟩ : Fin (L + 1)) = Fin.castSucc ⟨i.val, h2⟩ := Fin.ext rfl
        rw [h3, Fin.snoc_castSucc]
        change x ⟨i.val, h2⟩ + 2 > 0
        have hx_pos := hx.1 ⟨i.val, h2⟩
        omega
      · have h3 : (⟨i.val, h⟩ : Fin (L + 1)) = Fin.last L := Fin.ext (by have : (Fin.last L).val = L := rfl; omega)
        rw [h3, Fin.snoc_last]
        omega
    · have h1 : i = Fin.last (L + 1) := Fin.ext (by have : (Fin.last (L + 1)).val = L + 1 := rfl; omega)
      rw [h1, map4, Fin.snoc_last]
      omega
  · use Fin.castSucc (Fin.last L)
    rw [map4, Fin.snoc_castSucc, Fin.snoc_last]
