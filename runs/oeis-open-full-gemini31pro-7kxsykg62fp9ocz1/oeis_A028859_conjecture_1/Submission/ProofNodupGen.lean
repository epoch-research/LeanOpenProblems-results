import Submission.ProofNodup
import Submission.ProofValid

theorem gen_valid (L : ℕ) : ∀ x ∈ gen L, ValidGen x := by
  induction' L using Nat.strongRecOn with L ih
  rcases L with _ | _ | _ | L
  · intro x hx
    rw [gen.eq_1] at hx
    simp at hx
  · intro x hx
    rw [gen.eq_2] at hx
    simp at hx
    rw [hx]
    constructor
    · intro i; exact Nat.zero_lt_one
    · use ⟨0, by omega⟩
  · intro x hx
    rw [gen.eq_3] at hx
    simp at hx
    rcases hx with hx | hx | hx
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map1
      apply ih 1 (by omega) y hy
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map2
      apply ih 1 (by omega) y hy
    · rw [hx]
      constructor
      · intro i
        by_cases hi : i.val < 1
        · have h1 : i = Fin.castSucc ⟨0, by omega⟩ := Fin.ext (by have : (Fin.castSucc (⟨0, by omega⟩ : Fin 1)).val = 0 := rfl; omega)
          rw [h1, Fin.snoc_castSucc]
          exact Nat.zero_lt_one
        · have h2 : i.val < 2 := i.isLt
          have h1 : i = Fin.last 1 := Fin.ext (by have : (Fin.last 1).val = 1 := rfl; omega)
          rw [h1, Fin.snoc_last]
          exact by decide
      · use Fin.castSucc ⟨0, by omega⟩
        rw [Fin.snoc_castSucc]
  · intro x hx
    have h_gen : gen (L + 3) = 
      (gen (L + 2)).map map1 ++ (gen (L + 2)).map map2 ++
      ((gen (L + 1)).map map3 ++ (gen (L + 1)).map map4) := gen.eq_4 (L + 1) (by intro h; omega)
    rw [h_gen] at hx
    simp at hx
    rcases hx with hx | hx | hx | hx
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map1
      apply ih (L + 2) (by omega) y hy
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map2
      apply ih (L + 2) (by omega) y hy
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map3
      apply ih (L + 1) (by omega) y hy
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      apply valid_map4
      apply ih (L + 1) (by omega) y hy
