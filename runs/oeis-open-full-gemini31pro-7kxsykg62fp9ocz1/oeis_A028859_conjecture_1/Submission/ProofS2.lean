import Submission.ProofS
import Submission.ProofNodupGen
import Mathlib

def isValid2 {L : ℕ} (σ : Fin L → ℕ) : Prop :=
  L > 0 ∧
  (∀ i, σ i > 0) ∧
  let max_val := Finset.sup Finset.univ σ
  (∀ k, 1 ≤ k ∧ k ≤ max_val → ∃ i, σ i = k) ∧
  (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)

theorem valid2_has_1 {L : ℕ} (x : Fin L → ℕ) (hx : isValid2 x) : ∃ i, x i = 1 := by
  haveI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hx.1
  have h_ne : (Finset.univ : Finset (Fin L)).Nonempty := Finset.univ_nonempty
  have ⟨i, _, h_sup⟩ := Finset.exists_mem_eq_sup Finset.univ h_ne x
  have h_max_ge_1 : 1 ≤ Finset.sup Finset.univ x := by
    have : x i ≤ Finset.sup Finset.univ x := Finset.le_sup (Finset.mem_univ i)
    have : x i > 0 := hx.2.1 i
    omega
  exact hx.2.2.1 1 (by omega)

theorem isValid2_map1 {L : ℕ} (x : Fin L → ℕ) (hx : isValid2 x) : isValid2 (map1 x) := by
  constructor
  · omega
  · constructor
    · exact (valid_map1 ⟨hx.2.1, valid2_has_1 x hx⟩).1
    · constructor
      · exact image_map1 hx.1 x hx.2.2.1
      · exact cond3_map1 x hx.2.2.2

theorem isValid2_map2 {L : ℕ} (x : Fin L → ℕ) (hx : isValid2 x) : isValid2 (map2 x) := by
  constructor
  · omega
  · constructor
    · exact (valid_map2 ⟨hx.2.1, valid2_has_1 x hx⟩).1
    · constructor
      · exact image_map2 x (valid2_has_1 x hx) hx.2.2.1
      · exact cond3_map2 x hx.2.1 hx.2.2.2

theorem isValid2_map3 {L : ℕ} (x : Fin L → ℕ) (hx : isValid2 x) : isValid2 (map3 x) := by
  constructor
  · omega
  · constructor
    · exact (valid_map3 ⟨hx.2.1, valid2_has_1 x hx⟩).1
    · constructor
      · exact image_map3 hx.1 x hx.2.1 hx.2.2.1
      · exact cond3_map3 x hx.2.1 hx.2.2.2

theorem isValid2_map4 {L : ℕ} (x : Fin L → ℕ) (hx : isValid2 x) : isValid2 (map4 x) := by
  constructor
  · omega
  · constructor
    · exact (valid_map4 ⟨hx.2.1, valid2_has_1 x hx⟩).1
    · constructor
      · exact image_map4 hx.1 x hx.2.1 (valid2_has_1 x hx) hx.2.2.1
      · exact cond3_map4 x hx.2.1 hx.2.2.2

theorem gen_is_valid2 (L : ℕ) (hL : L > 0) : ∀ x ∈ gen L, isValid2 x := by
  induction' L using Nat.strongRecOn with L ih
  rcases L with _ | _ | _ | L
  · omega
  · intro x hx
    rw [gen.eq_2] at hx
    simp at hx
    rw [hx]
    constructor
    · exact hL
    · constructor
      · intro i; exact Nat.zero_lt_one
      · constructor
        · intro k hk
          have : Finset.sup Finset.univ (fun (_ : Fin 1) => 1) = 1 := by
            have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
            rw [this, Finset.sup_singleton]
          rw [this] at hk
          have : k = 1 := by omega
          rw [this]
          use 0
        · intro i j hij hneq
          omega
  · intro x hx
    rw [gen.eq_3] at hx
    simp at hx
    rcases hx with hx | hx | hx
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map1 y (ih 1 (by omega) (by omega) y hy)
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map2 y (ih 1 (by omega) (by omega) y hy)
    · rw [hx]
      constructor
      · exact hL
      · constructor
        · intro i; fin_cases i <;> exact by decide
        · constructor
          · intro k hk
            have : Finset.sup Finset.univ (Fin.snoc (fun _ : Fin 1 => 1) 2 : Fin 2 → ℕ) = 2 := by
              have h1 : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
              rw [h1, Finset.sup_insert, Finset.sup_singleton]
              rfl
            rw [this] at hk
            by_cases h : k = 2
            · use 1; rw [h]; rfl
            · use ⟨0, by omega⟩
              have h1 : k = 1 := by omega
              have : (Fin.snoc (fun _ : Fin 1 => 1) 2 : Fin 2 → ℕ) ⟨0, by omega⟩ = 1 := rfl
              rw [this, h1]
          · intro i j hij hneq
            omega
  · intro x hx
    have h_gen : gen (L + 3) = 
      (gen (L + 2)).map map1 ++ (gen (L + 2)).map map2 ++
      ((gen (L + 1)).map map3 ++ (gen (L + 1)).map map4) := gen.eq_4 (L + 1) (by intro h; omega)
    rw [h_gen] at hx
    simp at hx
    rcases hx with hx | hx | hx | hx
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map1 y (ih (L+2) (by omega) (by omega) y hy)
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map2 y (ih (L+2) (by omega) (by omega) y hy)
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map3 y (ih (L+1) (by omega) (by omega) y hy)
    · rcases hx with ⟨y, hy, hy2⟩
      rw [←hy2]
      exact isValid2_map4 y (ih (L+1) (by omega) (by omega) y hy)
