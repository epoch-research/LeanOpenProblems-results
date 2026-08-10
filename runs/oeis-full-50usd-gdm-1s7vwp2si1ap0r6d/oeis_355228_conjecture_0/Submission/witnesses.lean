import FormalConjectures.Util.ProblemImports
open Finset Nat Set

def S_a (n : ℕ) : Set ℕ :=
  { m : ℕ | 0 < m ∧
    ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧
      D.card = n ∧
      D.sum id = m ∧
      D.lcm id = m }

noncomputable def a (n : ℕ) : ℕ := sInf (S_a n)
lemma a_eq_sInf_S_a (n : ℕ) : a n = sInf (S_a n) := rfl
lemma a_13_le : a 13 ≤ 180 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 180 ∈ S_a 13 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 9, 10, 12, 18, 20, 30, 60}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_14_le : a 14 ≤ 180 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 180 ∈ S_a 14 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 45}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_15_le : a 15 ≤ 240 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 240 ∈ S_a 15 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 20, 30, 48, 60}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_16_le : a 16 ≤ 360 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 360 ∈ S_a 16 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 30, 45, 72, 120}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_17_le : a 17 ≤ 360 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 360 ∈ S_a 17 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 40, 45, 72, 90}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_18_le : a 18 ≤ 360 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 360 ∈ S_a 18 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 30, 40, 45, 60, 72}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_19_le : a 19 ≤ 360 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 360 ∈ S_a 19 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 72}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_20_le : a 20 ≤ 672 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 672 ∈ S_a 20 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 6, 7, 8, 12, 14, 16, 21, 24, 28, 32, 42, 48, 56, 84, 96, 168}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_21_le : a 21 ≤ 720 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 720 ∈ S_a 21 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 72, 144, 240}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_22_le : a 22 ≤ 720 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 720 ∈ S_a 22 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 45, 60, 72, 144, 180}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_23_le : a 23 ≤ 720 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 720 ∈ S_a 23 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 30, 36, 40, 45, 72, 80, 120, 144}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_24_le : a 24 ≤ 840 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 840 ∈ S_a 24 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 30, 35, 42, 56, 84, 105, 140, 168}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_25_le : a 25 ≤ 840 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 840 ∈ S_a 25 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 20, 21, 24, 28, 35, 40, 42, 56, 60, 70, 84, 105, 168}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_26_le : a 26 ≤ 1260 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1260 ∈ S_a 26 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 90, 180, 252, 315}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_27_le : a 27 ≤ 1260 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1260 ∈ S_a 27 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 180, 420}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_28_le : a 28 ≤ 1260 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1260 ∈ S_a 28 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 84, 90, 105, 180, 315}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_29_le : a 29 ≤ 1260 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1260 ∈ S_a 29 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 28, 30, 35, 36, 42, 45, 60, 63, 70, 84, 90, 140, 180, 210}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_30_le : a 30 ≤ 1680 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1680 ∈ S_a 30 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 80, 105, 112, 120, 336, 420}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_31_le : a 31 ≤ 1680 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1680 ∈ S_a 31 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 105, 120, 168, 210, 420}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

lemma a_32_le : a 32 ≤ 1680 := by
  rw [a_eq_sInf_S_a]
  have h_mem : 1680 ∈ S_a 32 := by
    dsimp [S_a]
    refine ⟨by decide, ?_⟩
    use {1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 16, 20, 21, 24, 28, 30, 35, 40, 42, 48, 56, 60, 70, 80, 84, 105, 120, 168, 210, 336}
    refine ⟨?_, by decide, by decide, by decide⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact Nat.sInf_le h_mem

