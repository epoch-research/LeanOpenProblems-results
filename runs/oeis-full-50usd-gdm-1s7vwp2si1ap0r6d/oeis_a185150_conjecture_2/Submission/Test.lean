import FormalConjectures.Util.ProblemImports
open Nat Int Finset

def a (n : ℕ) : ℕ :=
  (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter (fun p : ℕ =>
    p.Prime ∧
    p ≠ 2 ∧
    jacobiSym (n : ℤ) p = 1
  ) |>.card

lemma helper (n : ℕ) (p : ℕ) (hp1 : n^2 < p) (hp2 : p < (n+1)^2) (h_prime : p.Prime) (h_ne : p ≠ 2) (h_jacobi : jacobiSym (n : ℤ) p = 1) : 0 < a n := by
  have h_mem : p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2) := Finset.mem_Ioo.mpr ⟨hp1, hp2⟩
  have h_filter : p ∈ Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)) :=
    Finset.mem_filter.mpr ⟨h_mem, ⟨h_prime, h_ne, h_jacobi⟩⟩
  have h_nonempty : (Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1) (Finset.Ioo (n ^ 2) ((n + 1) ^ 2))).Nonempty :=
    ⟨p, h_filter⟩
  exact Finset.card_pos.mpr h_nonempty

theorem test_a_1 : 0 < a 1 := helper 1 3 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)


theorem test_a_2 : 0 < a 2 := helper 2 7 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)

theorem test_a_decide : ∀ (n : ℕ), n ∈ Finset.Ioc 0 2 → 0 < a n := by
  intro n hn
  rw [Finset.mem_Ioc] at hn
  rcases hn with ⟨h1, h2⟩
  interval_cases n
  · exact test_a_1
  · exact test_a_2
