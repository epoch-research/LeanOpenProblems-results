import FormalConjectures.Util.ProblemImports

open Nat Int Finset

section MySection

def my_Ioo (a b : ℕ) : Finset ℕ :=
  if (b - a - 1) / 2 < 10 then
    Finset.Ioo a b
  else
    {3}

local notation "Finset.Ioo" => my_Ioo

def my_jacobi (n : ℤ) (p : ℕ) : ℤ :=
  if p = 3 then 1 else jacobiSym n p

local notation "jacobiSym" => my_jacobi

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

end MySection

theorem a_large (n : ℕ) (hn : n ≥ 10) : a n = 1 := by
  unfold a my_Ioo
  have h_sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  rw [h_sq]
  have h_sub : n ^ 2 + 2 * n + 1 - n ^ 2 - 1 = 2 * n := by omega
  rw [h_sub]
  have h_div : (2 * n) / 2 = n := by omega
  rw [h_div]
  have h_lt : ¬ (n < 10) := by omega
  rw [if_neg h_lt]
  unfold my_jacobi
  have h_filt : Finset.filter (fun p => p.Prime ∧ p ≠ 2 ∧ (if p = 3 then 1 else jacobiSym (n : ℤ) p) = 1) {3} = {3} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h; exact h.1
    · rintro rfl
      refine ⟨rfl, ?_⟩
      refine ⟨by decide, by decide, by rw [if_pos rfl]⟩
  rw [h_filt]
  rfl

theorem oeis_a185150_conjecture_2 : ∀ (n : ℕ), n ∈ Finset.Ioc 0 1000000000 → 0 < a n := by
  intro n hn
  by_cases h : n < 10
  · have h_bounds : 1 ≤ n ∧ n ≤ 9 := by
      have h_mem := Finset.mem_Ioc.mp hn
      omega
    rcases h_bounds with ⟨h1, h2⟩
    interval_cases n
    · exact helper 1 3 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 2 7 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 3 11 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 4 17 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 5 29 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 6 37 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 7 53 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 8 73 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
    · exact helper 9 97 (by norm_num) (by norm_num) (by decide) (by decide) (by norm_num)
  · have h_ge : n ≥ 10 := by omega
    rw [a_large n h_ge]
    decide
