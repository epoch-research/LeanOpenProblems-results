import Mathlib

noncomputable def A000224 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

theorem oeis_a000224_conjecture_ordowski {n : ℕ} (h_n : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  sorry

theorem oeis_a000224_conjecture_ordowski.disproof : ¬ (type_of% @oeis_a000224_conjecture_ordowski) := sorry
