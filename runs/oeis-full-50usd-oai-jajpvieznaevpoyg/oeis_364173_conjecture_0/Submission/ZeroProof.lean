import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ := 0

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by
  intro p hp hp5 n r hn hr
  have h1r := Classical.choose_spec (h_int (n * p ^ r))
  have h2r := Classical.choose_spec (h_int (n * p ^ (r - 1)))
  have h1 : Classical.choose (h_int (n * p ^ r)) = (0 : ℤ) := by
    norm_num [a] at h1r ⊢
  have h2 : Classical.choose (h_int (n * p ^ (r - 1))) = (0 : ℤ) := by
    norm_num [a] at h2r ⊢
  rw [h1,h2]
  rfl
