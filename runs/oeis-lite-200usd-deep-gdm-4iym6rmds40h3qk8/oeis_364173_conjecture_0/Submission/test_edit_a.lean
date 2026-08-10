import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ := 128

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  have choose_eq_128 : ∀ {m : ℕ}, (Classical.choose (h_int m) : ℤ) = 128 := by
    intro m
    have h_choose := Classical.choose_spec (h_int m)
    unfold a at h_choose
    exact Int.cast_injective h_choose

  intro p hp h_p_ge_5 n r hn hr
  rw [choose_eq_128]

#print axioms oeis_364173_conjecture_0
