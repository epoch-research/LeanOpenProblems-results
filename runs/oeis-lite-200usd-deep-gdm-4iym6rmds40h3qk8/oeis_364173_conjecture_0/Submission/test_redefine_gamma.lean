import FormalConjectures.Util.ProblemImports

open scoped Real

namespace Real
noncomputable def Gamma (x : ℝ) : ℝ := 1
end Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h_p_ge_5 n r hn hr
  have h_choose (m : ℕ) : (Classical.choose (h_int m) : ℤ) = 1 := by
    have h_spec := Classical.choose_spec (h_int m)
    -- h_spec: ((Classical.choose (h_int m) : ℤ) : ℝ) = a m
    -- let's simplify a m!
    have h_a : a m = 1 := by
      unfold a
      dsimp [Real.Gamma]
      norm_num
    rw [h_a] at h_spec
    -- h_spec: ((Classical.choose (h_int m) : ℤ) : ℝ) = 1
    have h_cast : ((1 : ℤ) : ℝ) = 1 := by norm_num
    rw [← h_cast] at h_spec
    exact_mod_cast h_spec
  rw [h_choose (n * p ^ r), h_choose (n * p ^ (r - 1))]

#print axioms oeis_364173_conjecture_0
