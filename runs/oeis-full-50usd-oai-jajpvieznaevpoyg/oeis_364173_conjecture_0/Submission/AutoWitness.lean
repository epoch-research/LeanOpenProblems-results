import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

example
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp hge n r hn hr
  let x : ℤ := Classical.choose (h_int (n * p ^ r))
  let y : ℤ := Classical.choose (h_int (n * p ^ (r-1)))
  have hx : (x : ℝ) = a (n * p ^ r) := by simpa [x] using Classical.choose_spec (h_int (n * p ^ r))
  have hy : (y : ℝ) = a (n * p ^ (r-1)) := by simpa [y] using Classical.choose_spec (h_int (n * p ^ (r-1)))
  change x ≡ y [ZMOD ((p : ℤ) ^ (3 * r))]
  try omega
  try aesop (add simp [Int.ModEq, a, Set.mem_range])
  try grind [Int.ModEq]
  all_goals sorry
