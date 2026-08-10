import FormalConjectures.Util.ProblemImports
open scoped Real
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

-- probe: inspect what h_int gives and whether choose_spec pins the value
example (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (m : ℕ) :
    ((Classical.choose (h_int m) : ℤ) : ℝ) = a m := Classical.choose_spec (h_int m)

-- probe: is the modeq goal reachable trivially for r? try to see structure
example (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))))
    (p : ℕ) (hp : Nat.Prime p) (h5 : 5 ≤ p) (n r : ℕ) (hn : n>0) (hr : r>0) :
    (Classical.choose (h_int (n * p ^ r)) : ℤ) ≡ (Classical.choose (h_int (n * p ^ (r-1))) : ℤ) [ZMOD ((p:ℤ)^(3*r))] := by
  unfold Int.ModEq
  sorry
