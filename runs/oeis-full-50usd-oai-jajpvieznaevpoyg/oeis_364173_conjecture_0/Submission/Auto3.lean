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
  intro p hp hp5 n r hn hr
  have hpowne : p ^ r ≠ p ^ (r - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr) with ⟨s, rfl⟩
    simp only [Nat.succ_sub_one]
    intro h
    rw [pow_succ'] at h
    have h' : p * p ^ s = 1 * p ^ s := by simpa using h
    have hp1 : p = 1 := Nat.mul_right_cancel (pow_pos hp.pos s) h'
    omega
  grind
