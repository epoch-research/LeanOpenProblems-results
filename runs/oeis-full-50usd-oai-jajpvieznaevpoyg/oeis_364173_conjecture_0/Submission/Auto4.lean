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
  have hmulne : n * p ^ r ≠ n * p ^ (r - 1) := by
    intro h
    exact hpowne (Nat.mul_left_cancel (by omega : 0 < n) h)
  have hrpowne : r ≠ p ^ r := by
    have hp2 : 2 ≤ p := hp.two_le
    have hle : r < p ^ r := by
      -- p^r >= 2^r > r for r>0
      have h2pow : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp2 r
      have hrlt2 : r < 2 ^ r := Nat.lt_two_pow_self (by omega : 0 < r)
      exact lt_of_lt_of_le hrlt2 h2pow
    omega
  grind
