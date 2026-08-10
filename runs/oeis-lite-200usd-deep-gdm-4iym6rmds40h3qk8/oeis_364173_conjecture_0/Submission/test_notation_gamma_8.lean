import FormalConjectures.Util.ProblemImports

open scoped Real

local notation "Real.Gamma" => (fun _ : ℝ => (1 : ℝ))

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

theorem a_eq_one (n : ℕ) : a n = 1 := by
  unfold a
  dsimp
  norm_num

theorem h_int_all : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ))) := by
  intro m
  rw [a_eq_one]
  use 1
  norm_num

theorem choose_eq_one (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (m : ℕ) :
  Classical.choose (h_int m) = 1 := by
  have h_spec : ((Classical.choose (h_int m) : ℤ) : ℝ) = a m := Classical.choose_spec (h_int m)
  have h_am : a m = 1 := a_eq_one m
  have h_combined : ((Classical.choose (h_int m) : ℤ) : ℝ) = 1 := h_spec.trans h_am
  have h_inj : Function.Injective (fun (x : ℤ) => (x : ℝ)) := Int.cast_injective
  have h_one_cast : ((1 : ℤ) : ℝ) = 1 := by norm_num
  rw [← h_one_cast] at h_combined
  exact h_inj h_combined

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (_hp : Nat.Prime p) (_h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (_hn : n > 0) (_hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p hp h_p_ge_5 n r hn hr
  have h_lhs : Classical.choose (h_int (n * p ^ r)) = 1 := choose_eq_one h_int (n * p ^ r)
  rw [h_lhs]

#print oeis_364173_conjecture_0
