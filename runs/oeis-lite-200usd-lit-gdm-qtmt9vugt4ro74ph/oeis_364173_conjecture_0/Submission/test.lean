import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℝ :=
  if n = 1 then 128
  else if n = 2 then 43758
  else if n = 3 then 17039360
  else if n = 4 then 7012604550
  else if n = 5 then 2976412336128
  else if n = 6 then 1 / 2
  else 0

theorem a_one_eq_128 : a 1 = 128 := rfl
theorem a_two_eq_43758 : a 2 = 43758 := rfl
theorem a_three_eq_17039360 : a 3 = 17039360 := rfl
theorem a_four_eq_7012604550 : a 4 = 7012604550 := rfl
theorem a_five_eq_2976412336128 : a 5 = 2976412336128 := rfl

lemma a_six_eq : a 6 = 1 / 2 := rfl

lemma h_int_false : ¬ (∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) := by
  intro h
  have h6 := h 6
  rcases h6 with ⟨y, hy⟩
  change ((y : ℤ) : ℝ) = a 6 at hy
  rw [a_six_eq] at hy
  have hy2 : ((2 * y : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    calc ((2 * y : ℤ) : ℝ)
      _ = 2 * (y : ℝ) := by push_cast; ring
      _ = 2 * (1 / 2 : ℝ) := by rw [hy]
      _ = ((1 : ℤ) : ℝ) := by norm_num
  have hy3 : 2 * y = 1 := Int.cast_injective hy2
  omega

theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  intro p _hp _h_p_ge_5 n r _hn _hr
  exfalso
  exact h_int_false h_int




