import FormalConjectures.Util.ProblemImports

open Real Nat

/--
A364176 term:
$$a(n) = \frac{(15n)! (5n/2)! (2n)!}{(15n/2)! (6n)! (5n)! n!}$$
where integer factorials are evaluated using `Nat.factorial`, and fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n.cast
  let num_int_15 : ℝ := (15 * n).factorial.cast
  let num_int_2 : ℝ := (2 * n).factorial.cast
  let num_frac_5_halves : ℝ := Real.Gamma (5 * n_r / 2 + 1)

  let den_frac_15_halves : ℝ := Real.Gamma (15 * n_r / 2 + 1)
  let den_int_6 : ℝ := (6 * n).factorial.cast
  let den_int_5 : ℝ := (5 * n).factorial.cast
  let den_int_1 : ℝ := n.factorial.cast

  (num_int_15 * num_frac_5_halves * num_int_2) /
  (den_frac_15_halves * den_int_6 * den_int_5 * den_int_1)

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: The sequence a(n) is only conjecturally integer-valued. We formalize the congruence as divisibility of real numbers, requiring that the sequence terms are indeed integers.
-/
lemma real_div_range_int_cast (a b : ℤ) (hb : b ≠ 0) :
  (a : ℝ) / (b : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) ↔ b ∣ a := by
  constructor
  · rintro ⟨c, hc⟩
    use c
    have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have h_eq : (a : ℝ) = (b : ℝ) * (c : ℝ) := by
      rw [hc, mul_div_cancel₀ (a : ℝ) hb_real]
    have h_eq2 : (a : ℝ) = ((b * c : ℤ) : ℝ) := by
      rw [Int.cast_mul]
      exact h_eq
    exact_mod_cast h_eq2
  · rintro ⟨c, rfl⟩
    use c
    have hb_real : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    rw [Int.cast_mul]
    exact (mul_div_cancel_left₀ (c : ℝ) hb_real).symm


lemma df_5 (k : ℕ) : (10 * k + 5).doubleFactorial = (10 * k + 5) * (10 * k + 3) * (10 * k + 1).doubleFactorial := by
  have h1 : 10 * k + 5 = (10 * k + 3) + 2 := by omega
  rw [h1, doubleFactorial_add_two]
  have h2 : 10 * k + 3 = (10 * k + 1) + 2 := by omega
  rw [h2, doubleFactorial_add_two]
  ring

lemma df_15 (k : ℕ) : (30 * k + 15).doubleFactorial =
  (30 * k + 15) * (30 * k + 13) * (30 * k + 11) * (30 * k + 9) * (30 * k + 7) * (30 * k + 5) * (30 * k + 3) * (30 * k + 1).doubleFactorial := by
  have h1 : 30 * k + 15 = (30 * k + 13) + 2 := by omega
  rw [h1, doubleFactorial_add_two]
  have h2 : 30 * k + 13 = (30 * k + 11) + 2 := by omega
  rw [h2, doubleFactorial_add_two]
  have h3 : 30 * k + 11 = (30 * k + 9) + 2 := by omega
  rw [h3, doubleFactorial_add_two]
  have h4 : 30 * k + 9 = (30 * k + 7) + 2 := by omega
  rw [h4, doubleFactorial_add_two]
  have h5 : 30 * k + 7 = (30 * k + 5) + 2 := by omega
  rw [h5, doubleFactorial_add_two]
  have h6 : 30 * k + 5 = (30 * k + 3) + 2 := by omega
  rw [h6, doubleFactorial_add_two]
  have h7 : 30 * k + 3 = (30 * k + 1) + 2 := by omega
  rw [h7, doubleFactorial_add_two]
  ring

lemma a_even (m : ℕ) : a (2 * m) =
  (((30 * m).factorial : ℝ) * ((5 * m).factorial : ℝ) * ((4 * m).factorial : ℝ)) /
  (((15 * m).factorial : ℝ) * ((12 * m).factorial : ℝ) * ((10 * m).factorial : ℝ) * ((2 * m).factorial : ℝ)) := by
  dsimp [a]
  have h1 : 5 * ↑(2 * m) / 2 + 1 = ((5 * m : ℕ) + 1 : ℝ) := by
    push_cast
    ring
  have h2 : 15 * ↑(2 * m) / 2 + 1 = ((15 * m : ℕ) + 1 : ℝ) := by
    push_cast
    ring
  rw [h1, h2]
  rw [Real.Gamma_nat_eq_factorial (5 * m), Real.Gamma_nat_eq_factorial (15 * m)]
  have h3 : 15 * (2 * m) = 30 * m := by ring
  have h4 : 2 * (2 * m) = 4 * m := by ring
  have h5 : 6 * (2 * m) = 12 * m := by ring
  have h6 : 5 * (2 * m) = 10 * m := by ring
  have h7 : 2 * m = 2 * m := by rfl
  rw [h3, h4, h5, h6, h7]

lemma a_odd (k : ℕ) : a (2 * k + 1) =
  (((15 * (2 * k + 1)).factorial : ℝ) * ((10 * k + 5).doubleFactorial : ℝ) * (2 ^ (10 * k + 5) : ℝ) * ((2 * (2 * k + 1)).factorial : ℝ)) /
  (((30 * k + 15).doubleFactorial : ℝ) * ((6 * (2 * k + 1)).factorial : ℝ) * ((5 * (2 * k + 1)).factorial : ℝ) * ((2 * k + 1).factorial : ℝ)) := by
  dsimp [a]
  have h1 : 5 * ↑(2 * k + 1) / 2 + 1 = 5 * (k : ℝ) + 3 + 1 / 2 := by
    push_cast; linarith
  have h2 : 15 * ↑(2 * k + 1) / 2 + 1 = 15 * (k : ℝ) + 8 + 1 / 2 := by
    push_cast; linarith
  rw [h1, h2]
  have h_cast1 : 5 * (k : ℝ) + 3 = ↑(5 * k + 3) := by push_cast; rfl
  have h_cast2 : 15 * (k : ℝ) + 8 = ↑(15 * k + 8) := by push_cast; rfl
  rw [h_cast1, h_cast2]
  rw [Real.Gamma_nat_add_half (5 * k + 3), Real.Gamma_nat_add_half (15 * k + 8)]
  have h3 : 2 * (5 * k + 3) - 1 = 10 * k + 5 := by omega
  have h4 : 2 * (15 * k + 8) - 1 = 30 * k + 15 := by omega
  rw [h3, h4]
  have h_df5 : ((10 * k + 5).doubleFactorial : ℝ) = ((10 * k + 5 : ℕ) : ℝ) * ((10 * k + 3 : ℕ) : ℝ) * ((10 * k + 1).doubleFactorial : ℝ) := by
    exact_mod_cast df_5 k
  have h_df15 : ((30 * k + 15).doubleFactorial : ℝ) =
    ((30 * k + 15 : ℕ) : ℝ) * ((30 * k + 13 : ℕ) : ℝ) * ((30 * k + 11 : ℕ) : ℝ) * ((30 * k + 9 : ℕ) : ℝ) *
    ((30 * k + 7 : ℕ) : ℝ) * ((30 * k + 5 : ℕ) : ℝ) * ((30 * k + 3 : ℕ) : ℝ) * ((30 * k + 1).doubleFactorial : ℝ) := by
    exact_mod_cast df_15 k
  rw [h_df5, h_df15]
  have h_pow : (2 : ℝ) ^ (15 * k + 8) = 2 ^ (10 * k + 5) * 2 ^ (5 * k + 3) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h_pow]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  push_cast
  ring

set_option linter.unusedVariables false

lemma a_one : a 1 = 7168 := by
  dsimp [a]
  norm_num
  have h72 : Gamma (7 / 2) = Gamma ((3 : ℕ) + 1 / 2) := by congr 1; norm_num
  have h172 : Gamma (17 / 2) = Gamma ((8 : ℕ) + 1 / 2) := by congr 1; norm_num
  rw [h72, h172]
  rw [Real.Gamma_nat_add_half 3, Real.Gamma_nat_add_half 8]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  norm_num


lemma a_three : a 3 = 4488240824320 := by
  dsimp [a]
  norm_num
  have h17_2 : Gamma (17 / 2) = Gamma ((8 : ℕ) + 1 / 2) := by congr 1; norm_num
  have h47_2 : Gamma (47 / 2) = Gamma ((23 : ℕ) + 1 / 2) := by congr 1; norm_num
  rw [h17_2, h47_2]
  rw [Real.Gamma_nat_add_half 8, Real.Gamma_nat_add_half 23]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  norm_num


lemma a_two : a 2 = 168043980 := by
  dsimp [a]
  norm_num


lemma a_four : a 4 = 126694219977836700 := by
  dsimp [a]
  norm_num


lemma a_five_val : a 5 = 3688258943632086663168 := by
  dsimp [a]
  norm_num
  have h27_2 : Gamma (27 / 2) = Gamma ((13 : ℕ) + 1 / 2) := by congr 1; norm_num
  have h77_2 : Gamma (77 / 2) = Gamma ((38 : ℕ) + 1 / 2) := by congr 1; norm_num
  rw [h27_2, h77_2]
  rw [Real.Gamma_nat_add_half 13, Real.Gamma_nat_add_half 38]
  have hpi : √π ≠ 0 := by positivity
  field_simp
  norm_num


theorem oeis_364176_conjecture_0
  (p : ℕ) (hp : Nat.Prime p) (hp_ge_five : 5 ≤ p)
  (n r : ℕ) (hn_pos : 0 < n) (hr_pos : 0 < r) :
  -- Define the arguments for a, ensuring r-1 is safe (guaranteed by hr_pos)
  let k_r := n * p ^ r
  let k_r_minus_1 := n * p ^ (r - 1)
  -- Define the modulus as a real number
  let modulus : ℝ := (p ^ (3 * r)).cast
  -- The premise is the conjectural integrality of the two relevant terms, i.e., they are in the image of Int.cast
  (a k_r ∈ Set.range (Int.cast : ℤ → ℝ)) ∧ (a k_r_minus_1 ∈ Set.range (Int.cast : ℤ → ℝ)) →
  -- The conclusion is the divisibility condition: modulus divides the difference.
  -- This is formalized as the quotient being an integer.
  (a k_r - a k_r_minus_1) / modulus ∈ Set.range (Int.cast : ℤ → ℝ)
:= by
  intros k_r k_r_minus_1 modulus h
  have h1 := h.left
  have h2 := h.right
  rcases h1 with ⟨w, hw⟩
  rcases h2 with ⟨w_1, hw_1⟩
  have h_mod : modulus = ((p ^ (3 * r) : ℤ) : ℝ) := by
    dsimp [modulus]
    push_cast
    rfl
  rw [← hw, ← hw_1, h_mod]
  have h_sub : (w : ℝ) - (w_1 : ℝ) = ((w - w_1 : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [h_sub]
  have h_nz : (p ^ (3 * r) : ℤ) ≠ 0 := by
    intro h_zero
    have hp_nz : p ≠ 0 := by
      omega
    have h_pow : p ^ (3 * r) ≠ 0 := by
      exact pow_ne_zero (3 * r) hp_nz
    exact h_pow (by exact_mod_cast h_zero)
  rw [real_div_range_int_cast (w - w_1) (p ^ (3 * r)) h_nz]
  have h_dec : Decidable ((p ^ (3 * r) : ℤ) ∣ w - w_1) := Classical.dec _
  by_cases h_div : (p ^ (3 * r) : ℤ) ∣ w - w_1
  · exact h_div
  · -- Under the assumption that the divisibility is false, can we classically bypass it?
    sorry
