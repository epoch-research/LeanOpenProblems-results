import FormalConjecturesUtil

/-!
An exact obstruction at the quadratic carry scale. This is NOT a disproof
of Erdos 773. The four digit words have identical histograms and Eisenstein
coefficient conditions at 3, but their evaluated squares collide. Every digit
is bounded by H with H^2 = 363 * base.
-/
namespace Erdos773.BalancedCarry
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private def base (t : ℕ) : ℕ := 3 * (t + 39) ^ 2
private def height (t : ℕ) : ℕ := 33 * (t + 39)

private def words (t : ℕ) : Fin 4 → Fin 17 → ℕ :=
  ![![21,0,219,0,15*(t+39),0,219,0,309,0,33*(t+39),15*(t+39),0,33*(t+39),0,0,1],
    ![309,0,219,0,33*(t+39),0,219,0,21,0,15*(t+39),33*(t+39),0,15*(t+39),0,0,1],
    ![219,0,21,0,15*(t+39),0,309,0,219,0,33*(t+39),33*(t+39),0,15*(t+39),0,0,1],
    ![219,0,309,0,33*(t+39),0,21,0,219,0,15*(t+39),15*(t+39),0,33*(t+39),0,0,1]]

private def val (t : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 17, words t j i * (base t) ^ i.val

lemma leading (t : ℕ) (j : Fin 4) : words t j 16 = 1 := by
  fin_cases j <;> rfl

lemma constant_mod (t : ℕ) (j : Fin 4) : words t j 0 % 9 = 3 := by
  fin_cases j <;> norm_num [words]

lemma lower_divisible (t : ℕ) (j : Fin 4) (i : Fin 17) (hi : i.val < 16) :
    3 ∣ words t j i := by
  have h15 : 3 ∣ 15 * (t + 39) := dvd_mul_of_dvd_left (by decide) _
  have h33 : 3 ∣ 33 * (t + 39) := dvd_mul_of_dvd_left (by decide) _
  fin_cases j <;> fin_cases i <;> simp [words, h15, h33] at hi ⊢

lemma digit_sum (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, words t j i) = 769 + 96 * (t + 39) := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_norm (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, (words t j i) ^ 2) = 191845 + 2628 * (t + 39) ^ 2 := by
  fin_cases j <;> norm_num [words, Fin.sum_univ_succ, mul_pow] <;> omega

lemma histogram_perm (t : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words t j)) (List.ofFn (words t 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [words, List.ofFn_succ, List.count_cons] <;> omega

lemma digit_le_height (t : ℕ) (j : Fin 4) (i : Fin 17) :
    words t j i ≤ height t := by
  fin_cases j <;> fin_cases i <;> simp [words, height] <;> omega

lemma height_scale (t : ℕ) : height t ^ 2 = 363 * base t := by
  simp only [height, base]
  ring

lemma height_lt_half_base (t : ℕ) : 2 * height t < base t := by
  dsimp [height, base]
  nlinarith only [Nat.zero_le t, Nat.zero_le (t ^ 2)]

lemma digit_bounds (t : ℕ) (j : Fin 4) (i : Fin 17) :
    2 * words t j i < base t := by
  have h := digit_le_height t j i
  have hh := height_lt_half_base t
  omega

lemma digit_sum_lt_base (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, words t j i) < base t := by
  rw [digit_sum]
  dsimp [base]
  nlinarith only [Nat.zero_le t, Nat.zero_le (t ^ 2)]


lemma eventual_height_rpow_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℕ in Filter.atTop,
      (height t : ℝ) ≤ (base t : ℝ) ^ (1 / 2 + δ) := by
  have he : ∀ᶠ t : ℕ in Filter.atTop, (363 : ℝ) ≤ (t : ℝ) ^ (2 * δ) :=
    (Filter.tendsto_atTop.mp
      ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * δ)).comp
        tendsto_natCast_atTop_atTop)) 363
  filter_upwards [he] with t ht
  have hb : (0 : ℝ) < base t := by
    exact_mod_cast (show 0 < base t by dsimp [base]; positivity)
  have htb : (t : ℝ) ≤ base t := by
    exact_mod_cast (show t ≤ base t by
      dsimp [base]
      nlinarith only [Nat.zero_le t, Nat.zero_le (t ^ 2)])
  have hc : (363 : ℝ) ≤ (base t : ℝ) ^ (2 * δ) :=
    ht.trans (Real.rpow_le_rpow (by positivity) htb (by positivity))
  have hs : (height t : ℝ) ^ 2 = 363 * (base t : ℝ) := by
    exact_mod_cast height_scale t
  apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Real.rpow_nonneg hb.le _)
  calc
    (height t : ℝ) ^ 2 = 363 * (base t : ℝ) := hs
    _ ≤ (base t : ℝ) ^ (2 * δ) * (base t : ℝ) :=
      mul_le_mul_of_nonneg_right hc hb.le
    _ = ((base t : ℝ) ^ (1 / 2 + δ)) ^ 2 := by
      rw [← Real.rpow_mul_natCast hb.le]
      rw [show (1 / 2 + δ) * (2 : ℕ) = 2 * δ + 1 by push_cast; ring]
      rw [Real.rpow_add hb, Real.rpow_one]

lemma arbitrary_linear_separation (C : ℕ) :
    ∃ t : ℕ, C * height t < base t := by
  refine ⟨11 * C, ?_⟩
  dsimp [base, height]
  nlinarith only [Nat.zero_le C, Nat.zero_le (C ^ 2)]


private def polyValue (t : ℕ) (j : Fin 4) (x : ℤ) : ℤ :=
  ∑ i : Fin 17, (words t j i : ℤ) * x ^ i.val

lemma norm_difference_factor (t : ℕ) (x : ℤ) :
    polyValue t 0 x ^ 2 + polyValue t 1 x ^ 2 -
      polyValue t 2 x ^ 2 - polyValue t 3 x ^ 2 =
      216 * x ^ 15 * ((base t : ℤ) - x) * (x ^ 2 - 1) * (x ^ 6 - 1) := by
  simp [polyValue, words, Fin.sum_univ_succ, base]
  ring

lemma collision (t : ℕ) : val t 0 ^ 2 + val t 1 ^ 2 = val t 2 ^ 2 + val t 3 ^ 2 := by
  simp [val, words, Fin.sum_univ_succ, base]
  ring

lemma nontrivial (t : ℕ) : val t 0 ≠ val t 2 ∧ val t 0 ≠ val t 3 := by
  have hb : 309 < base t := by
    dsimp [base]
    nlinarith only [Nat.zero_le t, Nat.zero_le (t ^ 2)]
  have hm (j : Fin 4) : val t j % base t = words t j 0 := by
    fin_cases j <;> simp [val, Fin.sum_univ_succ, words, Nat.add_mod, Nat.mul_mod, Nat.pow_succ]
    all_goals exact Nat.mod_eq_of_lt (by omega)
  constructor <;> intro h
  · have hh : val t 0 % base t = _ := congrArg (· % base t) h
    dsimp only at hh
    rw [hm 0, hm 2] at hh
    change (21 : ℕ) = 219 at hh
    omega
  · have hh : val t 0 % base t = _ := congrArg (· % base t) h
    dsimp only at hh
    rw [hm 0, hm 3] at hh
    change (21 : ℕ) = 219 at hh
    omega

lemma not_sidon (t : ℕ) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : val t j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h
  · exact (nontrivial t).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial t).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)

lemma primitive_example :
    Nat.gcd (Nat.gcd (val 0 0) (val 0 1)) (Nat.gcd (val 0 2) (val 0 3)) = 3 := by
  decide +kernel

#print axioms norm_difference_factor
#print axioms eventual_height_rpow_bound
#print axioms arbitrary_linear_separation
#print axioms histogram_perm
#print axioms height_scale
#print axioms digit_bounds
#print axioms digit_sum_lt_base
#print axioms not_sidon
#print axioms primitive_example
end Erdos773.BalancedCarry
