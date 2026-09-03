import Submission.FactorialClearingIndex

/-!
# Factorial clearing of fixed-length reciprocal blocks

This auxiliary result allows cancellation within a finite sum. It is not a
proof or disproof of the conjecture in `Spec.lean`.
-/

namespace FiniteBlockClearing

open Filter

lemma integral_product_sum {ι : Type*} (s : Finset ι) (d : ι → ℤ)
    (hd : ∀ i ∈ s, d i ≠ 0) :
    ∃ z : ℤ, ((∏ i ∈ s, d i : ℤ) : ℚ) * (∑ i ∈ s, 1 / (d i : ℚ)) = z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨z, hz⟩ := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    refine ⟨(∏ i ∈ s, d i) + d a * z, ?_⟩
    have hda : (d a : ℚ) ≠ 0 := by exact_mod_cast hd a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    push_cast
    calc
      _ = (∏ i ∈ s, (d i : ℚ)) + (d a : ℚ) *
          (((∏ i ∈ s, d i : ℤ) : ℚ) * (∑ i ∈ s, 1 / (d i : ℚ))) := by
        push_cast
        field_simp
      _ = _ := by rw [hz]

/-- Clearing the aggregate sum forces a divisibility relation without
assuming that any individual reciprocal denominator is cleared. -/
lemma first_denominator_dvd {ι : Type*} (s : Finset ι) (d : ι → ℤ)
    (b N : ℤ) (hb : b ≠ 0) (hd : ∀ i ∈ s, d i ≠ 0)
    (h : ∃ z : ℤ, (N : ℚ) * (1 / (b : ℚ) + ∑ i ∈ s, 1 / (d i : ℚ)) = z) :
    b ∣ N * ∏ i ∈ s, d i := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨w, hw⟩ := integral_product_sum s d hd
  let D : ℤ := ∏ i ∈ s, d i
  let T : ℚ := ∑ i ∈ s, 1 / (d i : ℚ)
  change (N : ℚ) * (1 / (b : ℚ) + T) = z at hz
  change (D : ℚ) * T = w at hw
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hQ : (N : ℚ) * D = (b : ℚ) * ((z : ℚ) * D - (N : ℚ) * w) := by
    calc
      _ = (b : ℚ) * (((N : ℚ) * (1 / (b : ℚ) + T)) * D - (N : ℚ) * ((D : ℚ) * T)) := by
        field_simp
        ring
      _ = _ := by rw [hz, hw]
  exact ⟨z * D - N * w, by exact_mod_cast hQ⟩

def block (k J : ℕ) : ℚ :=
  1 / (k.factorial - 1 : ℚ) +
    ∑ i ∈ Finset.range J, 1 / ((k + i + 1).factorial - 1 : ℚ)

def ratioProduct (k J : ℕ) : ℕ :=
  ∏ i ∈ Finset.range J, ((k + 1).ascFactorial (i + 1) - 1)

lemma ratio_one_lt (k i : ℕ) (hk : 2 ≤ k) :
    1 < (k + 1).ascFactorial (i + 1) := by
  rw [Nat.ascFactorial_succ]
  have hh := Nat.ascFactorial_pos k i
  nlinarith

lemma ratioProduct_pos (k J : ℕ) (hk : 2 ≤ k) : 0 < ratioProduct k J := by
  apply Finset.prod_pos
  intro i hi
  have := ratio_one_lt k i hk
  omega

lemma block_integral_forces_dvd (k J N : ℕ) (hk : 2 ≤ k)
    (h : ∃ z : ℤ, (N : ℚ) * block k J = z) :
    k.factorial - 1 ∣ N * ratioProduct k J := by
  have hkfac : 1 < k.factorial := Nat.one_lt_factorial.mpr hk
  have hfac (i : ℕ) : 1 < (k + i + 1).factorial :=
    Nat.one_lt_factorial.mpr (by omega)
  have hd := first_denominator_dvd (Finset.range J)
    (fun i => ((k + i + 1).factorial : ℤ) - 1) ((k.factorial : ℤ) - 1) N
    (by omega) (fun i _ => by dsimp; have := hfac i; omega) (by simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_one] using h)
  have hm (i : ℕ) :
      ((k + i + 1).factorial : ℤ) - 1 ≡
        ((k + 1).ascFactorial (i + 1) : ℤ) - 1 [ZMOD (k.factorial : ℤ) - 1] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-((k + 1).ascFactorial (i + 1) : ℤ), ?_⟩
    have he : (k + i + 1).factorial = k.factorial * (k + 1).ascFactorial (i + 1) := by
      simpa [Nat.add_assoc] using (Nat.factorial_mul_ascFactorial k (i + 1)).symm
    rw [he]
    push_cast
    ring
  have hmprod := Int.ModEq.prod (s := Finset.range J) (fun i _ => hm i)
  have hd' := ((Int.ModEq.refl (N : ℤ)).mul hmprod).dvd_iff.mp hd
  have hcast : ((ratioProduct k J : ℕ) : ℤ) =
      ∏ i ∈ Finset.range J, (((k + 1).ascFactorial (i + 1) : ℤ) - 1) := by
    unfold ratioProduct
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := ratio_one_lt k i hk; omega), Nat.cast_one]
  rw [← hcast] at hd'
  have he : ((k.factorial - 1 : ℕ) : ℤ) = (k.factorial : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [← he] at hd'
  exact_mod_cast hd'

lemma ratioProduct_bound (k J : ℕ) (hk : 2 ≤ k) :
    ratioProduct k J ≤ 2 ^ (J ^ 2 * J) * (2 ^ (J ^ 2)) ^ k := by
  have hb : ratioProduct k J ≤ ((k + J) ^ J) ^ J := by
    simpa [ratioProduct] using Finset.prod_le_pow_card (Finset.range J)
      (fun i => (k + 1).ascFactorial (i + 1) - 1) ((k + J) ^ J) (by
        intro i hi
        have hiJ : i + 1 ≤ J := by have := Finset.mem_range.mp hi; omega
        calc
          _ ≤ (k + 1).ascFactorial (i + 1) := Nat.sub_le _ _
          _ ≤ (k + (i + 1)) ^ (i + 1) := Nat.ascFactorial_le_pow_add k (i + 1)
          _ ≤ (k + J) ^ J := by gcongr; omega)
  calc
    _ ≤ ((k + J) ^ J) ^ J := hb
    _ ≤ ((2 ^ (k + J)) ^ J) ^ J := by
      gcongr
      exact (Nat.lt_two_pow_self (n := k + J)).le
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

lemma block_integral_forces_bound (C k J : ℕ) (hk : 2 ≤ k)
    (h : ∃ z : ℤ, ((C * k).factorial : ℚ) * block k J = z) :
    k.factorial - 1 ≤ 2 ^ (J ^ 2 * J) * (2 ^ (C ^ 2 + J ^ 2)) ^ k := by
  have hd := block_integral_forces_dvd k J (C * k).factorial hk h
  rw [← FactorialClearingIndex.blockCoefficient_identity] at hd
  have hd' : k.factorial - 1 ∣ FactorialClearingIndex.blockCoefficient C k * ratioProduct k J := by
    apply ((FactorialClearingIndex.pred_factorial_coprime k).pow_right C).dvd_of_dvd_mul_right
    convert hd using 1
    ring
  have hl := Nat.le_of_dvd (Nat.mul_pos (FactorialClearingIndex.blockCoefficient_pos C k)
    (ratioProduct_pos k J hk)) hd'
  calc
    _ ≤ FactorialClearingIndex.blockCoefficient C k * ratioProduct k J := hl
    _ ≤ 2 ^ (C ^ 2 * k) * (2 ^ (J ^ 2 * J) * (2 ^ (J ^ 2)) ^ k) :=
      Nat.mul_le_mul (FactorialClearingIndex.blockCoefficient_bound C k) (ratioProduct_bound k J hk)
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

/-- Even after arbitrary cancellation among a fixed number of neighboring
rows, their sum cannot eventually be cleared at a linear factorial index. -/
theorem eventually_block_not_integral (C J : ℕ) :
    ∀ᶠ k : ℕ in atTop, ¬∃ z : ℤ, ((C * k).factorial : ℚ) * block k J = z := by
  filter_upwards [eventually_ge_atTop 2,
    Nat.eventually_mul_pow_lt_factorial_sub (2 * 2 ^ (J ^ 2 * J))
      (2 ^ (C ^ 2 + J ^ 2)) 0] with k hk hbound
  simp only [Nat.sub_zero] at hbound
  intro h
  have hh := block_integral_forces_bound C k J hk h
  have hp : 0 < 2 ^ (J ^ 2 * J) * (2 ^ (C ^ 2 + J ^ 2)) ^ k := by positivity
  have he := Nat.sub_add_cancel (Nat.factorial_pos k)
  nlinarith

lemma mul_integral_of_den_dvd (q : ℚ) (M : ℕ) (h : q.den ∣ M) :
    ∃ z : ℤ, (M : ℚ) * q = z := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(a : ℤ) * q.num, ?_⟩
  conv_lhs => rw [← Rat.num_div_den q]
  rw [ha]
  push_cast
  field_simp

/-- The reduced denominator itself, not just a termwise common denominator,
needs a superlinear factorial clearing index for each fixed block length. -/
theorem eventual_reduced_clearing_index_gt_linear (C J : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, (block k J).den ∣ N.factorial → C * k < N := by
  filter_upwards [eventually_block_not_integral C J] with k hk
  intro N hN
  by_contra hn
  apply hk
  exact mul_integral_of_den_dvd (block k J) (C * k).factorial
    (hN.trans (Nat.factorial_dvd_factorial (by omega)))

def partialSum (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, 1 / (i.factorial - 1 : ℚ)

lemma block_eq_sum (k J : ℕ) :
    block k J = ∑ i ∈ Finset.range (J + 1), 1 / ((k + i).factorial - 1 : ℚ) := by
  rw [Finset.sum_range_succ']
  simp only [block, Nat.add_zero, Nat.add_assoc, add_comm]

lemma prefix_add (k J : ℕ) : partialSum (k + J + 1) = partialSum k + block k J := by
  simpa only [partialSum, block_eq_sum, Nat.add_assoc] using
    Finset.sum_range_add (fun i => 1 / (i.factorial - 1 : ℚ)) k (J + 1)

/-- Two partial sums whose cutoffs differ by a fixed positive number of
rows cannot both be integral at a linear factorial scaling eventually. -/
theorem eventually_prefix_pair_not_integral (C J : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ¬((∃ z : ℤ, ((C * k).factorial : ℚ) * partialSum k = z) ∧
        (∃ z : ℤ, ((C * k).factorial : ℚ) * partialSum (k + J + 1) = z)) := by
  filter_upwards [eventually_block_not_integral C J] with k hk
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  apply hk
  refine ⟨b - a, ?_⟩
  rw [prefix_add, mul_add, ha] at hb
  push_cast
  linarith

/-- A moving prefix cannot have all of: bounded nonnegative cutoff jumps,
a cutoff at least proportional to the scaling index, divergence of its
cutoff, and an integrally cleared aggregate prefix. Cancellation within the
prefix is fully allowed here. -/
theorem no_bounded_step_cutoff (K : ℕ → ℕ) (C B N : ℕ)
    (hK : Tendsto K atTop atTop)
    (hstep : ∀ n ≥ N, K n ≤ K (n + 1) ∧ K (n + 1) ≤ K n + B)
    (hlinear : ∀ n ≥ N, n ≤ C * K n)
    (hclear : ∀ n ≥ N, (partialSum (K n)).den ∣ n.factorial) : False := by
  have hevent : ∀ᶠ k : ℕ in atTop, ∀ J ∈ Finset.range B,
      ¬((∃ z : ℤ, (((C + 1) * k).factorial : ℚ) * partialSum k = z) ∧
        (∃ z : ℤ, (((C + 1) * k).factorial : ℚ) * partialSum (k + J + 1) = z)) := by
    apply (eventually_all_finset (Finset.range B)).mpr
    intro J hJ
    exact eventually_prefix_pair_not_integral (C + 1) J
  have hstable : ∀ᶠ n : ℕ in atTop, K (n + 1) = K n := by
    filter_upwards [hK.eventually hevent, hK.eventually_ge_atTop 1,
      eventually_ge_atTop N] with n hn hkpos hnN
    have hs := hstep n hnN
    by_contra hne
    have hlt : K n < K (n + 1) := by omega
    let J := K (n + 1) - K n - 1
    have hJ : J < B := by dsimp [J]; omega
    have hJeq : K n + J + 1 = K (n + 1) := by dsimp [J]; omega
    have hscale : n + 1 ≤ (C + 1) * K n := by
      have hh := hlinear n hnN
      nlinarith
    apply hn J (Finset.mem_range.mpr hJ)
    constructor
    · exact mul_integral_of_den_dvd _ _
        ((hclear n hnN).trans (Nat.factorial_dvd_factorial (by omega)))
    · rw [hJeq]
      exact mul_integral_of_den_dvd _ _
        ((hclear (n + 1) (by omega)).trans (Nat.factorial_dvd_factorial hscale))
  obtain ⟨a, ha⟩ := eventually_atTop.mp hstable
  have hconst : ∀ n ≥ a, K n = K a := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [ha n hn, ih]
  obtain ⟨n, hn, hkn⟩ := ((eventually_ge_atTop a).and
    (hK.eventually_ge_atTop (K a + 1))).exists
  rw [hconst n hn] at hkn
  omega

#print axioms no_bounded_step_cutoff

#print axioms eventual_reduced_clearing_index_gt_linear
#print axioms eventually_prefix_pair_not_integral

#print axioms first_denominator_dvd
#print axioms block_integral_forces_dvd
#print axioms eventually_block_not_integral

end FiniteBlockClearing
