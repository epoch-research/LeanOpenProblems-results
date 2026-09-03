import Submission.Development

/-!
# Integer forms from index-dependent telescoping kernels

This auxiliary development verifies an identity, not an irrationality proof.
No sequence of nonzero small forms is constructed here.
-/

namespace IndexDependentTelescoping

open Filter Topology

lemma summable_nat_pow_div_factorial (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k / (n.factorial : ℝ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [Nat.eventually_pow_lt_factorial_sub 2 0] with n hn
  have hf : (2 : ℝ) ^ n ≤ (n.factorial : ℝ) := by
    exact_mod_cast (show 2 ^ n ≤ n.factorial by simpa using hn.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (n : ℝ) ^ k / (n.factorial : ℝ) ≤ (n : ℝ) ^ k / (2 : ℝ) ^ n := by
      gcongr
    _ = (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]; ring

lemma summable_eval_div_factorial (H : Polynomial ℤ) :
    Summable (fun n : ℕ =>
      H.eval₂ (Int.castRingHom ℝ) (n : ℝ) / (n.factorial : ℝ)) := by
  induction H using Polynomial.induction_on' with
  | add H K hH hK =>
      simpa only [Polynomial.eval₂_add, add_div] using hH.add hK
  | monomial k c =>
      simpa only [Polynomial.eval₂_monomial, mul_div_assoc]
        using (summable_nat_pow_div_factorial k).mul_left (c : ℝ)

lemma summable_eval_div_factorial_pow (H : Polynomial ℤ) (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun n : ℕ =>
      H.eval₂ (Int.castRingHom ℝ) (n : ℝ) / (n.factorial : ℝ) ^ j) := by
  apply (summable_eval_div_factorial H).norm.of_norm_bounded
  intro n
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp : (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ j := by
    simpa using pow_le_pow_right₀ hf hj
  simp only [norm_div, Real.norm_eq_abs, abs_pow,
    abs_of_nonneg (show (0 : ℝ) ≤ n.factorial by positivity)]
  gcongr

/-- The integer coefficient of a telescoping factorial-power row. -/
def rowCoeff (H : Polynomial ℤ) (j n : ℕ) : ℤ :=
  ((n + 2 : ℕ) : ℤ) ^ j * H.eval ((n + 1 : ℕ) : ℤ) -
    H.eval ((n + 2 : ℕ) : ℤ)

noncomputable def scaledEval (H : Polynomial ℤ) (j n : ℕ) : ℝ :=
  ((H.eval (n : ℤ) : ℤ) : ℝ) / (n.factorial : ℝ) ^ j

lemma cast_eval_nat (H : Polynomial ℤ) (n : ℕ) :
    ((H.eval (n : ℤ) : ℤ) : ℝ) = H.eval₂ (Int.castRingHom ℝ) (n : ℝ) := by
  simpa using (Polynomial.eval₂_at_apply (p := H) (Int.castRingHom ℝ) (n : ℤ)).symm

lemma summable_scaledEval (H : Polynomial ℤ) (j : ℕ) (hj : 1 ≤ j) :
    Summable (scaledEval H j) := by
  change Summable (fun n : ℕ => ((H.eval (n : ℤ) : ℤ) : ℝ) / (n.factorial : ℝ) ^ j)
  simpa only [cast_eval_nat] using summable_eval_div_factorial_pow H j hj

lemma rowCoeff_div (H : Polynomial ℤ) (j n : ℕ) :
    (rowCoeff H j n : ℝ) / ((n + 2).factorial : ℝ) ^ j =
      scaledEval H j (n + 1) - scaledEval H j (n + 2) := by
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((n + 2).factorial : ℝ) =
      (n + 2 : ℝ) * ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  unfold rowCoeff scaledEval
  push_cast
  rw [hfac, mul_pow]
  field_simp

lemma hasSum_rowCoeff (H : Polynomial ℤ) (j : ℕ) (hj : 1 ≤ j) :
    HasSum (fun n : ℕ => (rowCoeff H j n : ℝ) / ((n + 2).factorial : ℝ) ^ j)
      ((H.eval 1 : ℤ) : ℝ) := by
  have hs := summable_scaledEval H j hj
  have hs1 : Summable (fun n => scaledEval H j (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable (fun n => scaledEval H j (n + 2)) :=
    (summable_nat_add_iff 2).mpr hs
  have he := Summable.sum_add_tsum_nat_add 1 hs1
  have he' : (∑' n, scaledEval H j (n + 1)) -
      (∑' n, scaledEval H j (n + 2)) = ((H.eval 1 : ℤ) : ℝ) := by
    simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
    have hbase : scaledEval H j 1 = ((H.eval 1 : ℤ) : ℝ) := by
      simp [scaledEval]
    rw [hbase] at he
    linarith
  simpa only [rowCoeff_div, he'] using hs1.hasSum.sub hs2.hasSum

end IndexDependentTelescoping

namespace IndexDependentTelescoping

/-- The numerator of the weighted original row. -/
noncomputable def kernel (A : ℤ) (H : ℕ → Polynomial ℤ) (J n : ℕ) (t : ℝ) : ℝ :=
  (A : ℝ) - (1 - t) *
    ∑ j ∈ Finset.range J, (rowCoeff (H j) (j + 1) n : ℝ) * t ^ j

def boundary (H : ℕ → Polynomial ℤ) (J : ℕ) : ℤ :=
  ∑ j ∈ Finset.range J, (H j).eval 1

lemma kernel_div (A : ℤ) (H : ℕ → Polynomial ℤ) (J n : ℕ) :
    kernel A H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1) =
      (A : ℝ) / (((n + 2).factorial : ℝ) - 1) -
        ∑ j ∈ Finset.range J,
          (rowCoeff (H j) (j + 1) n : ℝ) / ((n + 2).factorial : ℝ) ^ (j + 1) := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd : ((n + 2).factorial : ℝ) - 1 ≠ 0 :=
    ne_of_gt (Erdos68Development.denom_pos n)
  unfold kernel
  rw [sub_div, Finset.mul_sum, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_pow, one_pow, pow_succ]
  field_simp

lemma hasSum_rows (H : ℕ → Polynomial ℤ) (J : ℕ) :
    HasSum (fun n : ℕ => ∑ j ∈ Finset.range J,
      (rowCoeff (H j) (j + 1) n : ℝ) / ((n + 2).factorial : ℝ) ^ (j + 1))
      ((boundary H J : ℤ) : ℝ) := by
  induction J with
  | zero => simpa [boundary] using (hasSum_zero (β := ℕ) (α := ℝ))
  | succ J ih =>
      simpa only [boundary, Finset.sum_range_succ, Int.cast_add] using
        ih.add (hasSum_rowCoeff (H J) (J + 1) (by omega))

/-- Exact integer linear form. There is no smallness or nonvanishing assertion. -/
theorem hasSum_kernel (A : ℤ) (H : ℕ → Polynomial ℤ) (J : ℕ) :
    HasSum (fun n : ℕ =>
      kernel A H J n (1 / ((n + 2).factorial : ℝ)) /
        (((n + 2).factorial : ℝ) - 1))
      ((A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) -
        ((boundary H J : ℤ) : ℝ)) := by
  simpa only [kernel_div, Erdos68Development.term, mul_one_div] using
    (Erdos68Development.summable_term.hasSum.mul_left (A : ℝ)).sub (hasSum_rows H J)

lemma clear_power_denominator (F : ℤ) (hF : F ≠ 0) (J : ℕ) (c : ℕ → ℤ) :
    (∑ j ∈ Finset.range J, (c j : ℝ) / (F : ℝ) ^ (j + 1)) * (F : ℝ) ^ J =
      ((∑ j ∈ Finset.range J, c j * F ^ (J - (j + 1)) : ℤ) : ℝ) := by
  have hF' : (F : ℝ) ≠ 0 := by exact_mod_cast hF
  rw [Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j + 1 ≤ J := by simpa using Finset.mem_range.mp hj
  have he : (F : ℝ) ^ J = (F : ℝ) ^ (j + 1) * (F : ℝ) ^ (J - (j + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [he]
  field_simp

/-- Exact annihilation of a row forces its original denominator to divide A. -/
theorem denominator_dvd_of_kernel_zero (A : ℤ) (H : ℕ → Polynomial ℤ) (J n : ℕ)
    (hz : kernel A H J n (1 / ((n + 2).factorial : ℝ)) = 0) :
    ((n + 2).factorial : ℤ) - 1 ∣ A := by
  let F : ℤ := (n + 2).factorial
  let c : ℕ → ℤ := fun j => rowCoeff (H j) (j + 1) n
  let B : ℤ := ∑ j ∈ Finset.range J, c j * F ^ (J - (j + 1))
  have hF : F ≠ 0 := by dsimp [F]; positivity
  have hd : (F : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (Erdos68Development.denom_pos n)
  have hpoint := kernel_div A H J n
  rw [hz, zero_div] at hpoint
  have he : (A : ℝ) / ((F : ℝ) - 1) =
      ∑ j ∈ Finset.range J, (c j : ℝ) / (F : ℝ) ^ (j + 1) := by
    simp only [F, c, Int.cast_natCast]
    linarith [hpoint]
  have hm := congrArg (fun x : ℝ => x * (F : ℝ) ^ J) he
  dsimp only at hm
  rw [clear_power_denominator F hF J c] at hm
  have hreal : (A : ℝ) * (F : ℝ) ^ J = ((F : ℝ) - 1) * (B : ℝ) := by
    dsimp [B]
    field_simp at hm
    nlinarith [hm]
  have hint : A * F ^ J = (F - 1) * B := by exact_mod_cast hreal
  have hcop : IsCoprime (F - 1) F := ⟨-1, 1, by ring⟩
  apply hcop.pow_right.dvd_of_dvd_mul_left
  exact ⟨B, by simpa [mul_comm] using hint⟩

lemma nonzero_kernel_with_zero_sum :
    kernel 0 (fun _ => (Polynomial.X - 1 : Polynomial ℤ)) 1 0 (1 / 2) = 1 / 2 ∧
      (∑' n : ℕ,
        kernel 0 (fun _ => (Polynomial.X - 1 : Polynomial ℤ)) 1 n
          (1 / ((n + 2).factorial : ℝ)) /
          (((n + 2).factorial : ℝ) - 1)) = 0 := by
  constructor
  · norm_num [kernel, rowCoeff]
  · have h := (hasSum_kernel 0 (fun _ => (Polynomial.X - 1 : Polynomial ℤ)) 1).tsum_eq
    norm_num [boundary] at h
    simpa only [one_div] using h

#print axioms hasSum_kernel
#print axioms denominator_dvd_of_kernel_zero
#print axioms nonzero_kernel_with_zero_sum

end IndexDependentTelescoping
