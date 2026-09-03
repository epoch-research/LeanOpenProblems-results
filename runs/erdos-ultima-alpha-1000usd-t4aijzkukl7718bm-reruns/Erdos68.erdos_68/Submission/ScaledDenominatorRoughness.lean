import Submission.Development

/-! Reduced-denominator restrictions for the scaled partial sums.
These are auxiliary results; they do not settle Erdős problem 68. -/

namespace ScaledDenominatorRoughness

open Erdos68Development

lemma coprime_sum_den {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ℕ)
    (h : ∀ i ∈ s, Nat.Coprime b (f i).den) :
    Nat.Coprime b (∑ i ∈ s, f i).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Nat.Coprime.of_dvd_right (Rat.add_den_dvd _ _)
      ((h a (Finset.mem_insert_self _ _)).mul_right
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

lemma factorial_pred_coprime {B m : ℕ} (hBm : B ≤ m) :
    Nat.Coprime B.factorial (m.factorial - 1) := by
  apply Nat.Coprime.of_dvd_left (Nat.factorial_dvd_factorial hBm)
  exact (Nat.coprime_self_sub_right (Nat.factorial_pos m)).mpr (by simp)

lemma scaled_row_den_coprime (B n k : ℕ) (hn : B.factorial ≤ n + 1) :
    Nat.Coprime B.factorial
      (((n + 1).factorial : ℚ) * (1 / ((k + 2).factorial - 1 : ℚ))).den := by
  have hf : 2 ≤ (k + 2).factorial := by
    simpa using Nat.factorial_le (show 2 ≤ k + 2 by omega)
  have heq : ((k + 2).factorial - 1 : ℚ) = ↑((k + 2).factorial - 1) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [heq, one_div]
  by_cases hk : k + 2 ≤ B
  · have hd : (k + 2).factorial - 1 ∣ (n + 1).factorial :=
      Nat.dvd_factorial (by omega)
        (by have := Nat.factorial_le hk; omega)
    obtain ⟨c, hc⟩ := hd
    have hne : (↑((k + 2).factorial - 1) : ℚ) ≠ 0 := by
      exact_mod_cast (show (k + 2).factorial - 1 ≠ 0 by omega)
    have hrow : ((n + 1).factorial : ℚ) * (↑((k + 2).factorial - 1) : ℚ)⁻¹ = c := by
      rw [hc, Nat.cast_mul]
      field_simp
    rw [hrow]
    simp
  · apply Nat.Coprime.of_dvd_right (Rat.mul_den_dvd _ _)
    simpa [Rat.inv_natCast_den_of_pos (show 0 < (k + 2).factorial - 1 by omega)]
      using factorial_pred_coprime (show B ≤ k + 2 by omega)

/-- At sufficiently large cutoffs, every fixed factorial is coprime to the
reduced denominator of the scaled partial sum. -/
theorem scaledSumQ_den_coprime (B n : ℕ) (hn : B.factorial ≤ n + 1) :
    Nat.Coprime B.factorial (scaledSumQ n).den := by
  unfold scaledSumQ
  rw [Finset.mul_sum]
  exact coprime_sum_den _ _ _ (fun k _ => scaled_row_den_coprime B n k hn)

lemma factorial_mul_rat_integer (q : ℚ) (n : ℕ) (hn : q.den ≤ n + 1) :
    ∃ z : ℤ, ((n + 1).factorial : ℚ) * q = z := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos hn
  refine ⟨(c : ℤ) * q.num, ?_⟩
  conv_lhs => rw [← Rat.num_div_den q]
  rw [hc]
  push_cast
  field_simp

/-- Once the putative denominator is cleared, the rational tail and the scaled
partial sum have exactly the same reduced denominator. -/
theorem scaled_rational_tail_den (q : ℚ) (n : ℕ) (hn : q.den ≤ n + 1) :
    (((n + 1).factorial : ℚ) * q - scaledSumQ n).den = (scaledSumQ n).den := by
  obtain ⟨z, hz⟩ := factorial_mul_rat_integer q n hn
  rw [hz, Rat.intCast_sub_den]

#print axioms scaledSumQ_den_coprime
#print axioms scaled_rational_tail_den

end ScaledDenominatorRoughness
