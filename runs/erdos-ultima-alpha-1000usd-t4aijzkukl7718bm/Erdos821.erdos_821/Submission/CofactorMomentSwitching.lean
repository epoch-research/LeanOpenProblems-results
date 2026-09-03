import Submission.HigherDivisorSubpower

/-!
# Divisor-weighted cofactors and the resulting product moduli

Expanding a cofactor divisor weight gives ordinary Mangoldt progression sums
at larger product moduli. These are exact finite identities, not estimates
for the weighted correlations or for the resulting full-range discrepancy.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta

namespace Erdos821.HigherDivisors

open AnalyticSieve

noncomputable def cofactorMangoldtMoment (k d X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    if d ∣ n-1 then vonMangoldt n * (tau k ((n-1)/d) : ℝ) else 0

lemma cofactorMangoldtMoment_one (k X : ℕ) :
    cofactorMangoldtMoment k 1 X = shiftedMangoldtMoment k X := by
  simp [cofactorMangoldtMoment, shiftedMangoldtMoment]

lemma cofactor_divisor_filter (d n X : ℕ) (hd : 0 < d)
    (hn : 0 < n) (hnX : n ≤ X) (hdn : d ∣ n) :
    (Finset.Icc 1 (X/d)).filter (fun e => d*e ∣ n) = (n/d).divisors := by
  have hquot : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨he1, heX⟩, he⟩
    exact ⟨Nat.dvd_div_of_mul_dvd he, hquot.ne'⟩
  · rintro ⟨he, hn0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos he hquot,
      (Nat.le_of_dvd hquot he).trans (Nat.div_le_div_right hnX)⟩,
      (Nat.dvd_div_iff_mul_dvd hdn).mp he⟩

/-- The complementary divisor weight changes the modulus from d to d*e.
The e range reaches X/d, so this identity is not a short-modulus estimate. -/
theorem cofactorMangoldtMoment_succ (k d X : ℕ) (hd : 0 < d) :
    cofactorMangoldtMoment (k+1) d X =
      ∑ e ∈ Finset.Icc 1 (X/d), (tau k e : ℝ) * residueOneMangoldt (d*e) X := by
  unfold cofactorMangoldtMoment residueOneMangoldt
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnX := (Finset.mem_Icc.mp hn).2
  by_cases hn' : n = 1
  · subst n
    simp only [vonMangoldt_apply_one, mul_zero, zero_mul, ite_self, Finset.sum_const_zero]
  simp_rw [residue_one_iff_dvd_pred hn1]
  by_cases hdn : d ∣ n-1
  · rw [if_pos hdn, tau_succ, Nat.cast_sum, Finset.mul_sum]
    calc
      _ = ∑ e ∈ (Finset.Icc 1 (X/d)).filter (fun e => d*e ∣ n-1),
          vonMangoldt n * (tau k e : ℝ) := by
        rw [cofactor_divisor_filter d (n-1) X hd (by omega) (by omega) hdn]
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e he
        split_ifs <;> ring
  · rw [if_neg hdn]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have hde : ¬d*e ∣ n-1 := fun h => hdn ((Nat.dvd_mul_right d e).trans h)
    simp [hde]

lemma cofactorMangoldtMoment_nonneg (k d X : ℕ) :
    0 ≤ cofactorMangoldtMoment k d X := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  · exact le_rfl

/-- An arbitrary cofactor cutoff gives a lower sum, but its product
moduli d*e still need to be estimated. -/
lemma truncated_progressions_le_cofactorMoment (k d T X : ℕ)
    (hd : 0 < d) (hT : T ≤ X/d) :
    (∑ e ∈ Finset.Icc 1 T, (tau k e : ℝ) * residueOneMangoldt (d*e) X) ≤
      cofactorMangoldtMoment (k+1) d X := by
  rw [cofactorMangoldtMoment_succ k d X hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he).1, (Finset.mem_Icc.mp he).2.trans hT⟩
  · intro e he heT
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun n _ => by split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl)

lemma sum_convolution_weighted_quotient (f g : ArithmeticFunction ℝ)
    (w : ℕ → ℝ) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (f*g) n * w n) =
      ∑ d ∈ Finset.Icc 1 X, f d *
        ∑ e ∈ Finset.Icc 1 (X/d), g e * w (d*e) := by
  rw [sum_convolution_weighted f g w (le_refl X)]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hset : (Finset.Icc 1 X).filter (fun e => d*e ≤ X) = Finset.Icc 1 (X/d) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hdiv := Nat.div_le_self X d
    have he : d*e ≤ X ↔ e ≤ X/d := by rw [Nat.le_div_iff_mul_le hd0, mul_comm]
    rw [he]
    omega
  rw [← Finset.sum_filter, hset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

noncomputable def truncatedConvolution (r s Q : ℕ) : ArithmeticFunction ℝ :=
  shortPart ((ζ : ArithmeticFunction ℝ)^r) Q * (ζ : ArithmeticFunction ℝ)^s

/-- Aggregation puts the cofactor-weighted expression over moduli up to X,
not merely up to the outer cutoff Q. -/
theorem cofactor_moment_eq_product_moduli (r s Q X : ℕ) (hQX : Q ≤ X) :
    (∑ d ∈ Finset.Icc 1 Q, (tau r d : ℝ) * cofactorMangoldtMoment (s+1) d X) =
      ∑ m ∈ Finset.Icc 1 X, truncatedConvolution r s Q m * residueOneMangoldt m X := by
  unfold truncatedConvolution
  rw [sum_convolution_weighted_quotient]
  have hset : (Finset.Icc 1 X).filter (fun d => d ≤ Q) = Finset.Icc 1 Q := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  simp only [shortPart]
  simp only [ArithmeticFunction.coe_mk, ite_mul, zero_mul]
  rw [← Finset.sum_filter, hset]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cofactorMangoldtMoment_succ s d X (Finset.mem_Icc.mp hd).1]
  simp only [tau_cast]

lemma truncatedConvolution_nonneg (r s Q m : ℕ) :
    0 ≤ truncatedConvolution r s Q m := by
  unfold truncatedConvolution
  rw [mul_apply]
  apply Finset.sum_nonneg
  intro ab hab
  apply mul_nonneg _ (tau_real_nonneg _ _)
  simp only [shortPart, ArithmeticFunction.coe_mk]
  split_ifs <;> first | exact tau_real_nonneg _ _ | exact le_rfl

lemma truncatedConvolution_le_tau (r s Q m : ℕ) :
    truncatedConvolution r s Q m ≤ (tau (r+s) m : ℝ) := by
  rw [tau_cast, pow_add]
  unfold truncatedConvolution
  rw [mul_apply, mul_apply]
  apply Finset.sum_le_sum
  intro ab hab
  apply mul_le_mul_of_nonneg_right _ (tau_real_nonneg _ _)
  simp only [shortPart, ArithmeticFunction.coe_mk]
  split_ifs <;> first | exact le_rfl | exact tau_real_nonneg _ _

lemma truncatedConvolution_eq_tau_below (r s Q m : ℕ) (hm : m ≤ Q) :
    truncatedConvolution r s Q m = (tau (r+s) m : ℝ) := by
  rw [tau_cast, pow_add]
  unfold truncatedConvolution
  rw [mul_apply, mul_apply]
  apply Finset.sum_congr rfl
  intro ab hab
  have ha : ab.1 ≤ Q := (Nat.divisor_le
    (Nat.fst_mem_divisors_of_mem_antidiagonal hab)).trans hm
  simp [shortPart, ha]

/-- With no outer truncation, this is just the original higher moment
written as a sum of cofactor moments; the identity adds no distribution. -/
theorem full_cofactor_moment_eq_shiftedMoment (r s X : ℕ) :
    (∑ d ∈ Finset.Icc 1 X, (tau r d : ℝ) * cofactorMangoldtMoment (s+1) d X) =
      shiftedMangoldtMoment (r+s+1) X := by
  rw [cofactor_moment_eq_product_moduli r s X X le_rfl]
  simp_rw [Finset.sum_congr rfl (fun m hm => congrArg
    (fun x : ℝ => x * residueOneMangoldt m X)
    (truncatedConvolution_eq_tau_below r s X m (Finset.mem_Icc.mp hm).2))]
  have h := cofactorMangoldtMoment_succ (r+s) 1 X (by norm_num)
  simpa only [cofactorMangoldtMoment_one, Nat.div_one, one_mul] using h.symm

/-- A full-range weighted discrepancy bounds this reindexed error.
No estimate making that discrepancy small is asserted. -/
theorem product_modulus_error_le_full_discrepancy (r s Q X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, truncatedConvolution r s Q m *
      |residueOneMangoldt m X - mangoldtSum X/(m.totient : ℝ)|) ≤
        divisorProgressionError (r+s) X X := by
  apply Finset.sum_le_sum
  intro m hm
  exact mul_le_mul_of_nonneg_right (truncatedConvolution_le_tau r s Q m) (abs_nonneg _)

end Erdos821.HigherDivisors
