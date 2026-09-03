import Submission.NewmanDegreeNineteenData
import Submission.NewmanNineteenSparsePrefix

/-! Exclusion of one particular degree-19 Newman divisor, using exact
integer cuts. This does not classify all factors or settle Erdős 406. -/
namespace Erdos406NineteenPrefix
open Polynomial Finset Erdos406Quotient Erdos406IntegerCuts
lemma coeff_mul_eq_fin_sum {N n : ℕ} (hn : n < N) (Q R : ℤ[X]) :
    (Q * R).coeff n = ∑ j : Fin N,
      if j.val ≤ n then Q.coeff (n - j.val) * R.coeff j.val else 0 := by
  rw [mul_comm Q R, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ n then Q.coeff (n - j) * R.coeff j else 0)]
  have hs : Finset.range (n + 1) ⊆ Finset.range N := Finset.range_mono (by omega)
  rw [← Finset.sum_subset hs]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using hj
    simp [hjn, mul_comm]
  · intro j hj hjn
    have hjn' : ¬ j ≤ n := by simpa using hjn
    simp [hjn']
open Erdos406Quotient
lemma listPoly_coeff_getD (w : List ℤ) (n : ℕ) :
    (listPoly w).coeff n = w.getD n 0 := by
  induction w generalizing n with
  | nil => simp [listPoly]
  | cons a w ih =>
    cases n with
    | zero => simp [listPoly]
    | succ n => simp only [listPoly, coeff_add, coeff_C, coeff_X_mul, ih]; simp

lemma qNineteen_coeff (n : ℕ) : qNineteen.coeff n = coefficients.getD n 0 := by
  rw [qNineteen_list, listPoly_coeff_getD]
  change _ = ([1, 0, -1, 0, 2, -1, -1, 1, 2, -1, -2, 2, 1, -2, 0, 0, 1, -1, 0, 1] : List ℤ).toArray.getD n 0
  simp

lemma tri_product_coeff (R : ℤ[X]) (i : Fin 64) :
    dot (tri i) (fun j => R.coeff j.val) = (qNineteen * R).coeff i.val := by
  rw [coeff_mul_eq_fin_sum i.isLt]
  unfold dot
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j.val ≤ i.val <;> simp [tri, h, qNineteen_coeff]

lemma dot_unit (r : Fin 64 → ℤ) (k : Fin 64) :
    dot (fun j => if j.val = k.val then 1 else 0) r = r k := by
  simp [dot, Fin.val_inj]

lemma dot_neg_unit (r : Fin 64 → ℤ) (k : Fin 64) :
    dot (fun j => if j.val = k.val then -1 else 0) r = -r k := by
  simp [dot, Fin.val_inj]

lemma initial_valid (P R : ℤ[X]) (hPR : P = qNineteen * R)
    (h0 : P.coeff 0 = 1) (hP : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ 1)
    (hR : ∀ i, |R.coeff i| ≤ 28) :
    Valid matrix state0 (fun j => R.coeff j.val) := by
  let r : Fin 64 → ℤ := fun j => R.coeff j.val
  have hp (i : Fin 64) : 0 ≤ dot (tri i) r ∧ dot (tri i) r ≤ 1 := by
    simpa only [r, tri_product_coeff, ← hPR] using hP i.val
  have hz : dot (tri 0) r = 1 := by
    simpa only [r, tri_product_coeff, ← hPR] using h0
  have hb (i : Fin 64) : -28 ≤ r i ∧ r i ≤ 28 := abs_le.mp (hR i.val)
  change Valid matrix state0 r
  intro i
  by_cases h64 : i.val < 64
  · have he : dot (matrix i) r = dot (tri ⟨i.val, h64⟩) r := by
      unfold dot
      simp only [matrix, dif_pos h64]
    rw [he]
    simpa only [state0, if_pos h64] using (hp ⟨i.val, h64⟩).2
  · by_cases h128 : i.val < 128
    · let k : Fin 64 := ⟨i.val - 64, by omega⟩
      have he : dot (matrix i) r = -dot (tri k) r := by
        simp only [matrix, dif_neg h64, dif_pos h128, dot, neg_mul,
          Finset.sum_neg_distrib, k]
      rw [he]
      by_cases heq : i.val = 64
      · have hk : k = 0 := by apply Fin.ext; simp [k, heq]
        rw [hk, hz]
        simp [state0, heq]
      · simpa only [state0, if_neg h64, if_pos h128, if_neg heq]
          using neg_nonpos.mpr (hp k).1
    · by_cases h192 : i.val < 192
      · let k : Fin 64 := ⟨i.val - 128, by omega⟩
        have he : dot (matrix i) r = r k := by
          unfold dot
          simp only [matrix, dif_neg h64, dif_neg h128, if_pos h192]
          exact dot_unit r k
        rw [he]
        simpa only [state0, if_neg h64, if_neg h128] using (hb k).2
      · let k : Fin 64 := ⟨i.val - 192, by omega⟩
        have he : dot (matrix i) r = -r k := by
          unfold dot
          simp only [matrix, dif_neg h64, dif_neg h128, if_neg h192]
          exact dot_neg_unit r k
        rw [he]
        have hh : -r k ≤ 28 := by have := (hb k).1; omega
        simpa only [state0, if_neg h64, if_neg h128] using hh

#print axioms initial_valid
end Erdos406NineteenPrefix

namespace Erdos406Quotient
open Polynomial

lemma qNineteen_eval_three : qNineteen.eval 3 = (2 : ℤ) ^ 30 := by
  norm_num [qNineteen]

lemma qNineteen_degree : qNineteen.natDegree = 19 := by
  unfold qNineteen
  compute_degree <;> norm_num

theorem qNineteen_not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qNineteen ∣ P := by
  rintro ⟨R, hPR⟩
  have hR := qNineteen_quotient_bound P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hp (i : ℕ) : 0 ≤ P.coeff i ∧ P.coeff i ≤ 1 := by
    rcases hP i with h | h <;> rw [h] <;> norm_num
  exact Erdos406NineteenPrefix.impossible (fun j => R.coeff j.val)
    (Erdos406NineteenPrefix.initial_valid P R hPR h0 hp hR)

theorem qNineteen_not_dvd_digits (w : List ℕ) (hw : w ⊆ [0, 1]) :
    ¬ qNineteen ∣ Nat.ofDigits (X : ℤ[X]) (1 :: w) := by
  apply qNineteen_not_dvd_newman
  · simp [Nat.ofDigits]
  · exact ofDigits_coeff_zero_one _ (by simpa using hw)

#print axioms qNineteen_not_dvd_newman
#print axioms qNineteen_not_dvd_digits
end Erdos406Quotient
