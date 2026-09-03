import Submission.IntegerCutCertificates
import Submission.NewmanQuotientCertificate

/-! Generic conversion of a Newman-divisor problem into finite integer
prefix constraints. Concrete certificates must still be supplied. -/
namespace Erdos406FinitePrefix
open Polynomial Erdos406Quotient Erdos406IntegerCuts

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

lemma listPoly_coeff_getD (w : List ℤ) (n : ℕ) :
    (listPoly w).coeff n = w.getD n 0 := by
  induction w generalizing n with
  | nil => simp [listPoly]
  | cons a w ih =>
    cases n with
    | zero => simp [listPoly]
    | succ n => simp only [listPoly, coeff_add, coeff_C, coeff_X_mul, ih]; simp

variable {N : ℕ}
def tri (c : Array ℤ) (i j : Fin N) : ℤ :=
  if j.val ≤ i.val then c.getD (i.val - j.val) 0 else 0

def matrix (c : Array ℤ) (i : Fin (4 * N)) (j : Fin N) : ℤ :=
  if h : i.val < N then tri c ⟨i.val, h⟩ j
  else if h : i.val < 2 * N then -tri c ⟨i.val - N, by omega⟩ j
  else if i.val < 3 * N then (if j.val = i.val - 2 * N then 1 else 0)
  else (if j.val = i.val - 3 * N then -1 else 0)

def state (B : Fin N → ℤ) (i : Fin (4 * N)) : ℤ :=
  if i.val < N then 1
  else if i.val < 2 * N then (if i.val = N then -1 else 0)
  else if h : i.val < 3 * N then B ⟨i.val - 2 * N, by omega⟩
  else B ⟨i.val - 3 * N, by omega⟩

lemma tri_product_coeff (c : Array ℤ) (Q R : ℤ[X])
    (hc : ∀ n, Q.coeff n = c.getD n 0) (i : Fin N) :
    dot (tri c i) (fun j => R.coeff j.val) = (Q * R).coeff i.val := by
  rw [coeff_mul_eq_fin_sum i.isLt]
  unfold dot
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j.val ≤ i.val <;> simp [tri, h, hc]

lemma dot_unit (r : Fin N → ℤ) (k : Fin N) :
    dot (fun j => if j.val = k.val then 1 else 0) r = r k := by
  simp [dot, Fin.val_inj]

lemma dot_neg_unit (r : Fin N → ℤ) (k : Fin N) :
    dot (fun j => if j.val = k.val then -1 else 0) r = -r k := by
  simp [dot, Fin.val_inj]

lemma initial_valid (hN : 0 < N) (c : Array ℤ) (B : Fin N → ℤ) (Q P R : ℤ[X])
    (hc : ∀ n, Q.coeff n = c.getD n 0) (hPR : P = Q * R)
    (h0 : P.coeff 0 = 1) (hP : ∀ i, 0 ≤ P.coeff i ∧ P.coeff i ≤ 1)
    (hR : ∀ i : Fin N, |R.coeff i.val| ≤ B i) :
    Valid (matrix c) (state B) (fun j => R.coeff j.val) := by
  let r : Fin N → ℤ := fun j => R.coeff j.val
  have hp (i : Fin N) : 0 ≤ dot (tri c i) r ∧ dot (tri c i) r ≤ 1 := by
    simpa only [r, tri_product_coeff c Q R hc, ← hPR] using hP i.val
  have hz : dot (tri c ⟨0, hN⟩) r = 1 := by
    simpa only [r, tri_product_coeff c Q R hc, ← hPR] using h0
  have hb (i : Fin N) : -B i ≤ r i ∧ r i ≤ B i := abs_le.mp (hR i)
  change Valid (matrix c) (state B) r
  intro i
  by_cases h1 : i.val < N
  · have he : dot (matrix c i) r = dot (tri c ⟨i.val, h1⟩) r := by
      unfold dot
      simp only [matrix, dif_pos h1]
    rw [he]
    simpa only [state, if_pos h1] using (hp ⟨i.val, h1⟩).2
  · by_cases h2 : i.val < 2 * N
    · let k : Fin N := ⟨i.val - N, by omega⟩
      have he : dot (matrix c i) r = -dot (tri c k) r := by
        simp only [matrix, dif_neg h1, dif_pos h2, dot, neg_mul,
          Finset.sum_neg_distrib, k]
      rw [he]
      by_cases heq : i.val = N
      · have hk : k = ⟨0, hN⟩ := by apply Fin.ext; simp [k, heq]
        rw [hk, hz]
        simp [state, heq, hN]
      · simpa only [state, if_neg h1, if_pos h2, if_neg heq]
          using neg_nonpos.mpr (hp k).1
    · by_cases h3 : i.val < 3 * N
      · let k : Fin N := ⟨i.val - 2 * N, by omega⟩
        have he : dot (matrix c i) r = r k := by
          unfold dot
          simp only [matrix, dif_neg h1, dif_neg h2, if_pos h3]
          exact dot_unit r k
        rw [he]
        simpa only [state, if_neg h1, if_neg h2, dif_pos h3, k] using (hb k).2
      · let k : Fin N := ⟨i.val - 3 * N, by omega⟩
        have he : dot (matrix c i) r = -r k := by
          unfold dot
          simp only [matrix, dif_neg h1, dif_neg h2, if_neg h3]
          exact dot_neg_unit r k
        rw [he]
        have hh : -r k ≤ B k := by have := (hb k).1; omega
        simpa only [state, if_neg h1, if_neg h2, dif_neg h3, k] using hh

#print axioms initial_valid
end Erdos406FinitePrefix
