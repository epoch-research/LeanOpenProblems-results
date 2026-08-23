import Submission.CorePositive
import Submission.PairShift
open Nat Finset BigOperators Int Polynomial
open Core

lemma coeff_series_mul_expand
    (q : ℕ → ℤ) {p : ℕ} (hp : 0 < p) (hq : ∀ n, q (n*p) = q n)
    (f : Polynomial ℤ) (n : ℕ) :
    PowerSeries.coeff (n*p)
        (PowerSeries.mk q * (Polynomial.expand ℤ p f : PowerSeries ℤ)) =
      PowerSeries.coeff n (PowerSeries.mk q * (f : PowerSeries ℤ)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_subset
    (s₁ := (Finset.antidiagonal n).image fun x => (x.1*p, x.2*p)), Finset.sum_image]
  · simp_rw [PowerSeries.coeff_mk, Polynomial.coeff_coe,
      Polynomial.coeff_expand_mul hp, hq]
  · intro x hx y hy heq
    simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp] using heq
  · simp_rw [Finset.subset_iff, Finset.mem_image, Finset.mem_antidiagonal]
    rintro _ ⟨x, rfl, rfl⟩
    simp_rw [Nat.add_mul]
  · simp_rw [Finset.mem_image, Finset.mem_antidiagonal]
    intro ⟨x,y⟩ heq hnmem
    by_cases hy : p ∣ y
    · obtain ⟨x', rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left hy).mpr
          (heq ▸ dvd_mul_left p n)
      obtain ⟨y', rfl⟩ := hy
      refine (hnmem ⟨⟨x',y'⟩, (Nat.mul_right_cancel_iff hp).mp ?_, by simp_rw [mul_comm]⟩).elim
      rw [← heq, mul_comm, mul_add]
    · rw [Polynomial.coeff_coe, Polynomial.coeff_expand hp, if_neg hy, mul_zero]

noncomputable def FNat (A B : ℕ) : ℤ :=
  PowerSeries.coeff B
    (Core.Qseries * (((1 + Polynomial.X : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ))

lemma base_eq_expand (p A : ℕ) :
    (1 + Polynomial.X^p : Polynomial ℤ)^A =
      Polynomial.expand ℤ p ((1+Polynomial.X)^A) := by
  rw [map_pow]
  simp

lemma FNat_base_scale {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (A B : ℕ) :
    PowerSeries.coeff (p*B)
      (Core.Qseries * (((1+Polynomial.X^p : Polynomial ℤ)^A : Polynomial ℤ) : PowerSeries ℤ)) =
      FNat A B := by
  rw [base_eq_expand, Nat.mul_comm p B]
  change PowerSeries.coeff (B*p)
      (PowerSeries.mk Core.qCoeff *
        (Polynomial.expand ℤ p ((1+Polynomial.X : Polynomial ℤ)^A) : PowerSeries ℤ)) = _
  rw [coeff_series_mul_expand Core.qCoeff hp.pos]
  · rfl
  · intro t
    simpa [Nat.mul_comm] using Core.qCoeff_mul_prime (hp := hp) (hp5 := hp5) (n := t)

lemma frobenius_expansion {p : ℕ} (hp : p.Prime) (A : ℕ) :
    (1+Polynomial.X : Polynomial ℤ)^(p*A) =
      ∑ j ∈ Finset.range (A+1),
        Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p ^ j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) := by
  rw [pow_mul, Core.frob_decomposition hp]
  rw [show (1 + Polynomial.X^p + Polynomial.C (p : ℤ) * Core.frobError p : Polynomial ℤ) =
      Polynomial.C (p : ℤ) * Core.frobError p + (1+Polynomial.X^p) by ring]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow, map_mul, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast]
  rw [show Polynomial.C ((p : ℤ)^j) = (p : Polynomial ℤ)^j by
    rw [map_pow]; simp]
  ring

lemma coeff_mul_one_add_pow (f : Polynomial ℤ) (N B : ℕ) :
    (f * (1+Polynomial.X)^N).coeff B =
      ∑ d ∈ Finset.range (B+1), f.coeff d * (N.choose (B-d) : ℤ) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.coeff_one_add_X_pow]

lemma sum_chooseSub_eq {f : ℕ → ℤ} {N B j : ℕ}
    (hzero : ∀ d, j < d → f d = 0) :
    (∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ)) =
      ∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ) := by
  by_cases hjB : j ≤ B
  · symm
    calc
      (∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ)) =
          ∑ d ∈ Finset.range (j+1), f d * (N.choose (B-d) : ℤ) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdj : d ≤ j := by
              simp only [Finset.mem_range] at hd
              omega
            rw [chooseSub, if_pos (le_trans hdj hjB)]
      _ = ∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ) := by
            apply Finset.sum_subset
            · intro d hd
              simp only [Finset.mem_range] at hd ⊢
              omega
            · intro d hdB hdj
              rw [hzero d (by simp only [Finset.mem_range] at hdB hdj; omega)]
              simp
  · have hBj : B < j := by omega
    calc
      (∑ d ∈ Finset.range (B+1), f d * (N.choose (B-d) : ℤ)) =
          ∑ d ∈ Finset.range (B+1), f d * (chooseSub N B d : ℤ) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [chooseSub, if_pos]
            simpa [Finset.mem_range] using (show d ≤ B by
              simp only [Finset.mem_range] at hd; omega)
      _ = ∑ d ∈ Finset.range (j+1), f d * (chooseSub N B d : ℤ) := by
            apply Finset.sum_subset
            · intro d hd
              simp only [Finset.mem_range] at hd ⊢
              omega
            · intro d hdj hdB
              have hnot : ¬ d ≤ B := by
                simp only [Finset.mem_range] at hdj hdB
                omega
              simp [chooseSub, hnot]

lemma errorPoly_coeff_zero {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) :
    (Core.errorPoly p j).coeff 0 = 0 := by
  have h := congr_arg (PowerSeries.coeff 0)
    (Core.Qseries_mul_frobError_pow hp hp5 hj)
  simp only [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_one, Core.Qseries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simp [Core.qCoeff, Polynomial.coeff_coe, Core.coeff_frobError, hj.ne'] at h
  exact h.symm

lemma errorPoly_coeff_above {p j d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) (hd : j < d) :
    (Core.errorPoly p j).coeff (p*d) = 0 := by
  have h := congr_arg (fun f : Polynomial ℤ => f.coeff (p*d))
    (Core.reflect_errorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (Core.errorPoly p j)).coeff (p*d) =
    (-Core.errorPoly p j).coeff (p*d) at h
  rw [Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt (show p*j < p*d by
      exact Nat.mul_lt_mul_of_pos_left hd hp.pos), Polynomial.coeff_neg] at h
  omega

lemma contracted_error_coeff_sum {p j A B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    (Core.errorPoly p j * (1+Polynomial.X^p)^(A-j)).coeff (p*B) =
      ∑ d ∈ Finset.range (j+1),
        (Core.errorPoly p j).coeff (p*d) * (chooseSub (A-j) B d : ℤ) := by
  rw [base_eq_expand]
  have hc := Polynomial.contract_mul_expand hp.ne_zero (Core.errorPoly p j)
    ((1+Polynomial.X : Polynomial ℤ)^(A-j))
  have heq := congr_arg (fun f : Polynomial ℤ => f.coeff B) hc
  change (Polynomial.contract p
      (Core.errorPoly p j * Polynomial.expand ℤ p ((1+Polynomial.X)^ (A-j)))).coeff B =
    (Polynomial.contract p (Core.errorPoly p j) * (1+Polynomial.X)^(A-j)).coeff B at heq
  rw [Polynomial.coeff_contract hp.ne_zero, coeff_mul_one_add_pow] at heq
  rw [Nat.mul_comm] at heq
  rw [heq]
  have hs := sum_chooseSub_eq (N := A-j) (B := B) (j := j)
    (f := fun d => (Polynomial.contract p (Core.errorPoly p j)).coeff d) (by
      intro d hd
      change (Polynomial.contract p (Core.errorPoly p j)).coeff d = 0
      rw [Polynomial.coeff_contract hp.ne_zero]
      simpa [Nat.mul_comm] using errorPoly_coeff_above hp hp5 hj hd)
  simpa only [Polynomial.coeff_contract hp.ne_zero, Nat.mul_comm] using hs

lemma correction_coeff_eq {p A B j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    PowerSeries.coeff (p*B)
      (Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ)) =
      ∑ d ∈ Finset.range (j+1),
        (p : ℤ)^j * (Core.errorPoly p j).coeff (p*d) * (A.choose j : ℤ) *
          (chooseSub (A-j) B d : ℤ) := by
  have herr := Core.Qseries_mul_frobError_pow hp hp5 hj
  have hs : Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * (A.choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) =
      PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
        ((Core.errorPoly p j * (1+Polynomial.X^p)^(A-j) : Polynomial ℤ) : PowerSeries ℤ) := by
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C]
    calc
      Core.Qseries * (PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.frobError p : PowerSeries ℤ)^j *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j)) =
        PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.Qseries * (Core.frobError p : PowerSeries ℤ)^j) *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by ring
      _ = PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
          (Core.errorPoly p j : PowerSeries ℤ) *
          ((1+Polynomial.X^p : Polynomial ℤ) : PowerSeries ℤ)^(A-j) := by rw [herr]
      _ = _ := by ring
  rw [hs, PowerSeries.coeff_C_mul, Polynomial.coeff_coe,
    contracted_error_coeff_sum hp hp5 hj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

lemma correction_coeff_dvd {p lev B Y j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) (hj : 0 < j) (hjA : j ≤ B+Y) :
    ((p : ℤ)^(3*(lev+1))) ∣
    PowerSeries.coeff (p*B)
      (Core.Qseries *
        ((Polynomial.C ((p : ℤ)^j * ((B+Y).choose j : ℤ)) * Core.frobError p^j *
          (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-j) : Polynomial ℤ) : PowerSeries ℤ)) := by
  rw [correction_coeff_eq hp hp5 hj]
  apply shifted_paired_sum_dvd hp hp5 hB hY hjA
  · exact errorPoly_coeff_zero hp hp5 hj
  · intro d hd
    exact Core.coeff_errorPoly_antisymm hp hp5 hj hd


lemma coe_finset_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) :
    ((∑ i ∈ s, f i : Polynomial ℤ) : PowerSeries ℤ) =
      ∑ i ∈ s, (f i : PowerSeries ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Polynomial.coe_add]

lemma FNat_scale_expansion {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (A B : ℕ) :
    FNat (p*A) (p*B) = FNat A B +
      ∑ i ∈ Finset.range A,
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * (A.choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^(A-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ)) := by
  unfold FNat
  rw [frobenius_expansion hp]
  rw [coe_finset_sum_poly]
  rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.natCast_one,
    mul_one, Polynomial.C_1, one_mul, Nat.sub_zero]
  rw [FNat_base_scale hp hp5]
  abel


lemma FNat_scale_supercongruence {p lev B Y : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y) :
    FNat (p*(B+Y)) (p*B) ≡ FNat (B+Y) B
      [ZMOD ((p : ℤ)^(3*(lev+1)))] := by
  rw [Int.modEq_iff_dvd]
  rw [FNat_scale_expansion hp hp5]
  -- The remaining difference is the negative of the correction sum.
  rw [show FNat (B+Y) B -
      (FNat (B+Y) B + ∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * ((B+Y).choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) =
      -(∑ i ∈ Finset.range (B+Y),
        PowerSeries.coeff (p*B)
          (Core.Qseries *
            ((Polynomial.C ((p : ℤ)^(i+1) * ((B+Y).choose (i+1) : ℤ)) *
              Core.frobError p^(i+1) *
              (1+Polynomial.X^p : Polynomial ℤ)^((B+Y)-(i+1)) : Polynomial ℤ) :
                PowerSeries ℤ))) by ring]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hiA : i+1 ≤ B+Y := by
    simp only [Finset.mem_range] at hi
    omega
  exact correction_coeff_dvd hp hp5 hB hY (by omega) hiA




