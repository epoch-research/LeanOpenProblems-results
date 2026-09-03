import Submission.LambertPrimeBlocks

/-!
Prime-power congruences for the original Lambert coefficients with singleton
blocks included. Auxiliary arithmetic only; not a settlement of Erdős 68.
-/

namespace LambertDoldCongruence

open Erdos68Development LambertPrimeScaling MvPolynomial

noncomputable def powers {k : ℕ} (f : Fin k → ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm f

@[simp] lemma powers_apply {k : ℕ} (f : Fin k → ℕ) (i : Fin k) : powers f i = f i := rfl

lemma product_X_eq {k : ℕ} (f : Fin k → ℕ) :
    (∏ i : Fin k, (X i : MvPolynomial (Fin k) ℤ)^f i) = monomial (powers f) 1 := by
  rw [monomial_eq, C_1, one_mul]
  exact (Finsupp.prod_fintype (powers f) (fun i n => (X i : MvPolynomial (Fin k) ℤ)^n)
    (by simp)).symm

lemma coefficient_sum_X_pow {k : ℕ} (f : Fin k → ℕ) :
    coeff (powers f) ((∑ i : Fin k, (X i : MvPolynomial (Fin k) ℤ))^(∑ i, f i)) =
      (Nat.multinomial Finset.univ f : ℤ) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  have ht (g : Fin k → ℕ) :
      coeff (powers f) ((Nat.multinomial Finset.univ g : MvPolynomial (Fin k) ℤ) *
        ∏ i : Fin k, (X i : MvPolynomial (Fin k) ℤ)^g i) =
      if g=f then (Nat.multinomial Finset.univ f : ℤ) else 0 := by
    rw [product_X_eq, ← C_eq_coe_nat, C_mul_monomial, mul_one, coeff_monomial]
    have he : powers g = powers f ↔ g=f := Finsupp.equivFunOnFinite.symm.injective.eq_iff
    by_cases h : g=f <;> simp [he, h]
  simp_rw [ht]
  have hf : f ∈ Finset.piAntidiag Finset.univ (∑ i, f i) := by
    simp [Finset.mem_piAntidiag]
  simp [hf]

lemma uniform_eq_coefficient (d k : ℕ) :
    (uniform d k : ℤ) = coeff (powers (fun _ : Fin k => d))
      ((∑ i : Fin k, (X i : MvPolynomial (Fin k) ℤ))^(d*k)) := by
  have h := coefficient_sum_X_pow (fun _ : Fin k => d)
  simpa [Nat.multinomial, uniform, Nat.mul_comm] using h.symm

lemma frobenius_lift {σ : Type*} (f : MvPolynomial σ ℤ) (p r m : ℕ) (hp : p.Prime) :
    C ((p : ℤ)^(r+1)) ∣ f^(p^(r+1)*m) - expand p (f^(p^r*m)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hbase : (p : MvPolynomial σ ℤ) ∣ f^p-expand p f := by
    rw [← C_eq_coe_nat, C_dvd_iff_zmod]
    simp only [map_sub, map_pow, map_expand, expand_zmod, sub_self]
  have hlift := dvd_sub_pow_of_dvd_sub hbase r
  have hmore := hlift.trans (sub_dvd_pow_sub_pow ((f^p)^(p^r)) ((expand p f)^(p^r)) m)
  rw [map_pow, C_eq_coe_nat]
  simpa only [map_pow, pow_mul, pow_succ', mul_assoc] using hmore

lemma uniform_prime_power_lift (p r d k : ℕ) (hp : p.Prime)
    (hdk : p^(r+1) ∣ (p*d)*k) :
    Nat.ModEq (p^(r+1)) (uniform (p*d) k) (uniform d k) := by
  classical
  obtain ⟨m, hm⟩ := hdk
  have hm' : d*k = p^r*m := Nat.eq_of_mul_eq_mul_left hp.pos (by
    simpa only [pow_succ', mul_assoc] using hm)
  let f : MvPolynomial (Fin k) ℤ := ∑ i : Fin k, X i
  have h := (C_dvd_iff_dvd_coeff _ _).mp (frobenius_lift f p r m hp)
    (powers (fun _ : Fin k => p*d))
  have he : powers (fun _ : Fin k => p*d) = p • powers (fun _ : Fin k => d) := by
    ext i
    simp [smul_eq_mul]
  rw [coeff_sub, he, coeff_expand_smul p hp.ne_zero] at h
  rw [← hm, ← hm', ← he] at h
  change (p : ℤ)^(r+1) ∣
    coeff (powers (fun _ : Fin k => p*d)) (f^((p*d)*k)) -
      coeff (powers (fun _ : Fin k => d)) (f^(d*k)) at h
  rw [← uniform_eq_coefficient, ← uniform_eq_coefficient] at h
  exact (Nat.modEq_iff_dvd.mpr (by simpa only [Nat.cast_pow] using h)).symm

lemma prime_power_dvd_uniform (p r d k : ℕ) (hp : p.Prime) (hkp : 0 < k)
    (hdk : p^(r+1) ∣ d*k) (hpd : ¬p ∣ d) :
    p^(r+1) ∣ uniform d k := by
  by_cases hd0 : d=0
  · subst d
    simp at hpd
  have hdpos : 0 < d := by omega
  have hc : (p^(r+1)).Coprime d :=
    ((hp.coprime_iff_not_dvd).mpr hpd).pow_left _
  have hk : p^(r+1) ∣ k := hc.dvd_of_dvd_mul_left hdk
  exact (hk.trans (Nat.dvd_factorial hkp (le_refl k))).trans
    (factorial_dvd_uniform_multinomial hdpos k)

/-- Dold-type prime-power congruence for the coefficients that include
singleton blocks. -/
theorem fullCoeff_dold (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Nat.ModEq (p^(r+1)) (fullCoeff (p^(r+1)*m)) (fullCoeff (p^r*m)) := by
  have hp0 := hp.pos
  have hn : 0 < p^r*m := by positivity
  rw [pow_succ', mul_assoc, fullCoeff_uniform, fullCoeff_uniform]
  rw [← pow_succ' p r]
  trans ∑ d ∈ (p*(p^r*m)).divisors,
    if p ∣ d then uniform d ((p*(p^r*m))/d) else 0
  · apply Nat.ModEq.sum
    intro d hd
    by_cases hpd : p ∣ d
    · rw [if_pos hpd]
    · rw [if_neg hpd]
      apply Nat.modEq_zero_iff_dvd.mpr
      have hdv := Nat.dvd_of_mem_divisors hd
      have hdpos := Nat.pos_of_dvd_of_pos hdv (Nat.mul_pos hp.pos hn)
      apply prime_power_dvd_uniform p r d ((p*(p^r*m))/d) hp
        (Nat.div_pos (Nat.le_of_dvd (by positivity) hdv) hdpos) ?_ hpd
      rw [Nat.mul_div_cancel' hdv, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
  · rw [← Finset.sum_filter, scaled_divisors p (p^r*m) hp.pos hn,
      Finset.sum_image (by intro a _ b _ hab; exact (Nat.mul_left_cancel_iff hp.pos).mp hab)]
    apply Nat.ModEq.sum
    intro d hd
    rw [Nat.mul_div_mul_left (p^r*m) d hp.pos]
    apply uniform_prime_power_lift p r d ((p^r*m)/d) hp
    rw [mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd),
      ← mul_assoc, ← pow_succ']
    exact dvd_mul_right _ _

/-- The exact Lambert coefficients obey the same stronger congruence,
with the smaller index's singleton factorial retained on the right. -/
theorem lambertCoeff_dold (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Nat.ModEq (p^(r+1)) (lambertCoeff (p^(r+1)*m))
      (lambertCoeff (p^r*m)+(p^r*m).factorial) := by
  have hp0 := hp.pos
  have hn : 0 < p^(r+1)*m := by positivity
  have h := fullCoeff_dold p r m hp hm
  rw [fullCoeff_eq _ hn, fullCoeff_eq _ (by positivity)] at h
  have hd : p^(r+1) ∣ (p^(r+1)*m).factorial :=
    (dvd_mul_right (p^(r+1)) m).trans (Nat.dvd_factorial hn (le_refl _))
  have he : Nat.ModEq (p^(r+1))
      (lambertCoeff (p^(r+1)*m)+(p^(r+1)*m).factorial)
      (lambertCoeff (p^(r+1)*m)) := by
    simpa only [Nat.add_zero] using
      (Nat.ModEq.refl (lambertCoeff (p^(r+1)*m))).add
        (Nat.modEq_zero_iff_dvd.mpr hd)
  exact he.symm.trans h

#print axioms coefficient_sum_X_pow
#print axioms uniform_prime_power_lift
#print axioms fullCoeff_dold
#print axioms lambertCoeff_dold

end LambertDoldCongruence
