import FormalConjecturesUtil

/-! Injectivity of evaluation at a reduced rational number when polynomial
coefficient differences have absolute values below its denominator. This
concerns individual values, not preservation of Sidonness. -/
namespace Erdos773.RationalDigitInjection
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000

lemma denominator_divides {p q : ℕ} (hq : 0<q) (hc : p.Coprime q)
    {P : ℤ[X]} (hr : P.eval₂ (Int.castRingHom ℚ) ((p:ℚ)/q)=0) :
    (q:ℤ) ∣ P.leadingCoeff := by
  let r : ℚ := (p:ℚ)/q
  let a : ℤ := IsFractionRing.num ℤ r
  let b : ℤ := IsFractionRing.den ℤ r
  have hrel : r*(b:ℚ)=(a:ℚ) :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (A := ℤ)).mpr rfl
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcross : (p:ℚ)*(b:ℚ)=(q:ℚ)*(a:ℚ) := by
    dsimp only [r] at hrel
    field_simp at hrel
    nlinarith only [hrel]
  have hi : (p:ℤ)*b=(q:ℤ)*a := by exact_mod_cast hcross
  have hd : (q:ℤ) ∣ (p:ℤ)*b := ⟨a,hi⟩
  have hcop : IsCoprime (q:ℤ) (p:ℤ) := Nat.isCoprime_iff_coprime.mpr hc.symm
  have hqb : (q:ℤ) ∣ b := hcop.dvd_of_dvd_mul_left hd
  have haeval : Polynomial.aeval r P=0 := by
    simpa only [aeval_def,r] using hr
  exact hqb.trans (den_dvd_of_is_root haeval)

/-- Small coefficient differences prevent evaluation aliases. They do not
prevent a relation between sums of squares of several different values. -/
theorem eval_injective {p q : ℕ} (hq : 0<q) (hc : p.Coprime q)
    {P Q : ℤ[X]} (hsmall : ∀ n, |P.coeff n-Q.coeff n|<(q:ℤ))
    (he : P.eval₂ (Int.castRingHom ℚ) ((p:ℚ)/q)=Q.eval₂ (Int.castRingHom ℚ) ((p:ℚ)/q)) :
    P=Q := by
  have hr : (P-Q).eval₂ (Int.castRingHom ℚ) ((p:ℚ)/q)=0 := by simp [he]
  have hd := denominator_divides hq hc hr
  have hl : |(P-Q).leadingCoeff|<(q:ℤ) := by
    simpa only [leadingCoeff,coeff_sub] using hsmall (P-Q).natDegree
  exact sub_eq_zero.mp (leadingCoeff_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hl))

lemma coeff_le_value_one {P : ℤ[X]} (hP : ∀ n, 0 ≤ P.coeff n) (n : ℕ) :
    P.coeff n ≤ P.eval 1 := by
  rw [eval_eq_sum,Polynomial.sum_def]
  simp only [one_pow,mul_one]
  by_cases hn : n ∈ P.support
  · exact Finset.single_le_sum (fun k hk => hP k) hn
  · rw [notMem_support_iff.mp hn]
    exact Finset.sum_nonneg (fun k hk => hP k)

#print axioms coeff_le_value_one

#print axioms denominator_divides
#print axioms eval_injective
end
end Erdos773.RationalDigitInjection
