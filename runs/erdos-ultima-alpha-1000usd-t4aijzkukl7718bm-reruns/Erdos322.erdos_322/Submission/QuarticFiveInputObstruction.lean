import Submission.QuarticRationalSpecialization
import Submission.QuarticSquareMultiplier

/-! A five-adic obstruction to transferring five fourth powers into four
by a fixed square multiplier. This is not a representation-count bound. -/
namespace Erdos322Research.QuarticFiveInputObstruction

open QuarticSquareMultiplier

private lemma fourth_mod_five (x : ℕ) : x^4%5 ≤ 1 := by
  have h : ∀ x : Fin 5, x.val^4%5 ≤ 1 := by decide
  rw [Nat.pow_mod]
  exact h ⟨x%5,Nat.mod_lt _ (by decide)⟩

private lemma five_dvd_all {a : Fin 4 → ℕ} (h : 5 ∣ ∑ i, a i^4) :
    ∀ i, 5 ∣ a i := by
  have h0 := fourth_mod_five (a 0)
  have h1 := fourth_mod_five (a 1)
  have h2 := fourth_mod_five (a 2)
  have h3 := fourth_mod_five (a 3)
  have hs := Nat.mod_eq_zero_of_dvd h
  simp only [Fin.sum_univ_four] at hs
  have hz (i : Fin 4) : (a i)^4%5=0 := by
    fin_cases i
    · change (a 0)^4%5=0
      omega
    · change (a 1)^4%5=0
      omega
    · change (a 2)^4%5=0
      omega
    · change (a 3)^4%5=0
      omega
  intro i
  exact (by decide : Nat.Prime 5).dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero (hz i))

private theorem no_scaled_representation {n : ℕ} (hn : 5 ∣ n) (h625 : ¬625 ∣ n) :
    ∀ d : ℕ, 0 < d → ∀ a : Fin 4 → ℕ, ∑ i, a i^4 ≠ n*d^4 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd a he
    have h5 : 5 ∣ ∑ i, a i^4 := he ▸ dvd_mul_of_dvd_left hn _
    have ha := five_dvd_all h5
    have had (i : Fin 4) : 5*(a i/5)=a i := Nat.mul_div_cancel' (ha i)
    have hs : ∑ i, a i^4=625*(∑ i, (a i/5)^4) := by
      simp only [Fin.sum_univ_four]
      conv_lhs => rw [← had 0,← had 1,← had 2,← had 3]
      ring
    by_cases hdd : 5 ∣ d
    · have hdsmall : d/5 < d := Nat.div_lt_self hd (by decide)
      have hdp : 0 < d/5 := Nat.div_pos (Nat.le_of_dvd hd hdd) (by decide)
      have hd5 : 5*(d/5)=d := Nat.mul_div_cancel' hdd
      apply ih (d/5) hdsmall hdp (fun i ↦ a i/5)
      have he' : 625*(∑ i, (a i/5)^4)=625*(n*(d/5)^4) := by
        calc
          _ = n*d^4 := hs.symm.trans he
          _ = _ := by
            conv_lhs => rw [← hd5]
            ring
      omega
    · apply h625
      have hdiv : 625 ∣ n*d^4 := he ▸ ⟨_,hs⟩
      have hc : (625 : ℕ).Coprime (d^4) := by
        simpa using ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hdd).pow 4 4
      exact hc.dvd_of_dvd_mul_right hdiv

/-- Rational denominators cannot evade the five-adic restriction. -/
theorem represented_five_dvd_imp_625_dvd {n : ℕ} (hn : Represented n) (h5 : 5 ∣ n) :
    625 ∣ n := by
  by_contra h625
  obtain ⟨a,he⟩ := hn
  let d := ∏ i, (a i).den
  have hd : 0 < d := Finset.prod_pos (fun i _ ↦ (a i).den_pos)
  let b : Fin 4 → ℤ := fun i ↦ (a i).num*(d/(a i).den)
  have hb (i : Fin 4) : (b i : ℚ)=(d : ℚ)*a i := by
    have hdiv : (a i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hm : ((a i).den : ℚ)*(d/(a i).den : ℕ)=d := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    dsimp only [b]
    push_cast
    calc
      ((a i).num : ℚ)*(d/(a i).den : ℕ) =
          (a i*(a i).den)*(d/(a i).den : ℕ) := by rw [Rat.mul_den_eq_num]
      _ = (d : ℚ)*a i := by rw [mul_assoc,hm,mul_comm]
  have hq : ∑ i, (b i : ℚ)^4=(n : ℚ)*d^4 := by
    simp_rw [hb,mul_pow]
    rw [← Finset.mul_sum,he,mul_comm]
  have hz : ∑ i, (b i)^4=(n : ℤ)*d^4 := by exact_mod_cast hq
  have ha : ∑ i, (b i).natAbs^4=n*d^4 := by
    have hh : ∑ i, ((b i).natAbs : ℤ)^4=(n : ℤ)*d^4 := by
      simpa only [Int.natCast_natAbs,Even.pow_abs (by decide : Even 4)] using hz
    exact_mod_cast hh
  exact no_scaled_representation h5 h625 d hd (fun i ↦ (b i).natAbs) ha

theorem represented_strip_625 {n : ℕ} (h : Represented (625*n)) : Represented n := by
  obtain ⟨a,ha⟩ := h
  refine ⟨fun i ↦ a i/5,?_⟩
  simp only [div_pow,← Finset.sum_div]
  rw [ha]
  push_cast
  ring

/-- No positive fixed multiplier can handle both square-input tests `1` and
`5` when the output must be a sum of only four rational fourth powers. -/
theorem no_multiplier_for_one_and_five (C : ℕ) (hC : 0 < C) :
    ¬(Represented C ∧ Represented (25*C)) := by
  induction C using Nat.strong_induction_on with
  | h C ih =>
    rintro ⟨h1,h5⟩
    by_cases hd : 5 ∣ C
    · have h625 := represented_five_dvd_imp_625_dvd h1 hd
      have hc : 625*(C/625)=C := Nat.mul_div_cancel' h625
      have hsmall : C/625<C := Nat.div_lt_self hC (by decide)
      have hp : 0 < C/625 := Nat.div_pos (Nat.le_of_dvd hC h625) (by decide)
      apply ih (C/625) hsmall hp
      constructor
      · apply represented_strip_625
        simpa only [hc] using h1
      · apply represented_strip_625
        convert h5 using 1
        nlinarith [hc]
    · have hh : 625 ∣ 25*C := represented_five_dvd_imp_625_dvd h5 ⟨5*C,by ring⟩
      have hh' : 25 ∣ C := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 25)
        (by simpa using hh : 25*25 ∣ 25*C)
      exact hd ((by decide : 5 ∣ 25).trans hh')

/-- Consequently no rational polynomial formula, even with poles, can
universally square a five-coordinate quartic norm into four coordinates
with a positive fixed natural multiplier. -/
theorem no_five_input_rational_square_formula
    (C : ℕ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (D : MvPolynomial (Fin 5) ℚ) (hD : D ≠ 0) :
    ∑ i, P i^4 ≠ D^4*(MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^2) := by
  intro h
  apply no_multiplier_for_one_and_five C hC
  constructor
  · obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
      (MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^2) hD h ![1,0,0,0,0]
    refine ⟨b,?_⟩
    simpa [Fin.sum_univ_succ] using hb
  · obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
      (MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^2) hD h (fun _ ↦ 1)
    refine ⟨b,?_⟩
    simpa [mul_comm] using hb

/-- The five-adic valuation of a positive rationally represented natural
number is a multiple of four. -/
theorem represented_valuation_multiple_four (n : ℕ) (hn : 0 < n) (h : Represented n) :
    4 ∣ padicValNat 5 n := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hd : 5 ∣ n
    · have h625 := represented_five_dvd_imp_625_dvd h hd
      have hp : 0 < n/625 := Nat.div_pos (Nat.le_of_dvd hn h625) (by decide)
      have hs : n/625<n := Nat.div_lt_self hn (by decide)
      have he : 625*(n/625)=n := Nat.mul_div_cancel' h625
      have hr : Represented (n/625) := represented_strip_625 (by simpa only [he] using h)
      have hi := ih (n/625) hs hp hr
      conv_rhs => rw [← he]
      rw [padicValNat.mul (by decide) hp.ne']
      have hval : padicValNat 5 625=4 := by
        exact padicValNat.prime_pow 4
      rw [hval]
      exact dvd_add (dvd_refl 4) hi
    · rw [padicValNat.eq_zero_of_not_dvd hd]
      exact dvd_zero 4

/-- Input targets `1` and `5` already force any universal power exponent to
be divisible by four. No assertion of existence at those exponents is made. -/
theorem power_exponent_multiple_four (C e : ℕ) (hC : 0 < C)
    (h1 : Represented C) (h5 : Represented (5^e*C)) : 4 ∣ e := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hv1 := represented_valuation_multiple_four C hC h1
  have hv5 := represented_valuation_multiple_four (5^e*C) (by positivity) h5
  rw [padicValNat.mul (by positivity) hC.ne',padicValNat.prime_pow] at hv5
  exact (Nat.dvd_add_iff_right hv1).mpr (by simpa only [add_comm] using hv5)

/-- The obstruction covers rational formulas with arbitrary polynomial degrees
and denominator poles. -/
theorem five_input_rational_power_exponent
    (C e : ℕ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (D : MvPolynomial (Fin 5) ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*(MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^e)) :
    4 ∣ e := by
  apply power_exponent_multiple_four C e hC
  · obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
      (MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^e) hD h ![1,0,0,0,0]
    refine ⟨b,?_⟩
    simpa [Fin.sum_univ_succ] using hb
  · obtain ⟨b,hb⟩ := QuarticRationalSpecialization.multivariate_specialization P D
      (MvPolynomial.C (C : ℚ)*(∑ j : Fin 5, MvPolynomial.X j^4)^e) hD h (fun _ ↦ 1)
    refine ⟨b,?_⟩
    simpa [mul_comm] using hb

/-- Allowing a positive rational rather than natural fixed multiplier does
not remove the exponent restriction. -/
theorem rational_multiplier_power_exponent
    (C : ℚ) (e : ℕ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 5) ℚ)
    (D : MvPolynomial (Fin 5) ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*(MvPolynomial.C C*(∑ j : Fin 5, MvPolynomial.X j^4)^e)) :
    4 ∣ e := by
  have hd : (0 : ℚ) < C.den := by exact_mod_cast C.den_pos
  have hnum : (0 : ℚ) < C.num := by rw [← Rat.mul_den_eq_num]; positivity
  have hnum' : (0 : ℤ) < C.num := by exact_mod_cast hnum
  have hcast : ((C.num.toNat : ℕ) : ℚ)=C.num := by
    exact_mod_cast Int.toNat_of_nonneg hnum'.le
  let N : ℕ := C.num.toNat*C.den^3
  have hN : 0 < N := by
    dsimp only [N]
    exact Nat.mul_pos (by omega : 0 < C.num.toNat) (pow_pos C.den_pos 3)
  have hNq : (N : ℚ)=C*(C.den : ℚ)^4 := by
    dsimp only [N]
    push_cast
    rw [hcast,← Rat.mul_den_eq_num]
    ring
  let P' : Fin 4 → MvPolynomial (Fin 5) ℚ := fun i ↦ MvPolynomial.C (C.den : ℚ)*P i
  apply five_input_rational_power_exponent N e hN P' D hD
  simp only [P',mul_pow,← Finset.mul_sum,h,hNq,map_mul,map_pow]
  ring

end Erdos322Research.QuarticFiveInputObstruction
