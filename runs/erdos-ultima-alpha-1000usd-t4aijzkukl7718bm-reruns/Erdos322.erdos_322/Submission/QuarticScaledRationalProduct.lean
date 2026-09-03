import Submission.QuarticRationalSpecialization
import Submission.QuarticSquareMultiplier

/-! No fixed positive scale makes generic multiplication of quartic norms
possible by four rational fourth powers. This is a construction obstruction,
not a representation-count upper bound. -/
namespace Erdos322Research.QuarticScaledRationalProduct

open QuarticSquareMultiplier
open Finset
set_option Elab.async false

private lemma residue_test (r : Fin 16) : r.val ≤ 4 → (2*r.val)%16 ≤ 4 →
    (3*r.val)%16 ≤ 4 → (6*r.val)%16 ≤ 4 → r.val=0 := by
  revert r
  decide

/-- Four small tests defeat every positive fixed multiplier, even when
arbitrary rational denominators are allowed in the representations. -/
theorem no_four_scaled_levels (C : ℕ) (hC : 0 < C) :
    ¬ (Represented C ∧ Represented (2*C) ∧ Represented (3*C) ∧ Represented (6*C)) := by
  induction C using Nat.strong_induction_on with
  | h C ih =>
    rintro ⟨h1,h2,h3,h6⟩
    have hc : C%16=0 := by
      apply residue_test ⟨C%16,Nat.mod_lt _ (by decide)⟩ (represented_mod_sixteen h1)
      · simpa only [Nat.mul_mod,Nat.mod_mod,Nat.reduceMod] using represented_mod_sixteen h2
      · simpa only [Nat.mul_mod,Nat.mod_mod,Nat.reduceMod] using represented_mod_sixteen h3
      · simpa only [Nat.mul_mod,Nat.mod_mod,Nat.reduceMod] using represented_mod_sixteen h6
    have hd : 16 ∣ C := Nat.dvd_of_mod_eq_zero hc
    have hp : 0 < C/16 := Nat.div_pos (Nat.le_of_dvd hC hd) (by decide)
    have hs : C/16 < C := Nat.div_lt_self hC (by decide)
    have he : 16*(C/16)=C := Nat.mul_div_cancel' hd
    have hg (v : ℕ) (hv : Represented (v*C)) : Represented (v*(C/16)) := by
      apply represented_strip_sixteen
      convert hv using 1
      nlinarith [he]
    exact ih (C/16) hs hp ⟨by simpa using hg 1 (by simpa using h1), hg 2 h2, hg 3 h3, hg 6 h6⟩

/-- Small nonnegative integral levels used in the obstruction. -/
lemma represented_one : Represented 1 := by
  exact ⟨![1,0,0,0],by norm_num [Fin.sum_univ_succ]⟩
lemma represented_two : Represented 2 := by
  exact ⟨![1,1,0,0],by norm_num [Fin.sum_univ_succ]⟩
lemma represented_three : Represented 3 := by
  exact ⟨![1,1,1,0],by norm_num [Fin.sum_univ_succ]⟩

/-- There is no positive universal scaled multiplicative closure, regardless
of how a proposed output representation is chosen. -/
theorem no_universal_product_scale (C : ℕ) (hC : 0 < C) :
    ¬ (∀ m n : ℕ, Represented m → Represented n → Represented (C*m*n)) := by
  intro h
  apply no_four_scaled_levels C hC
  refine ⟨?_,?_,?_,?_⟩
  · simpa using h 1 1 represented_one represented_one
  · simpa [mul_comm] using h 1 2 represented_one represented_two
  · simpa [mul_comm] using h 1 3 represented_one represented_three
  · simpa [mul_assoc, mul_comm, mul_left_comm] using h 2 3 represented_two represented_three

/-- Specialization remains valid at apparent poles of a rational formula. -/
theorem formula_gives_product_scale
    (C : ℕ) (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0)
    (h : ∑ i, P i^4 = D^4*(MvPolynomial.C (C : ℚ)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4))) :
    ∀ m n : ℕ, Represented m → Represented n → Represented (C*m*n) := by
  rintro m n ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨c,hc⟩ := QuarticRationalSpecialization.multivariate_specialization P D
    (MvPolynomial.C (C : ℚ)*(∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4)) hD h (Sum.elim a b)
  refine ⟨c,?_⟩
  simpa only [map_mul,map_sum,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,
    Sum.elim_inl,Sum.elim_inr,ha,hb,Nat.cast_mul] using hc

/-- No generic rational four-output product identity has a positive fixed
natural multiplier. Denominators may depend on all eight input coordinates. -/
theorem no_scaled_rational_product
    (C : ℕ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0) :
    ∑ i, P i^4 ≠ D^4*(MvPolynomial.C (C : ℚ)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4)) := by
  intro h
  exact no_universal_product_scale C hC (formula_gives_product_scale C P D hD h)

/-- Multiplying a positive rational constant by a fourth power clears it to
 a positive natural constant. -/
lemma natural_fourth_multiple (C : ℚ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧ (m : ℚ)=C*(d : ℚ)^4 := by
  let m := C.num.natAbs*C.den^3
  have hn : (C.num.natAbs : ℚ) = C.num := by
    have hh : (C.num.natAbs : ℤ)=C.num := by
      rw [Int.natCast_natAbs,abs_of_nonneg (Rat.num_nonneg.mpr hC.le)]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℚ)) hh
  have he : (m : ℚ)=C*(C.den : ℚ)^4 := by
    dsimp only [m]
    push_cast
    rw [hn,← Rat.mul_den_eq_num C]
    ring
  have hm : 0 < m := by
    have hp : (0 : ℚ) < m := by rw [he]; positivity
    exact_mod_cast hp
  exact ⟨C.den,m,C.den_pos,hm,he⟩

/-- The same four tests rule out a positive rational, rather than just
natural, fixed multiplier. -/
theorem no_four_scaled_rational_levels (C : ℚ) (hC : 0 < C) :
    ¬ ((∃ a : Fin 4 → ℚ, ∑ i, a i^4 = C) ∧
      (∃ a : Fin 4 → ℚ, ∑ i, a i^4 = 2*C) ∧
      (∃ a : Fin 4 → ℚ, ∑ i, a i^4 = 3*C) ∧
      (∃ a : Fin 4 → ℚ, ∑ i, a i^4 = 6*C)) := by
  rintro ⟨h1,h2,h3,h6⟩
  obtain ⟨d,m,hd,hm,he⟩ := natural_fourth_multiple C hC
  have hg (v : ℕ) (hv : ∃ a : Fin 4 → ℚ, ∑ i, a i^4=(v : ℚ)*C) :
      Represented (v*m) := by
    obtain ⟨a,ha⟩ := hv
    refine ⟨fun i ↦ (d : ℚ)*a i,?_⟩
    simp only [mul_pow,← Finset.mul_sum,ha,Nat.cast_mul,he]
    ring
  exact no_four_scaled_levels m hm ⟨by simpa using hg 1 (by simpa using h1),
    hg 2 h2,hg 3 h3,hg 6 h6⟩

/-- Allowing an arbitrary positive rational scale does not rescue a generic
rational norm-product formula. -/
theorem no_positive_rational_product_scale
    (C : ℚ) (hC : 0 < C) (P : Fin 4 → MvPolynomial (Fin 4 ⊕ Fin 4) ℚ)
    (D : MvPolynomial (Fin 4 ⊕ Fin 4) ℚ) (hD : D ≠ 0) :
    ∑ i, P i^4 ≠ D^4*(MvPolynomial.C C*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
      (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4)) := by
  intro h
  have hs (m n : ℕ) (hm : Represented m) (hn : Represented n) :
      ∃ c : Fin 4 → ℚ, ∑ i, c i^4=C*(m : ℚ)*(n : ℚ) := by
    obtain ⟨a,ha⟩ := hm
    obtain ⟨b,hb⟩ := hn
    obtain ⟨c,hc⟩ := QuarticRationalSpecialization.multivariate_specialization P D
      (MvPolynomial.C C*(∑ i : Fin 4, MvPolynomial.X (Sum.inl i)^4)*
        (∑ i : Fin 4, MvPolynomial.X (Sum.inr i)^4)) hD h (Sum.elim a b)
    refine ⟨c,?_⟩
    simpa only [map_mul,map_sum,map_pow,MvPolynomial.eval_C,MvPolynomial.eval_X,
      Sum.elim_inl,Sum.elim_inr,ha,hb] using hc
  apply no_four_scaled_rational_levels C hC
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hs 1 1 represented_one represented_one
  · simpa [mul_comm] using hs 1 2 represented_one represented_two
  · simpa [mul_comm] using hs 1 3 represented_one represented_three
  · simpa [mul_assoc,mul_comm,mul_left_comm,show (2 : ℚ)*3=6 by norm_num] using
      hs 2 3 represented_two represented_three

end Erdos322Research.QuarticScaledRationalProduct
