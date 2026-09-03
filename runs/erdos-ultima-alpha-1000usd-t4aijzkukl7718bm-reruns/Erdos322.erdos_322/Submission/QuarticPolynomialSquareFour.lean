import Submission.QuarticQuadraticModFive
import Submission.QuarticAutomaticHomogeneity
import Submission.LargeCountQuarticTransfer

/-! Polynomial quartic-norm squaring with multiplier four is impossible over
Q, even if required only above a fixed multiplicity threshold. This does not
exclude arbitrary rational maps or settle the representation-count conjecture. -/
namespace Erdos322Research.QuarticPolynomialSquareFour
noncomputable section
open Finset MvPolynomial QuarticQuadraticModFive
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

private lemma degree_map_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial (Fin 4) R) : (map f P).totalDegree ≤ P.totalDegree :=
  Finset.sup_mono (support_map_subset f P)

private lemma degree_map_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) (P : MvPolynomial (Fin 4) R) :
    (map f P).totalDegree=P.totalDegree := by
  unfold totalDegree
  rw [support_map_of_injective P hf]

private lemma mod_five_anisotropic (v : Fin 4 → ZMod 5)
    (h : ∑ i, v i^4=0) : ∀ i, v i=0 := by
  have hc : ∀ v : Fin 4 → ZMod 5, (∑ i, v i^4)=0 → ∀ i, v i=0 := by decide +kernel
  exact hc v h

private lemma quadratic_eq_zero_of_eval_zero (P : MvPolynomial (Fin 4) (ZMod 5))
    (hd : P.totalDegree ≤ 2) (h : ∀ x : Vec, eval x P=0) : P=0 := by
  by_contra hp
  have hh := quadratic_zero_bound P hp hd
  simp only [h,filter_true,card_univ,Fintype.card_fun,Fintype.card_fin,ZMod.card] at hh
  norm_num at hh

private lemma degree_of_five_mul (P Q : MvPolynomial (Fin 4) ℤ)
    (h : P=C 5*Q) (hd : P.totalDegree ≤ 2) : Q.totalDegree ≤ 2 := by
  by_cases hQ : Q=0
  · simp [hQ]
  · rw [h,totalDegree_mul_of_isDomain (by norm_num : (C 5 : MvPolynomial (Fin 4) ℤ) ≠ 0) hQ] at hd
    simpa only [totalDegree_C,zero_add] using hd

/-- Denominator descent at five rules out the integral numerator identity
for every nonzero common integer denominator. -/
theorem no_integer_scaled_quadratic (d : ℤ) (hd : d ≠ 0)
    (P : Fin 4 → MvPolynomial (Fin 4) ℤ) (hdeg : ∀ i, (P i).totalDegree ≤ 2) :
    ¬ (∑ i, P i^4 = 4*(C d)^4*(∑ j : Fin 4, X j^4)^2) := by
  have aux : ∀ n : ℕ, ∀ d : ℤ, d.natAbs=n → d ≠ 0 →
      ∀ P : Fin 4 → MvPolynomial (Fin 4) ℤ, (∀ i, (P i).totalDegree ≤ 2) →
      (∑ i, P i^4 = 4*(C d)^4*(∑ j : Fin 4, X j^4)^2) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hn hd P hdeg he
      let rho : ℤ →+* ZMod 5 := Int.castRingHom (ZMod 5)
      let A : Fin 4 → MvPolynomial (Fin 4) (ZMod 5) := fun i ↦ map rho (P i)
      have hAdeg (i : Fin 4) : (A i).totalDegree ≤ 2 := (degree_map_le rho (P i)).trans (hdeg i)
      have hA : ∑ i, A i^4 = 4*(C (rho d))^4*(∑ j : Fin 4, X j^4)^2 := by
        simpa only [map_sum,map_pow,map_mul,map_ofNat,map_C,map_X,A] using congrArg (map rho) he
      by_cases hdiv : (5 : ℤ) ∣ d
      · have hzero : rho d=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 5).mpr hdiv
        have hsum : ∑ i, A i^4=0 := by simpa [hzero] using hA
        have hAzero (i : Fin 4) : A i=0 := by
          apply quadratic_eq_zero_of_eval_zero (A i) (hAdeg i)
          intro x
          have hx : ∑ j, (eval x (A j))^4=0 := by
            simpa only [map_sum,map_pow,map_zero] using congrArg (eval x) hsum
          exact mod_five_anisotropic _ hx i
        have hPdiv (i : Fin 4) : C (5 : ℤ) ∣ P i :=
          (C_dvd_iff_map_hom_eq_zero rho 5 (fun z ↦ ZMod.intCast_zmod_eq_zero_iff_dvd z 5) (P i)).mpr (hAzero i)
        choose Q hQ using hPdiv
        obtain ⟨e,heq⟩ := hdiv
        have he0 : e ≠ 0 := by intro h; apply hd; simp [heq,h]
        have hlt : e.natAbs < n := by
          have hab : d.natAbs=5*e.natAbs := by rw [heq,Int.natAbs_mul]; rfl
          have hpos : 0 < e.natAbs := Int.natAbs_pos.mpr he0
          omega
        apply ih e.natAbs hlt e rfl he0 Q (fun i ↦ degree_of_five_mul (P i) (Q i) (hQ i) (hdeg i))
        apply mul_left_cancel₀ (pow_ne_zero 4 (by norm_num : (C 5 : MvPolynomial (Fin 4) ℤ) ≠ 0))
        calc
          (C 5)^4*(∑ i, Q i^4) = ∑ i, (C 5*Q i)^4 := by simp only [mul_pow,Finset.mul_sum]
          _ = 4*(C d)^4*(∑ j : Fin 4, X j^4)^2 := by simpa only [← hQ] using he
          _ = (C 5)^4*(4*(C e)^4*(∑ j : Fin 4, X j^4)^2) := by rw [heq,map_mul]; ring
      · have hd5 : rho d ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 5).not.mpr hdiv
        have hpow : (rho d)^4=1 := by simpa only [if_neg hd5] using fourth_value (rho d)
        have hpowC : (C (rho d))^4=(1 : MvPolynomial (Fin 4) (ZMod 5)) := by rw [← map_pow,hpow,map_one]
        apply no_quadratic_square_multiplier_four A hAdeg
        intro x
        have hx := congrArg (eval x) hA
        rw [hpowC] at hx
        simpa only [map_sum,map_pow,map_mul,map_ofNat,map_one,eval_X,mul_one] using hx
  exact aux d.natAbs d rfl hd P hdeg

/-- A common integer denominator for finitely many rational polynomials. -/
lemma common_integer_denominator (P : Fin 4 → MvPolynomial (Fin 4) ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ A : Fin 4 → MvPolynomial (Fin 4) ℤ,
      ∀ i, map (Int.castRingHom ℚ) (A i) = C (d : ℚ)*P i := by
  let I := Σ i : Fin 4, (P i).support
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun z : I ↦ coeff z.2.val (P z.1))
  have hz (i : Fin 4) (s : Fin 4 →₀ ℕ) : ∃ z : ℤ, (z : ℚ)=(d.val : ℚ)*coeff s (P i) := by
    by_cases hs : s ∈ (P i).support
    · obtain ⟨z,hz⟩ := hd ⟨i,⟨s,hs⟩⟩
      refine ⟨z,?_⟩
      simpa only [Algebra.smul_def] using hz
    · have he : coeff s (P i)=0 := by simpa only [mem_support_iff,not_not] using hs
      exact ⟨0,by rw [he]; simp⟩
  choose z hz using hz
  have hs (i : Fin 4) (s : Fin 4 →₀ ℕ) (h : z i s ≠ 0) : s ∈ (P i).support := by
    by_contra hh
    have he := hz i s
    have hc : coeff s (P i)=0 := by simpa only [mem_support_iff,not_not] using hh
    rw [hc,mul_zero] at he
    exact h (by exact_mod_cast he)
  let A : Fin 4 → MvPolynomial (Fin 4) ℤ := fun i ↦ Finsupp.onFinset (P i).support (z i) (hs i)
  refine ⟨d.val,nonZeroDivisors.ne_zero d.property,A,?_⟩
  intro i
  apply MvPolynomial.ext
  intro s
  rw [coeff_map,coeff_C_mul]
  change ((z i s : ℤ) : ℚ) = (d.val : ℚ)*coeff s (P i)
  exact hz i s

/-- No rational-coefficient polynomial formula, of any degree, squares the
quartic norm with multiplier four. -/
theorem no_rational_polynomial_square_four
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) :
    ¬ (∑ i, P i^4 = 4*(∑ j : Fin 4, X j^4)^2) := by
  intro h
  have hhom := QuarticAutomaticHomogeneity.transfer_is_homogeneous P 4 2 (by simpa using h)
  have hdeg (i : Fin 4) : (P i).totalDegree ≤ 2 := (hhom i).totalDegree_le
  obtain ⟨d,hd,A,hA⟩ := common_integer_denominator P
  let rho : ℤ →+* ℚ := Int.castRingHom ℚ
  have hinj : Function.Injective (map rho : MvPolynomial (Fin 4) ℤ → MvPolynomial (Fin 4) ℚ) :=
    map_injective rho Int.cast_injective
  have hAdeg (i : Fin 4) : (A i).totalDegree ≤ 2 := by
    rw [← degree_map_eq rho Int.cast_injective (A i)]
    change (map (Int.castRingHom ℚ) (A i)).totalDegree ≤ 2
    rw [hA i]
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hdeg i)
  apply no_integer_scaled_quadratic d hd A hAdeg
  apply hinj
  simp only [map_sum,map_pow,map_mul,map_ofNat,map_C,map_X]
  change (∑ i, (map (Int.castRingHom ℚ) (A i))^4)=
    4*(C (d : ℚ))^4*(∑ j : Fin 4, X j^4)^2
  simp only [hA,mul_pow,← Finset.mul_sum]
  rw [h]
  ring

/-- A multiplicity threshold cannot make such a fixed polynomial formula
possible. Its diagonal identity would already be generic. -/
theorem no_high_count_polynomial_square_four (M : ℕ)
    (P : Fin 4 → MvPolynomial (Fin 4) ℚ) :
    ¬ (∀ a : Fin 4 → ℕ,
      M < Erdos322.representationCount 4 (∑ i, a i^4) →
        ∑ i, (eval (fun j ↦ (a j : ℚ)) (P i))^4 =
          4*((∑ i, a i^4 : ℕ) : ℚ)^2) := by
  intro h
  apply no_rational_polynomial_square_four P
  have hh := LargeCountQuarticTransfer.square_identity_of_large_counts M 4 P 1 one_ne_zero
    (fun a ha _ ↦ by simpa only [map_one,div_one] using h a ha)
  simpa only [one_pow,one_mul,map_ofNat] using hh

end
end Erdos322Research.QuarticPolynomialSquareFour
