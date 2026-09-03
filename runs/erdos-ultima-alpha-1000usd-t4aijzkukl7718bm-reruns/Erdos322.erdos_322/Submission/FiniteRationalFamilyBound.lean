import Submission.SignedRationalFamilyBound

/-! Finiteness and subpolynomial cardinality of the full rational parameter
set of a fixed family. The even-power endpoint also includes the parameter
at infinity. No claim is made about a varying collection of families. -/
namespace Erdos322Research.FiniteRationalFamilyBound

open Polynomial Finset SignedRationalFamilyBound
set_option Elab.async false

/-- All affine rational parameters whose scaled coordinate values are integral. -/
def integralParameters {ι : Type*} (f : ℤ[X]) (g : ι → ℤ[X]) (L : ℕ) : Set ℚ :=
  {t | ∀ i, ∃ z : ℤ,
    (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) t /
      f.eval₂ (Int.castRingHom ℚ) t=z}

lemma finite_of_uniform_finset_card_bound {α : Type*} (S : Set α) (B : ℝ)
    (h : ∀ T : Finset α, (T : Set α) ⊆ S → (T.card : ℝ) ≤ B) : S.Finite := by
  classical
  by_contra hnot
  obtain ⟨N,hN⟩ := exists_nat_gt B
  obtain ⟨T,hT,hcard⟩ := (show S.Infinite from hnot).exists_subset_card_eq N
  have hb := h T hT
  rw [hcard] at hb
  linarith

/-- The full set is finite, not merely bounded when restricted to a finite
subset. The same constant works for every positive integral scale. -/
theorem rational_parameter_set_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ)
    (hd : 0 < f.natDegree) (hC : 0 < C)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ L : ℕ, 0 < L →
      (integralParameters f g L).Finite ∧
      ((integralParameters f g L).ncard : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  obtain ⟨K,hK,hbound⟩ := rational_parameter_bound f B g A C hd hC hnoroot hbez ε hε
  refine ⟨K,hK,?_⟩
  intro L hL
  have hfinite : (integralParameters f g L).Finite :=
    finite_of_uniform_finset_card_bound _ (K*(L : ℝ)^ε) (by
      intro S hS
      exact hbound S L hL (fun t ht => hS ht))
  refine ⟨hfinite,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  apply hbound hfinite.toFinset L hL
  intro t ht
  exact hfinite.mem_toFinset.mp ht

/-- Values at affine parameters and at infinity. For even-power norm
families, the automatic degree bound makes the latter the ordinary limit. -/
noncomputable def projectiveValue {ι : Type*} (f : ℤ[X]) (g : ι → ℤ[X])
    (t : Option ℚ) (i : ι) : ℚ :=
  match t with
  | some x => (g i).eval₂ (Int.castRingHom ℚ) x / f.eval₂ (Int.castRingHom ℚ) x
  | none => ((g i).coeff f.natDegree : ℚ)/(f.leadingCoeff : ℚ)

def projectiveIntegralParameters {ι : Type*} (f : ℤ[X]) (g : ι → ℤ[X])
    (L : ℕ) : Set (Option ℚ) :=
  {t | ∀ i, ∃ z : ℤ, (L : ℚ)*projectiveValue f g t i=z}

lemma eval_rat_ne_zero (f : ℤ[X])
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0) (t : ℚ) :
    f.eval₂ (Int.castRingHom ℚ) t ≠ 0 := by
  have he : ((f.eval₂ (Int.castRingHom ℚ) t : ℚ) : ℝ)=
      f.eval₂ (Int.castRingHom ℝ) (t : ℝ) := by
    simp only [Polynomial.eval₂_eq_sum_range,Int.coe_castRingHom]
    push_cast
    rfl
  intro hz
  rw [hz,Rat.cast_zero] at he
  exact hnoroot (t : ℝ) he.symm

private lemma quotient_norm {ι : Type*} [Fintype ι]
    (v : ι → ℚ) (d n : ℚ) (e : ℕ) (hd : d ≠ 0)
    (h : ∑ i, v i^e=n*d^e) : ∑ i, (v i/d)^e=n := by
  simp only [div_pow, ← Finset.sum_div]
  rw [h,mul_div_cancel_right₀ _ (pow_ne_zero _ hd)]

/-- The value assigned at infinity satisfies the same norm identity as the
finite values; it is not an extraneous point added to the counting bound. -/
theorem projectiveValue_even_norm {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hd : 0 < f.natDegree) (hC : 0 < C)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^(2*m)=Polynomial.C N*f^(2*m))
    (t : Option ℚ) : ∑ i, projectiveValue f g t i^(2*m)=(N : ℚ) := by
  have hf : f ≠ 0 := by intro hz; simp [hz] at hd
  have hnoroot := EvenPolynomialNormDegree.denominator_no_real_zero
    f B g A C N m hm hC hnorm hbez
  cases t with
  | some x =>
    have hx := congrArg (Polynomial.eval₂ (Int.castRingHom ℚ) x) hnorm
    simp only [eval₂_finset_sum,eval₂_pow,eval₂_mul,eval₂_C,Int.coe_castRingHom] at hx
    exact quotient_norm (fun i => (g i).eval₂ (Int.castRingHom ℚ) x)
      (f.eval₂ (Int.castRingHom ℚ) x) (N : ℚ) (2*m) (eval_rat_ne_zero f hnoroot x) hx
  | none =>
    have hdeg := EvenPolynomialNormDegree.numerator_degree_le f g N m hm hnorm
    have hc := congrArg (fun p : ℤ[X] => p.coeff ((2*m)*f.natDegree)) hnorm
    simp only [finset_sum_coeff,coeff_C_mul] at hc
    have hg (i : ι) : (g i^(2*m)).coeff ((2*m)*f.natDegree)=
        (g i).coeff f.natDegree^(2*m) := coeff_pow_of_natDegree_le (hdeg i)
    simp only [hg,coeff_pow_of_natDegree_le (le_refl f.natDegree),coeff_natDegree] at hc
    have hq : (∑ i, ((g i).coeff f.natDegree : ℚ)^(2*m))=
        (N : ℚ)*(f.leadingCoeff : ℚ)^(2*m) := by exact_mod_cast hc
    have hlc : (f.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf
    exact quotient_norm (fun i => ((g i).coeff f.natDegree : ℚ))
      (f.leadingCoeff : ℚ) (N : ℚ) (2*m) hlc hq

/-- A fixed reduced rational family with nonconstant denominator and no real
pole has subpolynomially many integral projective parameters at each scale. -/
theorem projective_parameter_set_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ)
    (hd : 0 < f.natDegree) (hC : 0 < C)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ L : ℕ, 0 < L →
      (projectiveIntegralParameters f g L).Finite ∧
      ((projectiveIntegralParameters f g L).ncard : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  obtain ⟨K,hK,hbound⟩ := rational_parameter_set_bound f B g A C hd hC hnoroot hbez ε hε
  refine ⟨K+1,by positivity,?_⟩
  intro L hL
  obtain ⟨hfinite,hcard⟩ := hbound L hL
  let S := projectiveIntegralParameters f g L
  let T : Set (Option ℚ) := insert none (Option.some '' integralParameters f g L)
  have hT : T.Finite := (hfinite.image Option.some).insert none
  have hsub : S ⊆ T := by
    intro t ht
    cases t with
    | none => exact Set.mem_insert _ _
    | some x =>
      apply Set.mem_insert_of_mem
      refine ⟨x,?_,rfl⟩
      intro i
      simpa only [projectiveValue,mul_div_assoc] using ht i
  have hS : S.Finite := hT.subset hsub
  have hc : S.ncard ≤ (integralParameters f g L).ncard+1 := by
    calc
      S.ncard ≤ T.ncard := Set.ncard_le_ncard hsub hT
      _ ≤ (Option.some '' integralParameters f g L).ncard+1 := Set.ncard_insert_le _ _
      _ = (integralParameters f g L).ncard+1 := by
        rw [Set.ncard_image_of_injective _ (Option.some_injective ℚ)]
  refine ⟨hS,?_⟩
  have hcR : (S.ncard : ℝ) ≤ ((integralParameters f g L).ncard : ℝ)+1 := by exact_mod_cast hc
  have hp : 1 ≤ (L : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast hL) hε.le
  change (S.ncard : ℝ) ≤ _
  nlinarith


/-- Every positive even-power norm family with the given reducedness
certificate has a finite, subpolynomial set of all rational projective
parameters making its scaled coordinates integral. -/
theorem even_projective_parameter_set_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ) (N : ℤ)
    (m : ℕ) (hm : 0 < m) (hd : 0 < f.natDegree) (hC : 0 < C)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (hnorm : ∑ i, g i^(2*m)=Polynomial.C N*f^(2*m))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ L : ℕ, 0 < L →
      (projectiveIntegralParameters f g L).Finite ∧
      ((projectiveIntegralParameters f g L).ncard : ℝ) ≤ K*(L : ℝ)^ε := by
  exact projective_parameter_set_bound f B g A C hd hC
    (EvenPolynomialNormDegree.denominator_no_real_zero
      f B g A C N m hm hC hnorm hbez) hbez ε hε

end Erdos322Research.FiniteRationalFamilyBound
