import Submission.GeneralRationalFamilyBound

/-! Fixed-family bounds for arbitrary rational parameters, including negative
parameters. Reflection and primitive numerator-denominator pairs remove the
nonnegative-parameter restriction from the preceding theorem. -/
namespace Erdos322Research.SignedRationalFamilyBound

open Polynomial Finset GeneralRationalFamilyBound
set_option Elab.async false

private def parameterPair (t : ℚ) : ℕ × ℕ := (t.num.natAbs,t.den)

private lemma parameterPair_ratio (t : ℚ) :
    ((parameterPair t).1 : ℚ)/(parameterPair t).2=|t| := by
  change (t.num.natAbs : ℚ)/(t.den : ℚ)=|t|
  calc
    _ = |((t.num : ℚ)/(t.den : ℚ))| := by
      simp only [abs_div,Nat.cast_natAbs,Int.cast_abs,
        abs_of_nonneg (Nat.cast_nonneg (α := ℚ) t.den)]
    _ = |t| := by rw [Rat.num_div_den]

private lemma parameterPair_injective_nonneg :
    Set.InjOn parameterPair {t : ℚ | 0 ≤ t} := by
  intro s hs t ht he
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  have hh := congrArg (fun p : ℕ × ℕ => (p.1 : ℚ)/(p.2 : ℚ)) he
  simpa only [parameterPair_ratio,abs_of_nonneg hs,abs_of_nonneg ht] using hh

/-- The pair-based bound implies a bound directly on nonnegative rational
parameters, with no parameter-height hypothesis. -/
theorem nonnegative_rational_parameter_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ)
    (hd : 0 < f.natDegree) (hC : 0 < C)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset ℚ) (L : ℕ), 0 < L →
      (∀ t ∈ S, 0 ≤ t) →
      (∀ t ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) t /
          f.eval₂ (Int.castRingHom ℚ) t=z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  obtain ⟨K,hK,hbound⟩ := rational_family_bound f B g A C hd hC hnoroot hbez ε hε
  refine ⟨K,hK,?_⟩
  intro S L hL hpos hint
  let T := S.image parameterPair
  have hcard : T.card=S.card := Finset.card_image_of_injOn
    (fun t ht s hs he => parameterPair_injective_nonneg (hpos t ht) (hpos s hs) he)
  have hb := hbound T L hL (by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      exact t.reduced)
    (by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      exact t.den_pos)
    (by
      intro p hp i
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      rw [parameterPair_ratio,abs_of_nonneg (hpos t ht)]
      exact hint t ht i)
  simpa only [hcard] using hb

noncomputable def reflect : ℤ[X] →+* ℤ[X] := Polynomial.compRingHom (-Polynomial.X)

@[simp] lemma reflect_C (c : ℤ) : reflect (Polynomial.C c)=Polynomial.C c := Polynomial.C_comp

@[simp] lemma reflect_natDegree (f : ℤ[X]) : (reflect f).natDegree=f.natDegree := by
  change (f.comp (-Polynomial.X)).natDegree=_
  simp only [natDegree_comp,natDegree_neg,natDegree_X,mul_one]

@[simp] lemma eval_reflect {R : Type*} [CommRing R] (f : ℤ[X]) (t : R) :
    (reflect f).eval₂ (Int.castRingHom R) t=f.eval₂ (Int.castRingHom R) (-t) := by
  change (f.comp (-Polynomial.X)).eval₂ (Int.castRingHom R) t=_
  rw [Polynomial.eval₂_comp]
  simp only [eval₂_neg,eval₂_X]

/-- Uniform subpolynomial count for all affine rational parameters in a fixed
reduced family, regardless of parameter sign. -/
theorem rational_parameter_bound {ι : Type*} [Fintype ι]
    (f B : ℤ[X]) (g A : ι → ℤ[X]) (C : ℕ)
    (hd : 0 < f.natDegree) (hC : 0 < C)
    (hnoroot : ∀ t : ℝ, f.eval₂ (Int.castRingHom ℝ) t ≠ 0)
    (hbez : (∑ i, A i*g i)+B*f=Polynomial.C (C : ℤ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ (S : Finset ℚ) (L : ℕ), 0 < L →
      (∀ t ∈ S, ∀ i, ∃ z : ℤ,
        (L : ℚ)*(g i).eval₂ (Int.castRingHom ℚ) t /
          f.eval₂ (Int.castRingHom ℚ) t=z) →
      (S.card : ℝ) ≤ K*(L : ℝ)^ε := by
  classical
  have hdeg : 0 < (reflect f).natDegree := by simpa using hd
  have hroot (t : ℝ) : (reflect f).eval₂ (Int.castRingHom ℝ) t ≠ 0 := by
    simpa only [eval_reflect] using hnoroot (-t)
  have href : (∑ i, reflect (A i)*reflect (g i))+reflect B*reflect f=Polynomial.C (C : ℤ) := by
    simpa only [map_add,map_sum,map_mul,reflect_C] using congrArg reflect hbez
  obtain ⟨Kp,hKp,hp⟩ := nonnegative_rational_parameter_bound f B g A C hd hC hnoroot hbez ε hε
  obtain ⟨Kn,hKn,hn⟩ := nonnegative_rational_parameter_bound (reflect f) (reflect B)
    (fun i => reflect (g i)) (fun i => reflect (A i)) C hdeg hC hroot href ε hε
  refine ⟨Kp+Kn,add_pos hKp hKn,?_⟩
  intro S L hL hint
  let P := S.filter (fun t => 0 ≤ t)
  let M := S.filter (fun t => ¬0 ≤ t)
  let T := M.image (fun t => -t)
  have hcard : P.card+M.card=S.card := Finset.card_filter_add_card_filter_not (fun t : ℚ => 0 ≤ t)
  have hTcard : T.card=M.card := Finset.card_image_of_injective M neg_injective
  have hplus := hp P L hL (by
    intro t ht
    exact (Finset.mem_filter.mp ht).2) (by
    intro t ht i
    exact hint t (Finset.mem_filter.mp ht).1 i)
  have hminus := hn T L hL (by
      intro t ht
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      have hh := (Finset.mem_filter.mp hs).2
      linarith)
    (by
      intro t ht i
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
      simpa only [eval_reflect,neg_neg] using hint s (Finset.mem_filter.mp hs).1 i)
  rw [hTcard] at hminus
  have hcr : (P.card : ℝ)+(M.card : ℝ)=(S.card : ℝ) := by exact_mod_cast hcard
  nlinarith

end Erdos322Research.SignedRationalFamilyBound
