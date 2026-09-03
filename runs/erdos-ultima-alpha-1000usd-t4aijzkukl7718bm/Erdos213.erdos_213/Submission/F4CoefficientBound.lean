import Submission.RootCoefficientBound

/-! F4 specialization of the uniform coefficient-ratio bound.
This file does not assert existence of an integral configuration. -/
namespace Erdos213.F4CoefficientBound
open Polynomial RootCoefficientBound
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

private def coeff : Fin 24 → Fin 4 → ℤ :=
  !![1,0,0,0;
     0,1,0,0;
     0,0,1,0;
     0,0,0,1;
     1,1,0,0;
     1,-1,0,0;
     1,0,1,0;
     1,0,-1,0;
     1,0,0,1;
     1,0,0,-1;
     0,1,1,0;
     0,1,-1,0;
     0,1,0,1;
     0,1,0,-1;
     0,0,1,1;
     0,0,1,-1;
     1,-1,-1,-1;
     1,-1,-1,1;
     1,-1,1,-1;
     1,-1,1,1;
     1,1,-1,-1;
     1,1,-1,1;
     1,1,1,-1;
     1,1,1,1]

private def pivot : Fin 24 → Fin 4 :=
  ![0,1,2,3,0,0,0,0,0,0,1,1,1,1,2,2,0,0,0,0,0,0,0,0]

private def eta (h f : Fin 24) (i : Fin 4) : ℤ :=
  coeff f i-coeff f (pivot h)*coeff h i

private lemma pivot_one : ∀ h, coeff h (pivot h)=1 := by decide
private lemma eta_small : ∀ h f i, -2 ≤ eta h f i ∧ eta h f i ≤ 2 := by decide
private lemma eta_nonzero : ∀ h f, h ≠ f → ∃ i, eta h f i ≠ 0 := by decide

private def beta (h f : Fin 24) : B := ofFn 4 (fun i => (eta h f i : ℚ))

private lemma beta_self (h : Fin 24) : beta h h=0 := by
  have hh : (fun i => (eta h h i : ℚ))=0 := by
    funext i
    simp [eta,pivot_one]
  rw [beta,hh]
  simp

private lemma beta_ne_zero {h f : Fin 24} (hne : h ≠ f) : beta h f ≠ 0 := by
  obtain ⟨i,hi⟩ := eta_nonzero h f hne
  intro he
  have hh := congrArg (fun p : B => p.coeff i.val) he
  have hz : (eta h f i : ℚ)=0 := by
    simpa only [beta,ofFn_coeff_eq_val_of_lt _ i.isLt,Fin.eta,coeff_zero] using hh
  exact hi (by exact_mod_cast hz)

private lemma small_integer_power {z : ℤ} (hb : -2 ≤ z ∧ z ≤ 2) (hz : z ≠ 0) :
    SignedPowerTwo 1 (z : ℚ) := by
  obtain ⟨hl,hr⟩ := hb
  interval_cases z
  · exact ⟨1,le_rfl,Or.inr (by norm_num)⟩
  · exact ⟨0,by omega,Or.inr (by norm_num)⟩
  · exact (hz rfl).elim
  · exact ⟨0,by omega,Or.inl (by norm_num)⟩
  · exact ⟨1,le_rfl,Or.inl (by norm_num)⟩

private lemma beta_leading {h f : Fin 24} (hne : h ≠ f) :
    SignedPowerTwo 1 (beta h f).leadingCoeff := by
  have hd : (beta h f).natDegree < 4 := ofFn_natDegree_lt (by norm_num) _
  let i : Fin 4 := ⟨(beta h f).natDegree,hd⟩
  have hl : (beta h f).leadingCoeff=(eta h f i : ℚ) := by
    exact ofFn_coeff_eq_val_of_lt _ hd
  rw [hl]
  apply small_integer_power (eta_small h f i)
  intro hz
  have hlead : (beta h f).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (beta_ne_zero hne)
  apply hlead
  rw [hl,hz]
  norm_num

/-- The image of a root after using root h as the outer variable. -/
def slice (h f : Fin 24) : T :=
  C (beta h f)+C (C (coeff f (pivot h) : ℚ))*X

lemma slice_self (h : Fin 24) : slice h h=X := by
  simp [slice,beta_self,pivot_one]

lemma slice_signed (h f : Fin 24) :
    SignedPowerTwo 1 (slice h f).trailingCoeff.leadingCoeff := by
  by_cases he : h=f
  · subst f
    rw [slice_self]
    refine ⟨0,by omega,Or.inl ?_⟩
    simp [trailingCoeff]
  · have h0 : (slice h f).coeff 0 ≠ 0 := by
      simpa [slice] using beta_ne_zero he
    rw [trailingCoeff_eq_coeff_zero h0]
    simpa [slice] using beta_leading he

lemma slice_order (h f : Fin 24) :
    (slice h f).natTrailingDegree=if f=h then 1 else 0 := by
  by_cases he : f=h
  · subst f
    simp [slice_self]
  · rw [if_neg he]
    apply natTrailingDegree_eq_zero.mpr
    right
    simpa [slice] using beta_ne_zero (Ne.symm he)

private def poly (f : Fin 24) : B := ofFn 4 (fun i => (coeff f i : ℚ))

private lemma beta_eq (h f : Fin 24) :
    beta h f=poly f-C (coeff f (pivot h) : ℚ)*poly h := by
  ext n
  by_cases hn : n < 4
  · simp only [beta,poly,ofFn_coeff_eq_val_of_lt _ hn,coeff_sub,coeff_C_mul]
    simp only [eta,Int.cast_sub,Int.cast_mul]
  · have hn' : 4 ≤ n := by omega
    simp only [beta,poly,ofFn_coeff_eq_zero_of_ge _ hn',coeff_sub,coeff_C_mul,
      mul_zero,sub_self]

private def vars (h : Fin 24) (i : Fin 4) : T :=
  if i=pivot h then X-C (poly h)+C (X^i.val) else C (X^i.val)

/-- The 24 primitive projective F4 root forms. -/
def root (f : Fin 24) : MvPolynomial (Fin 4) ℚ :=
  ∑ i : Fin 4, MvPolynomial.C (coeff f i : ℚ)*MvPolynomial.X i

private def specialization (h : Fin 24) : MvPolynomial (Fin 4) ℚ →+* T :=
  MvPolynomial.eval₂Hom (C.comp C) (vars h)

private lemma specialization_C (h : Fin 24) (a : ℚ) :
    specialization h (MvPolynomial.C a)=C (C a) := by
  simp [specialization]

private lemma specialization_root (h f : Fin 24) :
    specialization h (root f)=slice h f := by
  have hsum : (∑ i : Fin 4, C (C (coeff f i : ℚ))*C (X^i.val) : T)=C (poly f) := by
    rw [poly,ofFn_eq_sum_monomial,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← C_mul_X_pow_eq_monomial,map_mul]
  calc
    specialization h (root f)=∑ i : Fin 4, C (C (coeff f i : ℚ))*vars h i := by
      simp only [root,map_sum,map_mul,specialization_C]
      simp [specialization]
    _ = ∑ i : Fin 4, (C (C (coeff f i : ℚ))*C (X^i.val) +
        if i=pivot h then C (C (coeff f (pivot h) : ℚ))*(X-C (poly h)) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=pivot h
      · subst i
        simp only [vars,if_true]
        ring
      · simp only [vars,hi,if_false,add_zero]
    _ = C (poly f)+C (C (coeff f (pivot h) : ℚ))*(X-C (poly h)) := by
      rw [Finset.sum_add_distrib,hsum]
      simp
    _ = slice h f := by
      rw [slice,beta_eq]
      simp only [map_sub,map_mul]
      ring

/-- Products may have arbitrary degree and repeated factors. -/
def rootProduct (s : Multiset (Fin 24)) : MvPolynomial (Fin 4) ℚ :=
  (s.map root).prod

private lemma specialization_product (h : Fin 24) (s : Multiset (Fin 24)) :
    specialization h (rootProduct s)=product (slice h) s := by
  rw [rootProduct,map_multiset_prod]
  simp only [Multiset.map_map,Function.comp_def,specialization_root,product]

/-- Uniform all-degree F4 coefficient-ratio bound for polynomial identities.
There is no numerical root search or unproved gcd/classification premise. -/
theorem coefficient_ratio {s t u : Multiset (Fin 24)} {d : ℕ}
    (hs : s.card=d) (ht : t.card=d) (hu : u.card=d) (hsu : s ≠ u)
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : MvPolynomial.C a*rootProduct s-MvPolynomial.C b*rootProduct t=
      MvPolynomial.C c*rootProduct u) : RatioBound d a b := by
  apply ratio_bound_of_specializations slice slice_signed slice_order hs ht hu hsu ha hb
  intro h
  have hh := congrArg (specialization h) he
  simpa only [map_sub,map_mul,specialization_C,specialization_product] using hh

/-- Distinct products cannot differ only by a nonzero rational scalar. -/
lemma rootProduct_direction_injective {s t : Multiset (Fin 24)} {a b : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (he : MvPolynomial.C a*rootProduct s=MvPolynomial.C b*rootProduct t) : s=t := by
  apply multiset_eq_of_specializations slice slice_signed slice_order ha hb
  intro h
  have hh := congrArg (specialization h) he
  simpa only [map_mul,specialization_C,specialization_product] using hh

/-- The ratio bound needs only distinct input product directions. -/
theorem coefficient_ratio_of_distinct {s t u : Multiset (Fin 24)} {d : ℕ}
    (hs : s.card=d) (ht : t.card=d) (hu : u.card=d) (hst : s ≠ t)
    {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (he : MvPolynomial.C a*rootProduct s-MvPolynomial.C b*rootProduct t=
      MvPolynomial.C c*rootProduct u) : RatioBound d a b := by
  apply ratio_bound_of_distinct_specializations slice slice_signed slice_order hs ht hu hst ha hb
  intro h
  have hh := congrArg (specialization h) he
  simpa only [map_sub,map_mul,specialization_C,specialization_product] using hh

/-- Arbitrary rational constant coefficients in a finite homogeneous F4
product-difference family normalize to the window used by the catalogs.
This does not assert that every rational-distance set belongs to such a family. -/
theorem family_coefficient_window {ι : Type*} (S : Finset ι) (hne : S.Nonempty)
    (a : ι → ℚ) (p : ι → Multiset (Fin 24)) {d : ℕ}
    (ha : ∀ i∈S, a i ≠ 0) (hp : Set.InjOn p (S : Set ι))
    (hd : ∀ i∈S, (p i).card=d)
    (he : ∀ i∈S, ∀ j∈S, i ≠ j → ∃ u : Multiset (Fin 24), ∃ c : ℚ,
      u.card=d ∧ MvPolynomial.C (a i)*rootProduct (p i)-
        MvPolynomial.C (a j)*rootProduct (p j)=MvPolynomial.C c*rootProduct u) :
    ∃ k∈S, a k ≠ 0 ∧ ∀ i∈S, SignedPowerTwo d (a i/a k) := by
  apply finite_family_normalization S hne a ha
  intro i hi j hj hij
  obtain ⟨u,c,hu,heq⟩ := he i hi j hj hij
  exact coefficient_ratio_of_distinct (hd i hi) (hd j hj) hu
    (fun h => hij (hp hi hj h)) (ha i hi) (ha j hj) heq

/-- The denominator-cleared coefficient window used by the quartic anchor search. -/
lemma quartic_coefficient_window {s t u : Multiset (Fin 24)}
    (hs : s.card=4) (ht : t.card=4) (hu : u.card=4) (hsu : s ≠ u)
    {b c : ℚ} (hb : b ≠ 0)
    (he : rootProduct s-MvPolynomial.C b*rootProduct t=
      MvPolynomial.C c*rootProduct u) :
    ∃ k : ℕ, k ≤ 8 ∧ (16*b=2^k ∨ 16*b=-(2^k)) := by
  have he' : MvPolynomial.C (1 : ℚ)*rootProduct s-
      MvPolynomial.C b*rootProduct t=MvPolynomial.C c*rootProduct u := by
    simpa using he
  have hh := normalized_dyadic_window
    (coefficient_ratio hs ht hu hsu (by norm_num) hb he')
  norm_num [SignedPowerTwo] at hh
  exact hh

#print axioms rootProduct_direction_injective
#print axioms coefficient_ratio_of_distinct
#print axioms family_coefficient_window
#print axioms quartic_coefficient_window
#print axioms slice_signed
#print axioms slice_order
#print axioms coefficient_ratio
end
end Erdos213.F4CoefficientBound
