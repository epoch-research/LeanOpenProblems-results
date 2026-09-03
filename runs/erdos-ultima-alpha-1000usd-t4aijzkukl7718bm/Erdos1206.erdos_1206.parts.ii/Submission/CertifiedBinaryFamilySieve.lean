import Submission.NormalizedBinaryFamilySieve

/-!
Polynomial certificates for a familywise reciprocal-summable divisor cover.
The common-divisor bound and the absence of real basepoints are consequences
of the two displayed homogeneous Bezout identities.
-/
namespace Erdos1206.CertifiedBinaryFamilySieve
open MvPolynomial BinaryHomogeneousHeight NormalizedBinaryFamilySieve
open scoped BigOperators Classical

abbrev BinaryForm := MvPolynomial (Fin 2) ℤ

lemma homogeneous_eval_scale {R S : Type*} [CommSemiring R] [CommSemiring S]
    {P : MvPolynomial (Fin 2) R} {d : ℕ} (hP : P.IsHomogeneous d)
    (f : R →+* S) (s u v : S) :
    eval₂ f ![s*u,s*v] P=s^d*eval₂ f ![u,v] P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [eval₂_sum,eval₂_monomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg : e 0+e 1=d := by
    have hh := hP (mem_support_iff.mp he)
    simpa [Finsupp.weight_apply,Finsupp.sum_fintype,Fin.sum_univ_two] using hh
  simp only [Finsupp.prod_pow,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,mul_pow]
  calc
    _ = f (P.coeff e)*(s^(e 0+e 1)*(u^(e 0)*v^(e 1))) := by rw [pow_add]; ring
    _ = _ := by rw [hdeg]; ring

noncomputable def realFamily {m : ℕ} (P : Fin m → BinaryForm) (x : ℝ × ℝ) : Fin m → ℝ :=
  fun i => eval₂ (Int.castRingHom ℝ) ![x.1,x.2] (P i)

lemma realFamily_continuous {m : ℕ} (P : Fin m → BinaryForm) : Continuous (realFamily P) := by
  apply continuous_pi
  intro i
  dsimp only [realFamily]
  simp_rw [← MvPolynomial.eval_map]
  apply (MvPolynomial.continuous_eval ((MvPolynomial.map (Int.castRingHom ℝ)) (P i))).comp
  apply continuous_pi
  intro j
  fin_cases j
  · exact continuous_fst
  · exact continuous_snd

lemma realFamily_homogeneous {m d : ℕ} {P : Fin m → BinaryForm}
    (hP : ∀ i, (P i).IsHomogeneous d) (s : ℝ) (x : ℝ × ℝ) :
    realFamily P (s • x)=s^d • realFamily P x := by
  funext i
  exact homogeneous_eval_scale (hP i) (Int.castRingHom ℝ) s x.1 x.2

/-- The same symbolic certificates exclude all nonzero real common zeros. -/
lemma realFamily_zero {m n : ℕ} {P H K : Fin m → BinaryForm} {R : ℤ}
    (hR : R ≠ 0)
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n)
    (x : ℝ × ℝ) (hx : realFamily P x=0) : x=0 := by
  have hPx (i : Fin m) : eval₂ (Int.castRingHom ℝ) ![x.1,x.2] (P i)=0 :=
    congrFun hx i
  have hR' : (R:ℝ) ≠ 0 := by exact_mod_cast hR
  have h₀ := congrArg (eval₂Hom (Int.castRingHom ℝ) ![x.1,x.2]) hH
  have h₁ := congrArg (eval₂Hom (Int.castRingHom ℝ) ![x.1,x.2]) hK
  simp only [map_sum,map_mul,map_pow,coe_eval₂Hom,eval₂_C,eval₂_X,hPx,mul_zero,
    Finset.sum_const_zero,Matrix.cons_val_zero,Matrix.cons_val_one] at h₀ h₁
  have hx₀ : x.1=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h₀.symm).resolve_left hR')
  have hx₁ : x.2=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h₁.symm).resolve_left hR')
  exact Prod.ext hx₀ hx₁

/-- The integral versions of the certificates uniformly bound cancellation
at every primitive pair, irrespective of its size or signs. -/
lemma normalized_divisor_dvd {m n : ℕ} {P H K : Fin m → BinaryForm} {R u v g : ℤ}
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n)
    (hcop : IsCoprime u v) {N : Fin m → ℤ}
    (hN : ∀ i, eval ![u,v] (P i)=g*N i) : g ∣ R := by
  apply common_divisor_dvd_certificate (F := fun i => eval ![u,v] (P i))
    (H := fun i => eval ![u,v] (H i)) (K := fun i => eval ![u,v] (K i)) hcop
  · intro i
    rw [hN]
    exact dvd_mul_right _ _
  · have hh := congrArg (eval ![u,v]) hH
    simpa using hh
  · have hh := congrArg (eval ![u,v]) hK
    simpa using hh

lemma realFamily_int_values {m : ℕ} {P : Fin m → BinaryForm} {u v g : ℤ} {N : Fin m → ℤ}
    (hN : ∀ i, eval ![u,v] (P i)=g*N i) (i : Fin m) :
    realFamily P ((u:ℝ),(v:ℝ)) i=((g*N i:ℤ):ℝ) := by
  have hh := congrArg (Int.castRingHom ℝ) (hN i)
  rw [MvPolynomial.map_eval,MvPolynomial.eval_map] at hh
  have hv : (fun j : Fin 2 => ((![u,v] j:ℤ):ℝ))= ![(u:ℝ),(v:ℝ)] := by
    funext j
    fin_cases j <;> rfl
  change eval₂ (Int.castRingHom ℝ) (fun j : Fin 2 => ((![u,v] j:ℤ):ℝ)) (P i)=
    ((g*N i:ℤ):ℝ) at hh
  rw [hv] at hh
  exact hh

/-- Certified polynomial form of the normalized reciprocal-summability
criterion. All constants may depend on this fixed family. -/
theorem certified_maxima_summable {m d n : ℕ} (hd : 3 ≤ d)
    {P H K : Fin m → BinaryForm} {R : ℤ} (hR : R ≠ 0)
    (hP : ∀ i, (P i).IsHomogeneous d)
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n)
    {T : Set (ℤ × ℤ)} (hprim : ∀ p : T, IsCoprime p.val.1 p.val.2)
    (N : T → Fin m → ℤ) (g : T → ℤ)
    (hN : ∀ p i, eval ![p.val.1,p.val.2] (P i)=g p*N p i) :
    Summable (fun k : ℕ => if k ∈ Set.range (fun p => rootHeight (N p)) then (1:ℝ)/k else 0) := by
  exact normalized_maxima_summable hd (realFamily P) (realFamily_continuous P)
    (realFamily_homogeneous hP) (realFamily_zero hR hH hK) hprim N g hR
    (fun p => normalized_divisor_dvd hH hK (hprim p) (hN p))
    (fun p i => realFamily_int_values (hN p) i)

/-- Every dilation of every normalized tuple in this certified family is
avoided by a positive-density source. This is not a cover of all collisions. -/
theorem positive_density_avoids_certified_family {m d n : ℕ} (hm : 0 < m) (hd : 3 ≤ d)
    {P H K : Fin m → BinaryForm} {R : ℤ} (hR : R ≠ 0)
    (hP : ∀ i, (P i).IsHomogeneous d)
    (hH : ∑ i, H i*P i=C R*X 0^n) (hK : ∑ i, K i*P i=C R*X 1^n)
    {T : Set (ℤ × ℤ)} (hprim : ∀ p : T, IsCoprime p.val.1 p.val.2)
    (N : T → Fin m → ℤ) (g : T → ℤ)
    (hN : ∀ p i, eval ![p.val.1,p.val.2] (P i)=g p*N p i)
    (hmax : ∀ p, 1 < rootHeight (N p)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      ∀ (p : T) (t : ℕ), ∃ i : Fin m, t*(N p i).natAbs ∉ A := by
  exact positive_density_avoids_normalized_family hm hd (realFamily P) (realFamily_continuous P)
    (realFamily_homogeneous hP) (realFamily_zero hR hH hK) hprim N g hR
    (fun p => normalized_divisor_dvd hH hK (hprim p) (hN p))
    (fun p i => realFamily_int_values (hN p) i) hmax

#print axioms homogeneous_eval_scale
#print axioms certified_maxima_summable
#print axioms positive_density_avoids_certified_family
end Erdos1206.CertifiedBinaryFamilySieve
