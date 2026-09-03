import Submission.CertifiedBinaryFamilySieve

/-!
Automatic homogeneous Bezout certificates from nonzero resultants in both
projective charts. This turns two finite polynomial computations into the
bounded-cancellation hypotheses of the family sieve.
-/
namespace Erdos1206.BinaryResultantCertificates
open Polynomial
open CertifiedBinaryFamilySieve

lemma homogenize_reflect {R : Type*} [CommSemiring R] {p : R[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) :
    (p.reflect d).homogenize d=MvPolynomial.rename Fin.rev (p.homogenize d) := by
  apply Polynomial.induction_with_natDegree_le
    (fun p => (p.reflect d).homogenize d=MvPolynomial.rename Fin.rev (p.homogenize d)) d
  · simp
  · intro n r _ hn
    rw [reflect_C_mul_X_pow,revAt_le hn]
    simp only [homogenize_C_mul,homogenize_X_pow hn,
      homogenize_X_pow (Nat.sub_le d n),Nat.sub_sub_self hn,map_mul,map_pow,
      MvPolynomial.rename_C,MvPolynomial.rename_X]
    simp only [show Fin.rev (0:Fin 2)=1 from rfl,show Fin.rev (1:Fin 2)=0 from rfl]
    ring
  · intro f g _ _ hf hg
    simp only [reflect_add,homogenize_add,map_add,hf,hg]
  · exact hp

lemma homogenized_bezout {R : Type*} [CommSemiring R] {p q a b : R[X]} {r : R} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (ha : a.natDegree ≤ d) (hb : b.natDegree ≤ d)
    (he : p*a+q*b=C r) :
    a.homogenize d*p.homogenize d+b.homogenize d*q.homogenize d=
      MvPolynomial.C r*MvPolynomial.X 1^(d+d) := by
  calc
    _ = (p*a).homogenize (d+d)+(q*b).homogenize (d+d) := by
      rw [homogenize_mul p a hp ha,homogenize_mul q b hq hb]
      ring
    _ = (p*a+q*b).homogenize (d+d) := (homogenize_add _ _ _).symm
    _ = _ := by rw [he,homogenize_C]

private lemma rename_reverse_twice {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.rename Fin.rev (MvPolynomial.rename Fin.rev P)=P := by
  rw [MvPolynomial.rename_rename]
  have h : (Fin.rev ∘ Fin.rev : Fin 2 → Fin 2)=id := by funext i; exact Fin.rev_rev i
  rw [h,MvPolynomial.rename_id]
  rfl

/-- Two nonzero chart resultants produce integral certificates for pure
powers of both parameters, with a common nonzero constant. -/
theorem resultant_certificates {p q : ℤ[X]} {d : ℕ} (hd : 0 < d)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (h₁ : p.resultant q d d ≠ 0)
    (h₂ : (p.reflect d).resultant (q.reflect d) d d ≠ 0) :
    ∃ R : ℤ, R ≠ 0 ∧ ∃ H K : Fin 2 → BinaryForm,
      (∑ i, H i*(![p.homogenize d,q.homogenize d] i))=
        MvPolynomial.C R*MvPolynomial.X 0^(d+d) ∧
      (∑ i, K i*(![p.homogenize d,q.homogenize d] i))=
        MvPolynomial.C R*MvPolynomial.X 1^(d+d) := by
  let r₁ := p.resultant q d d
  let r₂ := (p.reflect d).resultant (q.reflect d) d d
  obtain ⟨a,b,ha,hb,he⟩ := exists_mul_add_mul_eq_C_resultant p q hp hq (Or.inl hd.ne')
  have ha' : a.natDegree ≤ d := natDegree_le_of_degree_le ha.le
  have hb' : b.natDegree ≤ d := natDegree_le_of_degree_le hb.le
  have hP : (p.reflect d).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hp)
  have hQ : (q.reflect d).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl hq)
  obtain ⟨a',b',ha'',hb'',he'⟩ := exists_mul_add_mul_eq_C_resultant
    (p.reflect d) (q.reflect d) hP hQ (Or.inl hd.ne')
  have ha''' : a'.natDegree ≤ d := natDegree_le_of_degree_le ha''.le
  have hb''' : b'.natDegree ≤ d := natDegree_le_of_degree_le hb''.le
  have hv := homogenized_bezout hp hq ha' hb' he
  have hu := congrArg (MvPolynomial.rename Fin.rev)
    (homogenized_bezout hP hQ ha''' hb''' he')
  rw [homogenize_reflect hp,homogenize_reflect hq] at hu
  simp only [map_add,map_mul,map_pow,MvPolynomial.rename_C,MvPolynomial.rename_X,
    rename_reverse_twice] at hu
  simp only [show Fin.rev (1:Fin 2)=0 from rfl] at hu
  refine ⟨r₁*r₂,mul_ne_zero h₁ h₂,
    ![MvPolynomial.C r₁*MvPolynomial.rename Fin.rev (a'.homogenize d),
      MvPolynomial.C r₁*MvPolynomial.rename Fin.rev (b'.homogenize d)],
    ![MvPolynomial.C r₂*a.homogenize d,MvPolynomial.C r₂*b.homogenize d],?_,?_⟩
  · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,map_mul]
    dsimp only [r₁,r₂]
    linear_combination MvPolynomial.C (p.resultant q d d)*hu
  · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,map_mul]
    dsimp only [r₁,r₂]
    linear_combination MvPolynomial.C ((p.reflect d).resultant (q.reflect d) d d)*hv

#print axioms homogenize_reflect
#print axioms resultant_certificates
end Erdos1206.BinaryResultantCertificates
