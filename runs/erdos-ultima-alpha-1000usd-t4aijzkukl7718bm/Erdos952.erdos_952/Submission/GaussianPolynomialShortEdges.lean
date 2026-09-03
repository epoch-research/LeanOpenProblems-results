import Submission.GaussianPolynomialImageObstruction

/-! A coefficient-independent bound on the number of close pairs in a
nonlinear Gaussian polynomial image. The degree bound and the jump bound
remain explicit. -/
namespace Erdos952Investigation.GaussianPolynomialShortEdges
open GaussianPolynomialImageObstruction Polynomial
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

def ball (B : ℤ) : Finset GaussianInt := (norm_sublevel_finite B).toFinset

lemma mem_ball (B : ℤ) (z : GaussianInt) : z ∈ ball B ↔ z.norm ≤ B :=
  (norm_sublevel_finite B).mem_toFinset

def differencePolynomial (P : Polynomial GaussianInt) (h d : GaussianInt) :
    Polynomial GaussianInt := P.comp (X+C h)-P-C d

lemma degree_differencePolynomial_le (P : Polynomial GaussianInt) (h d : GaussianInt) :
    (differencePolynomial P h d).natDegree ≤ P.natDegree := by
  dsimp only [differencePolynomial]
  rw [natDegree_sub_C]
  have hlin : (X+C h : Polynomial GaussianInt).natDegree = 1 := natDegree_X_add_C h
  have h1 := Polynomial.natDegree_sub_le (P.comp (X+C h)) P
  rw [natDegree_comp,hlin,mul_one,max_self] at h1
  exact h1

/-- A certificate containing the input pairs for every nonzero short output
edge. It may contain irrelevant pairs; these only enlarge the bound. -/
def pairCertificate (P : Polynomial GaussianInt) (B : ℤ) :
    Finset (GaussianInt × GaussianInt) :=
  ((ball B) ×ˢ (ball B)).biUnion (fun hd =>
    (differencePolynomial P hd.1 hd.2).roots.toFinset.image (fun z => (z,z+hd.1)))

lemma pairCertificate_card_le (P : Polynomial GaussianInt) (B : ℤ) :
    (pairCertificate P B).card ≤ (ball B).card^2*P.natDegree := by
  calc
    _ ≤ ∑ hd ∈ (ball B) ×ˢ (ball B),
        ((differencePolynomial P hd.1 hd.2).roots.toFinset.image
          (fun z => (z,z+hd.1))).card := Finset.card_biUnion_le
    _ ≤ ∑ _hd ∈ (ball B) ×ˢ (ball B), P.natDegree := by
      apply Finset.sum_le_sum
      intro hd _
      exact Finset.card_image_le.trans
        ((Multiset.toFinset_card_le _).trans
          ((Polynomial.card_roots' _).trans (degree_differencePolynomial_le P hd.1 hd.2)))
    _ = _ := by simp [Finset.card_product,pow_two]

lemma mem_pairCertificate (P : Polynomial GaussianInt) (hP : 2 ≤ P.natDegree)
    (B : ℤ) (u v : GaussianInt) (hne : P.eval u ≠ P.eval v)
    (hb : (P.eval v-P.eval u).norm ≤ B) : (u,v) ∈ pairCertificate P B := by
  let h := v-u
  let d := P.eval v-P.eval u
  have hd : d ≠ 0 := sub_ne_zero.mpr hne.symm
  have hh : h ≠ 0 := by
    intro he
    exact hne (congrArg P.eval (sub_eq_zero.mp he).symm)
  have hnorm : h.norm ≤ B := by
    have hdiv : h ∣ d := Polynomial.sub_dvd_eval_sub v u P
    exact (Int.le_of_dvd (GaussianInt.norm_pos.mpr hd)
      (Zsqrtd.normMonoidHom.map_dvd hdiv)).trans hb
  apply Finset.mem_biUnion.mpr
  refine ⟨(h,d),Finset.mem_product.mpr ⟨(mem_ball B h).mpr hnorm,(mem_ball B d).mpr hb⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨u,?_,?_⟩
  · rw [Multiset.mem_toFinset]
    change u ∈ (P.comp (X+C h)-P-C d).roots
    rw [Polynomial.mem_roots (difference_polynomial_ne_zero P hP h d hh)]
    simp only [Polynomial.IsRoot,eval_sub,eval_comp,eval_add,eval_X,eval_C]
    have he : u+h = v := by dsimp [h]; abel
    rw [he]
    exact sub_self _
  · apply Prod.ext
    · rfl
    · dsimp [h]
      abel

def vertexCertificate (P : Polynomial GaussianInt) (B : ℤ) : Finset GaussianInt :=
  (pairCertificate P B).image (fun uv => P.eval uv.1)

lemma vertexCertificate_card_le (P : Polynomial GaussianInt) (B : ℤ) :
    (vertexCertificate P B).card ≤ (ball B).card^2*P.natDegree :=
  Finset.card_image_le.trans (pairCertificate_card_le P B)

lemma mem_vertexCertificate (P : Polynomial GaussianInt) (hP : 2 ≤ P.natDegree)
    (B : ℤ) (z w : GaussianInt) (hz : z ∈ Set.range P.eval) (hw : w ∈ Set.range P.eval)
    (hne : z ≠ w) (hb : (w-z).norm ≤ B) : z ∈ vertexCertificate P B := by
  obtain ⟨u,rfl⟩ := hz
  obtain ⟨v,rfl⟩ := hw
  exact Finset.mem_image.mpr ⟨(u,v),mem_pairCertificate P hP B u v hne hb,rfl⟩

/-- A finite family has a common finite exceptional set of close-pair
vertices, whose cardinality depends only on degree and jump bounds. -/
def familyCertificate {J : Type*} [Fintype J] (P : J → Polynomial GaussianInt)
    (B : ℤ) : Finset GaussianInt := Finset.univ.biUnion (fun j => vertexCertificate (P j) B)

lemma familyCertificate_card_le {J : Type*} [Fintype J]
    (P : J → Polynomial GaussianInt) (d : ℕ) (hP : ∀ j, (P j).natDegree ≤ d) (B : ℤ) :
    (familyCertificate P B).card ≤ Fintype.card J*((ball B).card^2*d) := by
  calc
    _ ≤ ∑ j : J, (vertexCertificate (P j) B).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : J, (ball B).card^2*d := by
      apply Finset.sum_le_sum
      intro j _
      exact (vertexCertificate_card_le (P j) B).trans (Nat.mul_le_mul_left _ (hP j))
    _ = _ := by simp

lemma mem_familyCertificate {J : Type*} [Fintype J]
    (P : J → Polynomial GaussianInt) (hP : ∀ j, 2 ≤ (P j).natDegree)
    (B : ℤ) (j : J) (z w : GaussianInt) (hz : z ∈ Set.range (P j).eval)
    (hw : w ∈ Set.range (P j).eval) (hne : z ≠ w) (hb : (w-z).norm ≤ B) :
    z ∈ familyCertificate P B := by
  exact Finset.mem_biUnion.mpr
    ⟨j,Finset.mem_univ j,mem_vertexCertificate (P j) (hP j) B z w hz hw hne hb⟩

#print axioms pairCertificate_card_le
#print axioms mem_pairCertificate
#print axioms familyCertificate_card_le
#print axioms mem_familyCertificate
end
end Erdos952Investigation.GaussianPolynomialShortEdges
