import Submission.PointCountableEdgeCover

/-!
Finite-dimensional orthogonality for polynomial or rational-function vectors
in arbitrarily many variables over a countable integral domain admits a
countable triangle-free edge cover, including arbitrary coefficient matrices. Private-variable specialization and the verified
finite-support intersection theorem supply the cover. This is an auxiliary
result, not a representation of arbitrary K4-free graphs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open SimpleGraph Set MvPolynomial
open scoped BigOperators
namespace Erdos595PolynomialOrthogonality
open Erdos595Work

variable {R J I : Type*} [CommRing R] [Fintype J]

def form (B : J → J → R) {A : Type*} [CommRing A]
    (ι : R →+* A) (x y : J → A) : A :=
  ∑ i, ∑ j, ι (B i j) * x i * y j

lemma map_form (B : J → J → R) {A D : Type*} [CommRing A] [CommRing D]
    (ι : R →+* A) (φ : A →+* D) (x y : J → A) :
    φ (form B ι x y) = form B (φ.comp ι) (φ ∘ x) (φ ∘ y) := by
  simp only [form,map_sum,map_mul,RingHom.comp_apply,Function.comp_apply]

lemma form_scale (B : J → J → R) {A : Type*} [CommRing A]
    (ι : R →+* A) (a b : A) (x y : J → A) :
    form B ι (fun i => a * x i) (fun j => b * y j) = a * b * form B ι x y := by
  simp only [form,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

abbrev Point (B : J → J → R) (I : Type*) :=
  {x : J → MvPolynomial I R // form B C x x ≠ 0}

/-- Symmetrization permits arbitrary coefficient matrices. -/
def graph (B : J → J → R) (I : Type*) : SimpleGraph (Point B I) where
  Adj x y := form B C x.val y.val = 0 ∧ form B C y.val x.val = 0
  symm := fun _ _ h => h.symm
  loopless := fun x h => x.property h.1

private lemma countable_graph {V : Type*} [Countable V] (G : SimpleGraph V) :
    IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat V
  let f (v : V) (n : ℕ) : Fin 2 := if e v = n then 1 else 0
  apply countable_union_of_binary_encoding G f
  intro a b h
  apply he
  have hh := congrFun h (e a)
  by_contra hab
  simp [f,Ne.symm hab] at hh

private instance [Countable R] [Countable I] : Countable (MvPolynomial I R) :=
  inferInstanceAs (Countable ((I →₀ ℕ) →₀ R))

private theorem countable_target [Countable R] [Countable I] (B : J → J → R) :
    IsCountableUnionOfTriangleFree (graph B I) := countable_graph _

section Specialization
variable [IsDomain R] [Infinite R] (B : J → J → R)

private lemma exists_evaluation (x : Point B I) :
    ∃ a : I → R, eval a (form B C x.val x.val) ≠ 0 := by
  by_contra h
  push_neg at h
  apply x.property
  exact MvPolynomial.funext (fun a => by simpa using h a)

noncomputable def sample (x : Point B I) : I → R := (exists_evaluation B x).choose

lemma sample_nonzero (x : Point B I) :
    eval (sample B x) (form B C x.val x.val) ≠ 0 :=
  (exists_evaluation B x).choose_spec

noncomputable def assignment (F : Finset I) (x : Point B I) (i : I) : MvPolynomial F R := by
  classical
  exact if h : i ∈ F then X ⟨i,h⟩ else C (sample B x i)

noncomputable def specialize (F : Finset I) (x : Point B I) :
    MvPolynomial I R →+* MvPolynomial F R := eval₂Hom C (assignment B F x)

lemma evaluate_specialize (F : Finset I) (x : Point B I) (p : MvPolynomial I R) :
    eval (fun i : F => sample B x i.val) (specialize B F x p) = eval (sample B x) p := by
  have he : (eval (fun i : F => sample B x i.val)).comp (specialize B F x) =
      eval (sample B x) := by
    classical
    ext i <;> simp [specialize,assignment]
    split_ifs <;> simp
  exact RingHom.congr_fun he p

noncomputable def project (F : Finset I) (x : Point B I) : Point B F := by
  refine ⟨specialize B F x ∘ x.val,?_⟩
  intro hz
  have hm := map_form B C (specialize B F x) x.val x.val
  have hc : (specialize B F x).comp C = C := by ext r; simp [specialize]
  rw [hc,hz] at hm
  apply sample_nonzero B x
  rw [← evaluate_specialize B F x,hm,map_zero]

noncomputable def support (x : Point B I) : Finset I := by
  classical
  exact Finset.univ.biUnion (fun j => (x.val j).vars)

omit [IsDomain R] [Infinite R] in
lemma mem_support (x : Point B I) (j : J) {i : I} (hi : i ∈ (x.val j).vars) :
    i ∈ support B x := by
  classical
  exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hi⟩

/-- On the exact common support, the two independent specializations are
restrictions of ONE polynomial substitution. -/
lemma common_substitution [DecidableEq I] (x y : Point B I) :
    ∃ φ : MvPolynomial I R →+* MvPolynomial ↥(support B x ∩ support B y) R,
      φ.comp C = C ∧
      (∀ j, φ (x.val j) = (project B (support B x ∩ support B y) x).val j) ∧
      (∀ j, φ (y.val j) = (project B (support B x ∩ support B y) y).val j) := by
  classical
  let F := support B x ∩ support B y
  let a (i : I) : MvPolynomial F R :=
    if h : i ∈ F then X ⟨i,h⟩ else
      if i ∈ support B x then C (sample B x i) else C (sample B y i)
  let φ : MvPolynomial I R →+* MvPolynomial F R := eval₂Hom C a
  refine ⟨φ,eval₂Hom_comp_C C a,?_,?_⟩
  · intro j
    change eval₂Hom C a (x.val j) =
      eval₂Hom C (assignment B F x) (x.val j)
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    have hs := mem_support B x j hi
    by_cases hf : i ∈ F
    · simp [a,assignment,hf]
    · simp [a,assignment,hf,hs]
  · intro j
    change eval₂Hom C a (y.val j) =
      eval₂Hom C (assignment B F y) (y.val j)
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    have hs := mem_support B y j hi
    by_cases hf : i ∈ F
    · simp [a,assignment,hf]
    · have hn : i ∉ support B x := fun hx => hf (Finset.mem_inter.mpr ⟨hx,hs⟩)
      simp [a,assignment,hf,hn]

lemma projected_adj [DecidableEq I] {x y : Point B I} (h : (graph B I).Adj x y) :
    (graph B ↥(support B x ∩ support B y)).Adj
      (project B (support B x ∩ support B y) x)
      (project B (support B x ∩ support B y) y) := by
  obtain ⟨φ,hC,hx,hy⟩ := common_substitution B x y
  have hx' : φ ∘ x.val = (project B (support B x ∩ support B y) x).val := funext hx
  have hy' : φ ∘ y.val = (project B (support B x ∩ support B y) y).val := funext hy
  constructor
  · have hm := map_form B C φ x.val y.val
    rw [h.1,map_zero,hC,hx',hy'] at hm
    exact hm.symm
  · have hm := map_form B C φ y.val x.val
    rw [h.2,map_zero,hC,hx',hy'] at hm
    exact hm.symm

/-- The number of variables and the cardinality of the vertex set are unrestricted.
No K4-freeness hypothesis is needed for this covering theorem. -/
theorem countable_cover [Countable R] :
    IsCountableUnionOfTriangleFree (graph B I) := by
  classical
  exact Erdos595PointCountableEdgeCover.finite_intersection_reduction
    (graph B I) (support B) (fun F => Point B F) (fun F => graph B F) (project B)
    (fun _ => countable_target B) (fun _ _ h => projected_adj B h)

/-- A polynomial representation need preserve only edges, not nonedges. -/
theorem cover_of_representation [Countable R] {V : Type*} (G : SimpleGraph V)
    (r : V → J → MvPolynomial I R)
    (hr : ∀ v, form B C (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → form B C (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  let f : G →g graph B I :=
    ⟨fun v => ⟨r v,hr v⟩,fun h => ⟨he _ _ h,he _ _ h.symm⟩⟩
  exact countable_union_of_hom f (countable_cover B)
end Specialization

section FiniteCoefficientDomains
variable [IsDomain R] [Countable R]

private instance : Countable (Polynomial R) := by
  letI : Countable (AddMonoidAlgebra R ℕ) := inferInstanceAs (Countable (ℕ →₀ R))
  exact Polynomial.toFinsupp_injective.countable

/-- Adjoining one coefficient variable removes the infinitude hypothesis
on the coefficient domain; finite fields are included. -/
theorem cover_of_representation_domain (B : J → J → R) {V : Type*}
    (G : SimpleGraph V) (r : V → J → MvPolynomial I R)
    (hr : ∀ v, form B C (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → form B C (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  let f : R →+* Polynomial R := Polynomial.C
  let φ : MvPolynomial I R →+* MvPolynomial I (Polynomial R) := MvPolynomial.map f
  let B' : J → J → Polynomial R := fun i j => f (B i j)
  have hm (a b : V) : φ (form B C (r a) (r b)) =
      form B' C (φ ∘ r a) (φ ∘ r b) := by
    simp only [form,map_sum,map_mul,φ,MvPolynomial.map_C,B',Function.comp_apply]
  apply cover_of_representation B' G (fun v => φ ∘ r v)
  · intro v hz
    apply hr v
    apply MvPolynomial.map_injective f Polynomial.C_injective
    exact (hm v v).trans (hz.trans (map_zero φ).symm)
  · intro a b hab
    rw [← hm,he a b hab,map_zero]

/-- Countable coefficient domains of any characteristic suffice. -/
theorem countable_cover_domain (B : J → J → R) :
    IsCountableUnionOfTriangleFree (graph B I) :=
  cover_of_representation_domain B (graph B I) Subtype.val (fun v => v.property)
    (fun _ _ h => h.1)
end FiniteCoefficientDomains

section PolynomialCoefficients
variable [IsDomain R] [Countable R]

/-- The finitely many coefficient polynomials can be moved into a countable
coefficient domain. Thus the matrix itself may depend on arbitrary variables. -/
theorem cover_of_polynomial_matrix (B : J → J → MvPolynomial I R) {V : Type*}
    (G : SimpleGraph V) (r : V → J → MvPolynomial I R)
    (hr : ∀ v, form B (RingHom.id _) (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → form B (RingHom.id _) (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let T : Finset I := Finset.univ.biUnion (fun i : J =>
    Finset.univ.biUnion (fun j : J => (B i j).vars))
  let L := MvPolynomial T R
  let N := {i : I // i ∉ T}
  let g (i : I) : MvPolynomial N L := if h : i ∈ T then C (X ⟨i,h⟩) else X ⟨i,h⟩
  let φ : MvPolynomial I R →+* MvPolynomial N L := eval₂Hom (C.comp C) g
  let ρ : L →+* MvPolynomial I R := (rename (Subtype.val : T → I)).toRingHom
  let ψ : MvPolynomial N L →+* MvPolynomial I R := eval₂Hom ρ (fun i : N => X i.val)
  have hψφ : ψ.comp φ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change ψ (φ (C c)) = C c
      simp only [φ,eval₂Hom_C,RingHom.comp_apply,ψ]
      exact rename_C (Subtype.val : T → I) c
    · intro i
      change ψ (φ (X i)) = X i
      simp only [φ,eval₂Hom_X',ψ]
      by_cases hi : i ∈ T
      · simp only [g,dif_pos hi,eval₂Hom_C]
        exact rename_X (Subtype.val : T → I) ⟨i,hi⟩
      · simp only [g,dif_neg hi,eval₂Hom_X']
  have hinj : Function.Injective φ := by
    intro x y h
    have hh := congrArg ψ h
    simpa only [← RingHom.comp_apply,hψφ,RingHom.id_apply] using hh
  let a (i : I) : L := if h : i ∈ T then X ⟨i,h⟩ else 0
  let χ : MvPolynomial I R →+* L := eval₂Hom C a
  have hcoeff (i j : J) : φ (B i j) = C (χ (B i j)) := by
    have hT {k : I} (hk : k ∈ (B i j).vars) : k ∈ T :=
      Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
        Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hk⟩⟩
    change φ (B i j) = (C.comp χ) (B i j)
    apply hom_congr_vars _ _ rfl
    · simp only [φ,χ,eval₂Hom_comp_C,RingHom.comp_assoc]
    · intro k hk _
      simp [φ,χ,g,a,hT hk]
  let B' : J → J → L := fun i j => χ (B i j)
  have hm (v w : V) : φ (form B (RingHom.id _) (r v) (r w)) =
      form B' C (φ ∘ r v) (φ ∘ r w) := by
    simp only [form,map_sum,map_mul,RingHom.id_apply,Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcoeff]
  apply cover_of_representation_domain B' G (fun v => φ ∘ r v)
  · intro v hz
    apply hr v
    apply hinj
    exact (hm v v).trans (hz.trans (map_zero φ).symm)
  · intro v w hvw
    rw [← hm,he v w hvw,map_zero]
end PolynomialCoefficients

section Fractions
variable [IsDomain R] [Countable R]
variable {F : Type*} [Field F] [Algebra (MvPolynomial I R) F]
    [IsFractionRing (MvPolynomial I R) F]

omit [Countable R] in
private lemma clear_denominators (x : J → F) :
    ∃ d : MvPolynomial I R, d ≠ 0 ∧ ∃ p : J → MvPolynomial I R,
      ∀ j, algebraMap (MvPolynomial I R) F (p j) =
        algebraMap (MvPolynomial I R) F d * x j := by
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (MvPolynomial I R)) x
  choose p hp using hd
  refine ⟨d.val,mem_nonZeroDivisors_iff_ne_zero.mp d.property,p,?_⟩
  intro j
  simpa only [Algebra.smul_def] using hp j

/-- Clearing one common denominator per vector extends the theorem to the
fraction field of a polynomial ring. Its set of variables is unrestricted. -/
theorem cover_of_fraction_representation (B : J → J → R) {V : Type*}
    (G : SimpleGraph V) (r : V → J → F)
    (hr : ∀ v, form B ((algebraMap (MvPolynomial I R) F).comp C) (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b →
      form B ((algebraMap (MvPolynomial I R) F).comp C) (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  choose d hd p hp using fun v => clear_denominators (R := R) (I := I) (r v)
  let φ := algebraMap (MvPolynomial I R) F
  have hm (a b : V) : φ (form B C (p a) (p b)) =
      φ (d a) * φ (d b) * form B (φ.comp C) (r a) (r b) := by
    rw [map_form]
    have ha : φ ∘ p a = fun j => φ (d a) * r a j := funext (hp a)
    have hb : φ ∘ p b = fun j => φ (d b) * r b j := funext (hp b)
    rw [ha,hb,form_scale]
  have hd' (v : V) : φ (d v) ≠ 0 := by
    intro h
    exact hd v (IsFractionRing.injective (MvPolynomial I R) F
      (h.trans (map_zero φ).symm))
  apply cover_of_representation_domain B G p
  · intro v hz
    have h := hm v v
    rw [hz,map_zero] at h
    exact mul_ne_zero (mul_ne_zero (hd' v) (hd' v)) (hr v) h.symm
  · intro a b hab
    apply IsFractionRing.injective (MvPolynomial I R) F
    rw [map_zero,hm,he a b hab,mul_zero]

include R I in
/-- Arbitrary matrices over the fraction field are allowed, not only matrices
whose coefficients lie in the original countable domain. -/
theorem cover_of_fraction_matrix (B : J → J → F) {V : Type*}
    (G : SimpleGraph V) (r : V → J → F)
    (hr : ∀ v, form B (RingHom.id _) (r v) (r v) ≠ 0)
    (he : ∀ a b, G.Adj a b → form B (RingHom.id _) (r a) (r b) = 0) :
    IsCountableUnionOfTriangleFree G := by
  obtain ⟨D,hD,b₀,hb⟩ := clear_denominators (R := R) (I := I)
    (fun ij : J × J => B ij.1 ij.2)
  let b : J → J → MvPolynomial I R := fun i j => b₀ (i,j)
  choose d hd p hp using fun v => clear_denominators (R := R) (I := I) (r v)
  let φ := algebraMap (MvPolynomial I R) F
  have hn {q : MvPolynomial I R} (hq : q ≠ 0) : φ q ≠ 0 := by
    intro h
    exact hq (IsFractionRing.injective (MvPolynomial I R) F
      (h.trans (map_zero φ).symm))
  have hm (v w : V) : φ (form b (RingHom.id _) (p v) (p w)) =
      φ D * φ (d v) * φ (d w) * form B (RingHom.id _) (r v) (r w) := by
    simp only [form,map_sum,map_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change φ (b₀ (i,j)) * φ (p v i) * φ (p w j) = _
    rw [hb (i,j),hp v i,hp w j]
    ring
  apply cover_of_polynomial_matrix b G p
  · intro v hz
    have h := hm v v
    rw [hz,map_zero] at h
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hn hD) (hn (hd v)))
      (hn (hd v))) (hr v) h.symm
  · intro v w hvw
    apply IsFractionRing.injective (MvPolynomial I R) F
    rw [map_zero,hm,he v w hvw,mul_zero]

end Fractions

#print axioms common_substitution
#print axioms countable_cover
#print axioms cover_of_representation
#print axioms cover_of_fraction_representation
#print axioms countable_cover_domain
#print axioms cover_of_polynomial_matrix
#print axioms cover_of_fraction_matrix
end Erdos595PolynomialOrthogonality
