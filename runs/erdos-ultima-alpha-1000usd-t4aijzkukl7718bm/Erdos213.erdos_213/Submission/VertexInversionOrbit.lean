import FormalConjecturesUtil

/-! Finite normal forms for projective recharting of a fixed configuration.
This does not bound the cardinality of arbitrary integral-distance sets. -/
namespace Erdos213.VertexInversionOrbit
noncomputable section
open Matrix OnePoint
open scoped Pointwise
local notation "G" => Matrix.GeneralLinearGroup (Fin 2) ℂ
set_option maxHeartbeats 2000000

/-- Send p to infinity. The finite formula is 1/(z-p), i.e. an inversion
followed by a reflection, which does not change distances. -/
def normalizer : OnePoint ℂ → G
  | ∞ => 1
  | (p : ℂ) =>
    ⟨!![0,1;1,-p], !![p,1;1,0], by simp [one_fin_two], by simp [one_fin_two]⟩

lemma normalizer_at (p : OnePoint ℂ) : normalizer p • p = ∞ := by
  cases p with
  | infty => simp [normalizer]
  | coe p => simp [normalizer,OnePoint.smul_some_eq_ite]

lemma normalizer_infty (p : ℂ) : normalizer (p : OnePoint ℂ) • (∞ : OnePoint ℂ) = (0 : ℂ) := by
  simp [normalizer,OnePoint.smul_infty_eq_ite]

lemma normalizer_finite (p z : ℂ) (hz : z≠p) :
    normalizer (p : OnePoint ℂ) • (z : OnePoint ℂ) = ((z-p)⁻¹ : ℂ) := by
  have hz' : z + -p ≠ 0 := by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hz
  simp [normalizer,OnePoint.smul_some_eq_ite,hz',sub_eq_add_neg]

/-- An element fixing infinity acts on the finite plane by a nonsingular
complex affine map, hence by a Euclidean similarity. -/
lemma affine_of_fixes_infty (g : G) (hg : g • (∞ : OnePoint ℂ)=∞) :
    ∃ a b : ℂ, a≠0 ∧ ∀ z : ℂ, g • (z : OnePoint ℂ)=(a*z+b : ℂ) := by
  have hc : g 1 0=0 := OnePoint.smul_infty_eq_self_iff.mp hg
  have hdet : g 0 0*g 1 1≠0 := by
    have hh := g.det_ne_zero
    simpa [Matrix.det_fin_two,hc] using hh
  have ha : g 0 0≠0 := (mul_ne_zero_iff.mp hdet).1
  have hd : g 1 1≠0 := (mul_ne_zero_iff.mp hdet).2
  refine ⟨g 0 0/g 1 1,g 0 1/g 1 1,div_ne_zero ha hd,?_⟩
  intro z
  rw [OnePoint.smul_some_eq_ite]
  simp only [hc,zero_mul,zero_add,if_neg hd]
  congr 1
  ring

lemma affine_dist (a b z w : ℂ) : dist (a*z+b) (a*w+b)=‖a‖*dist z w := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : a*z+b-(a*w+b)=a*(z-w) := by ring
  rw [he,norm_mul]

/-- The finite part of a projective point set. -/
def finitePart (T : Set (OnePoint ℂ)) : Set ℂ := {z | (z : OnePoint ℂ)∈T}

lemma finitePart_smul (g : G) (T : Set (OnePoint ℂ))
    (hg : g • (∞ : OnePoint ℂ)=∞)
    {a b : ℂ} (hf : ∀ z : ℂ, g • (z : OnePoint ℂ)=(a*z+b : ℂ)) :
    finitePart (g • T)=(fun z : ℂ => a*z+b) '' finitePart T := by
  ext z
  constructor
  · intro hz
    obtain ⟨p,hp,hpz⟩ := hz
    cases p with
    | infty =>
      change g • (∞ : OnePoint ℂ) = (z : OnePoint ℂ) at hpz
      rw [hg] at hpz
      exact False.elim (OnePoint.infty_ne_coe z hpz)
    | coe p =>
      exact ⟨p,hp,OnePoint.coe_injective ((hf p).symm.trans hpz)⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(p : OnePoint ℂ),hp,hf p⟩

lemma recharts_affine (g : G) (p : OnePoint ℂ) (hp : g • p=∞) :
    ∃ a b : ℂ, a≠0 ∧ ∀ T : Set (OnePoint ℂ),
      finitePart (g • T)=(fun z : ℂ => a*z+b) '' finitePart (normalizer p • T) := by
  let h : G := g*(normalizer p)⁻¹
  have hh : h • (∞ : OnePoint ℂ)=∞ := by
    calc
      h • (∞ : OnePoint ℂ) = h • (normalizer p • p) := by rw [normalizer_at]
      _ = g • p := by simp [h, smul_smul]
      _ = ∞ := hp
  obtain ⟨a,b,ha,hf⟩ := affine_of_fixes_infty h hh
  refine ⟨a,b,ha,?_⟩
  intro T
  have he : h • (normalizer p • T)=g • T := by simp [h,smul_smul]
  rw [← he]
  exact finitePart_smul h _ hh hf

/-- At most card(S) affine-similarity representatives suffice for EVERY
Möbius image of a finite projective set S that contains infinity. This concerns
one fixed S; it is not a uniform cardinality bound on possible source sets. -/
theorem finite_normal_forms (S : Finset (OnePoint ℂ)) :
    ∃ F : Finset (Set ℂ), F.card≤S.card ∧
      ∀ g : G, (∞ : OnePoint ℂ)∈g • (S : Set (OnePoint ℂ)) →
        ∃ T∈F, ∃ a b : ℂ, a≠0 ∧
          finitePart (g • (S : Set (OnePoint ℂ)))=(fun z : ℂ => a*z+b) '' T := by
  classical
  let F := S.image (fun p => finitePart (normalizer p • (S : Set (OnePoint ℂ))))
  refine ⟨F,Finset.card_image_le,?_⟩
  intro g hg
  obtain ⟨p,hp,hpg⟩ := hg
  obtain ⟨a,b,ha,hform⟩ := recharts_affine g p hpg
  exact ⟨finitePart (normalizer p • (S : Set (OnePoint ℂ))),
    Finset.mem_image.mpr ⟨p,hp,rfl⟩,a,b,ha,hform _⟩

/-- Adjoining infinity to an n-point affine configuration gives at most n+1
representatives under the rechartings covered by `finite_normal_forms`. -/
theorem affine_configuration_normal_forms (A : Finset ℂ) :
    ∃ F : Finset (Set ℂ), F.card ≤ A.card + 1 ∧
      ∀ g : G,
        (∞ : OnePoint ℂ) ∈ g •
          (insert ∞ (OnePoint.some '' (A : Set ℂ))) →
        ∃ T ∈ F, ∃ a b : ℂ, a ≠ 0 ∧
          finitePart (g • (insert ∞ (OnePoint.some '' (A : Set ℂ)))) =
            (fun z : ℂ => a*z+b) '' T := by
  classical
  let S : Finset (OnePoint ℂ) := insert ∞ (A.image OnePoint.some)
  have hS : (S : Set (OnePoint ℂ)) = insert ∞ (OnePoint.some '' (A : Set ℂ)) := by
    simp [S]
  have hc : S.card ≤ A.card + 1 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  obtain ⟨F, hF, hf⟩ := finite_normal_forms S
  refine ⟨F, hF.trans hc, ?_⟩
  simpa only [hS] using hf

/-- Conjugation extended by fixing infinity. -/
def conjugate : OnePoint ℂ → OnePoint ℂ := OnePoint.map (starRingEnd ℂ)

@[simp] lemma conjugate_infty : conjugate ∞ = ∞ := rfl
@[simp] lemma conjugate_coe (z : ℂ) : conjugate (z : OnePoint ℂ) =
    ((starRingEnd ℂ) z : ℂ) := rfl
@[simp] lemma conjugate_conjugate (z : OnePoint ℂ) :
    conjugate (conjugate z) = z := by
  cases z <;> simp [conjugate]

lemma conjugate_smul (g : G) (z : OnePoint ℂ) :
    conjugate (g • z) = (g.map (starRingEnd ℂ)) • conjugate z :=
  OnePoint.map_smul _ _ _

lemma smul_conjugate (g : G) (z : OnePoint ℂ) :
    g • conjugate z = conjugate ((g.map (starRingEnd ℂ)) • z) := by
  have h := congrArg conjugate (conjugate_smul g (conjugate z))
  simpa only [conjugate_conjugate] using h

/-- Words generated by Möbius transformations and conjugation. -/
inductive RechartWord : (OnePoint ℂ → OnePoint ℂ) → Prop
  | id : RechartWord id
  | mobius (g : G) {f} : RechartWord f → RechartWord (fun z => g • f z)
  | reflect {f} : RechartWord f → RechartWord (fun z => conjugate (f z))

lemma word_normal_form {f : OnePoint ℂ → OnePoint ℂ} (hf : RechartWord f) :
    ∃ g : G, ∃ e : Bool, ∀ z,
      f z = if e then conjugate (g • z) else g • z := by
  induction hf with
  | id => exact ⟨1, false, by simp⟩
  | mobius k hf ih =>
    obtain ⟨g,e,hg⟩ := ih
    cases e with
    | false => exact ⟨k*g, false, by simpa only [Bool.false_eq_true, ↓reduceIte,
        smul_smul] using fun z => congrArg (fun w => k • w) (hg z)⟩
    | true =>
      refine ⟨(k.map (starRingEnd ℂ))*g, true, ?_⟩
      intro z
      simp only [hg, ↓reduceIte, smul_smul, smul_conjugate]
  | reflect hf ih =>
    obtain ⟨g,e,hg⟩ := ih
    cases e with
    | false =>
      refine ⟨g, true, ?_⟩
      intro z
      simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg conjugate (hg z)
    | true =>
      refine ⟨g, false, ?_⟩
      intro z
      simpa only [Bool.false_eq_true, ↓reduceIte, conjugate_conjugate]
        using congrArg conjugate (hg z)

lemma finitePart_conjugate (T : Set (OnePoint ℂ)) :
    finitePart (conjugate '' T) = (starRingEnd ℂ) '' finitePart T := by
  ext z
  constructor
  · rintro ⟨p,hp,hpz⟩
    cases p with
    | infty => exact False.elim (OnePoint.infty_ne_coe z hpz)
    | coe p => exact ⟨p,hp,OnePoint.coe_injective hpz⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(p : OnePoint ℂ),hp,rfl⟩

lemma infty_mem_conjugate_iff (T : Set (OnePoint ℂ)) :
    ∞ ∈ conjugate '' T ↔ ∞ ∈ T := by
  constructor
  · rintro ⟨p,hp,hp'⟩
    have he : p = ∞ := by
      simpa only [conjugate_conjugate, conjugate_infty] using congrArg conjugate hp'
    exact he ▸ hp
  · intro h
    exact ⟨∞,h,rfl⟩

/-- An affine similarity, with a possible final reflection. -/
def similarity (e : Bool) (a b z : ℂ) : ℂ :=
  if e then (starRingEnd ℂ) (a*z+b) else a*z+b

lemma similarity_dist (e : Bool) (a b z w : ℂ) :
    dist (similarity e a b z) (similarity e a b w) = ‖a‖ * dist z w := by
  cases e <;> simp only [similarity, Bool.false_eq_true, ↓reduceIte,
    Complex.dist_conj_conj, affine_dist]

/-- Including orientation-reversing words does not require extra normal forms
when similarity is allowed to reverse orientation. -/
theorem word_finite_normal_forms (S : Finset (OnePoint ℂ)) :
    ∃ F : Finset (Set ℂ), F.card ≤ S.card ∧
      ∀ f : OnePoint ℂ → OnePoint ℂ, RechartWord f →
        ∞ ∈ f '' (S : Set (OnePoint ℂ)) →
        ∃ T ∈ F, ∃ e : Bool, ∃ a b : ℂ, a ≠ 0 ∧
          finitePart (f '' (S : Set (OnePoint ℂ))) = similarity e a b '' T := by
  obtain ⟨F,hF,hforms⟩ := finite_normal_forms S
  refine ⟨F,hF,?_⟩
  intro f hf hinf
  obtain ⟨g,e,hg⟩ := word_normal_form hf
  cases e with
  | false =>
    have he : f '' (S : Set (OnePoint ℂ)) = g • (S : Set (OnePoint ℂ)) := by
      have he' : f = fun z => g • z := by funext z; simpa using hg z
      rw [he', Set.image_smul]
    rw [he] at hinf ⊢
    obtain ⟨T,hT,a,b,ha,hab⟩ := hforms g hinf
    exact ⟨T,hT,false,a,b,ha,hab⟩
  | true =>
    have he : f '' (S : Set (OnePoint ℂ)) =
        conjugate '' (g • (S : Set (OnePoint ℂ))) := by
      have he' : f = fun z => conjugate (g • z) := by funext z; simpa using hg z
      rw [he', ← Set.image_image, Set.image_smul]
    rw [he] at hinf ⊢
    obtain ⟨T,hT,a,b,ha,hab⟩ := hforms g ((infty_mem_conjugate_iff _).mp hinf)
    refine ⟨T,hT,true,a,b,ha,?_⟩
    rw [finitePart_conjugate, hab, Set.image_image]
    rfl

/-- The n+1 representative bound also covers orientation-reversing words,
including compositions of the projective sphere inversions defined below. -/
theorem word_affine_configuration_normal_forms (A : Finset ℂ) :
    ∃ F : Finset (Set ℂ), F.card ≤ A.card + 1 ∧
      ∀ f : OnePoint ℂ → OnePoint ℂ, RechartWord f →
        ∞ ∈ f '' (insert ∞ (OnePoint.some '' (A : Set ℂ))) →
        ∃ T ∈ F, ∃ e : Bool, ∃ a b : ℂ, a ≠ 0 ∧
          finitePart (f '' (insert ∞ (OnePoint.some '' (A : Set ℂ)))) =
            similarity e a b '' T := by
  classical
  let S : Finset (OnePoint ℂ) := insert ∞ (A.image OnePoint.some)
  have hS : (S : Set (OnePoint ℂ)) = insert ∞ (OnePoint.some '' (A : Set ℂ)) := by
    simp [S]
  have hc : S.card ≤ A.card + 1 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  obtain ⟨F, hF, hf⟩ := word_finite_normal_forms S
  refine ⟨F, hF.trans hc, ?_⟩
  simpa only [hS] using hf

/-- Matrix for an invertible complex affine map. -/
def affineMatrix (a b : ℂ) (ha : a ≠ 0) : G :=
  ⟨!![a,b;0,1], !![a⁻¹,-a⁻¹*b;0,1],
    by simp [one_fin_two, ha],
    by simp [one_fin_two, ha]⟩

@[simp] lemma affineMatrix_infty (a b : ℂ) (ha : a ≠ 0) :
    affineMatrix a b ha • (∞ : OnePoint ℂ) = ∞ := by
  simp [affineMatrix, OnePoint.smul_infty_eq_ite]

@[simp] lemma affineMatrix_finite (a b z : ℂ) (ha : a ≠ 0) :
    affineMatrix a b ha • (z : OnePoint ℂ) = (a*z+b : ℂ) := by
  simp [affineMatrix, OnePoint.smul_some_eq_ite]

/-- Projective extension of an ordinary inversion with nonzero radius.
Unlike Mathlib's totalized affine inversion, it interchanges the center and
infinity. Its finite values agree with that inversion away from the center. -/
def sphereInversion (p : ℂ) (R : ℝ) (hR : R ≠ 0) : OnePoint ℂ → OnePoint ℂ :=
  fun z => affineMatrix ((R : ℂ)^2) p (pow_ne_zero 2 (by exact_mod_cast hR)) •
    conjugate (normalizer (p : OnePoint ℂ) • z)

lemma sphereInversion_word (p : ℂ) (R : ℝ) (hR : R ≠ 0) :
    RechartWord (sphereInversion p R hR) :=
  RechartWord.mobius _ (RechartWord.reflect (RechartWord.mobius _ RechartWord.id))

@[simp] lemma sphereInversion_center (p : ℂ) (R : ℝ) (hR : R ≠ 0) :
    sphereInversion p R hR p = ∞ := by
  simp [sphereInversion, normalizer_at]

@[simp] lemma sphereInversion_infty (p : ℂ) (R : ℝ) (hR : R ≠ 0) :
    sphereInversion p R hR ∞ = (p : OnePoint ℂ) := by
  simp [sphereInversion, normalizer_infty]

lemma sphereInversion_finite (p z : ℂ) (R : ℝ) (hR : R ≠ 0) (hz : z ≠ p) :
    sphereInversion p R hR (z : OnePoint ℂ) =
      ((EuclideanGeometry.inversion p R z : ℂ) : OnePoint ℂ) := by
  rw [sphereInversion, normalizer_finite p z hz, conjugate_coe, affineMatrix_finite]
  congr 1
  rw [EuclideanGeometry.inversion, Complex.conj_inv, Complex.inv_def,
    Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  simp only [vsub_eq_sub, vadd_eq_add, dist_eq_norm, Complex.real_smul,
    div_pow, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv]
  ring

lemma RechartWord.comp {f g : OnePoint ℂ → OnePoint ℂ}
    (hf : RechartWord f) (hg : RechartWord g) : RechartWord (f ∘ g) := by
  induction hf with
  | id => exact hg
  | mobius k hf ih => exact RechartWord.mobius k ih
  | reflect hf ih => exact RechartWord.reflect ih

/-- Each further Euclidean inversion remains a word in the class covered by
the finite normal-form theorem. This holds whether or not its center is a
selected vertex. The theorem's infinity-membership premise is still required. -/
lemma RechartWord.invert {f : OnePoint ℂ → OnePoint ℂ} (hf : RechartWord f)
    (p : ℂ) (R : ℝ) (hR : R ≠ 0) :
    RechartWord (sphereInversion p R hR ∘ f) :=
  (sphereInversion_word p R hR).comp hf

#print axioms affine_of_fixes_infty
#print axioms affine_dist
#print axioms finite_normal_forms
#print axioms affine_configuration_normal_forms
#print axioms word_normal_form
#print axioms similarity_dist
#print axioms word_finite_normal_forms
#print axioms word_affine_configuration_normal_forms
#print axioms sphereInversion_finite
#print axioms RechartWord.invert
end
end Erdos213.VertexInversionOrbit
