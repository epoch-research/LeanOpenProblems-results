import Submission.CubicNormSextic

/-! Exact four-row normalization and its six-point bound. -/
noncomputable section
open Classical Finset
set_option maxHeartbeats 2000000
namespace Erdos714CubicFour
open Erdos714CubicSegre (norm norm_mul norm_div norm_ne_zero)
open Erdos714CubicSextic
variable {E J : Type*} [Field E]

/-- The affine parameter of the third center, after sending the first two to 0 and 1. -/
def affineParameter (x : Fin 3 → E) : E := (x 2-x 0)/(x 1-x 0)

lemma affineParameter_ne (x : Fin 3 → E) (hx : Function.Injective x) :
    affineParameter x ≠ 0 ∧ affineParameter x ≠ 1 := by
  have h10 : x 1-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  refine ⟨div_ne_zero (sub_ne_zero.mpr (hx.ne (by decide))) h10, ?_⟩
  intro he
  have he' := (div_eq_one_iff_eq h10).mp he
  exact hx.ne (by decide : (2 : Fin 3) ≠ 1) (sub_left_injective he')

/-- An invertible affine change normalizes any three distinct norm centers. -/
lemma normalize_spheres (σ : E →+* E) (x : Fin 3 → E) (hx : Function.Injective x)
    (w : J → E) (hw : Function.Injective w) (a : Fin 3 → E)
    (ha : ∀ i, a i ≠ 0) (h : ∀ i j, norm σ (x i+w j) = a i) :
    ∃ b : Fin 3 → E, (∀ i, b i ≠ 0) ∧ ∃ z : J → E, Function.Injective z ∧
      ∀ j, norm σ (z j) = b 0 ∧ norm σ (z j+1) = b 1 ∧
        norm σ (z j+affineParameter x) = b 2 := by
  let A := x 1-x 0
  have hA : A ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  let b (i : Fin 3) := a i / norm σ A
  let z (j : J) := (x 0+w j)/A
  refine ⟨b, (fun i => div_ne_zero (ha i) (norm_ne_zero σ hA)), z, ?_, ?_⟩
  · intro i j hij
    exact hw (add_left_cancel ((div_left_inj' hA).mp hij))
  · have he (i : Fin 3) (j : J) :
        norm σ (z j+(x i-x 0)/A) = b i := by
      have hv : z j+(x i-x 0)/A = (x i+w j)/A := by dsimp [z]; ring
      rw [hv,Erdos714CubicSegre.norm_div,h]
    intro j
    refine ⟨?_, ?_, he 2 j⟩
    · simpa using he 0 j
    · simpa [A,div_self hA] using he 1 j

/-- Three distinct spheres have at most six common points. -/
theorem three_spheres_card_le_six [Fintype J]
    (σ : E →+* E) (x : Fin 3 → E) (hx : Function.Injective x)
    (w : J → E) (hw : Function.Injective w) (a : Fin 3 → E)
    (ha : ∀ i, a i ≠ 0) (h : ∀ i j, norm σ (x i+w j) = a i) :
    Fintype.card J ≤ 6 := by
  obtain ⟨b,hb,z,hz,hn⟩ := normalize_spheres σ x hx w hw a ha h
  obtain ⟨hu,hu₁⟩ := affineParameter_ne x hx
  have hs := fiber_card_le_six σ (affineParameter x) (b 0) (b 1) (b 2)
    hu hu₁ (hb 0) (hb 1) (hb 2) (univ.image z) (by
      intro v hv
      obtain ⟨j,_,rfl⟩ := mem_image.mp hv
      exact hn j)
  simpa [card_image_of_injective _ hz] using hs

/-- For a fixed-field affine parameter, the bound improves to three. -/
theorem fixed_three_spheres_card_le_three [Fintype J]
    (σ : E →+* E) (x : Fin 3 → E) (hx : Function.Injective x)
    (hfix : σ (affineParameter x) = affineParameter x)
    (w : J → E) (hw : Function.Injective w) (a : Fin 3 → E)
    (ha : ∀ i, a i ≠ 0) (h : ∀ i j, norm σ (x i+w j) = a i) :
    Fintype.card J ≤ 3 := by
  obtain ⟨b,hb,z,hz,hn⟩ := normalize_spheres σ x hx w hw a ha h
  obtain ⟨hu,hu₁⟩ := affineParameter_ne x hx
  have hs := fixed_fiber_card_le_three σ (affineParameter x) (b 0) (b 1) (b 2)
    hfix hu hu₁ (hb 0) (hb 1) (hb 2) (univ.image z) (by
      intro v hv
      obtain ⟨j,_,rfl⟩ := mem_image.mp hv
      exact hn j)
  simpa [card_image_of_injective _ hz] using hs

/-- The three reciprocal centers associated to four distinct rows. -/
def centers (x : Fin 4 → E) (i : Fin 3) : E := (x i.succ-x 0)⁻¹

lemma centers_injective (x : Fin 4 → E) (hx : Function.Injective x) :
    Function.Injective (centers x) := by
  intro i j hij
  exact Fin.succ_injective 3 (hx (sub_left_injective (inv_injective hij)))

/-- Every denominator in the four-row reciprocal transformation is checked. -/
lemma normalize_rows (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x)
    (y : J → E) (hy : Function.Injective y) (a : Fin 4 → E) (b : J → E)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) :
    ∃ c : Fin 3 → E, (∀ i, c i ≠ 0) ∧ ∃ w : J → E, Function.Injective w ∧
      ∀ i j, norm σ (centers x i+w j) = c i := by
  have hsum (j : J) : x 0+y j ≠ 0 := by
    intro he
    have hn := h 0 j
    rw [he] at hn
    exact mul_ne_zero (ha 0) (hb j) (by simpa [Erdos714CubicSegre.norm] using hn.symm)
  let w (j : J) := (x 0+y j)⁻¹
  let c (i : Fin 3) := a i.succ/(a 0*norm σ (x i.succ-x 0))
  have hd (i : Fin 3) : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
  refine ⟨c, (fun i => div_ne_zero (ha i.succ) (mul_ne_zero (ha 0) (norm_ne_zero σ (hd i)))), w, ?_, ?_⟩
  · intro i j hij
    exact hy (add_left_cancel (inv_injective hij))
  · intro i j
    have he : centers x i+w j =
        (x i.succ+y j)/((x i.succ-x 0)*(x 0+y j)) := by
      dsimp [w,centers]
      field_simp [hsum j,hd i]
      ring
    rw [he,Erdos714CubicSegre.norm_div,Erdos714CubicSegre.norm_mul,h i.succ j,h 0 j]
    dsimp [c]
    field_simp [hb j,norm_ne_zero σ (hd i)]

/-- Four distinct weighted rows cannot have seven distinct common columns. -/
theorem four_rows_card_le_six [Fintype J]
    (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x)
    (y : J → E) (hy : Function.Injective y) (a : Fin 4 → E) (b : J → E)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : Fintype.card J ≤ 6 := by
  obtain ⟨c,hc,w,hw,hn⟩ := normalize_rows σ x hx y hy a b ha hb h
  exact three_spheres_card_le_six σ (centers x) (centers_injective x hx) w hw c hc hn

/-- A fixed cross-ratio is an explicit sufficient condition for the stronger bound. -/
theorem fixed_four_rows_card_le_three [Fintype J]
    (σ : E →+* E) (x : Fin 4 → E) (hx : Function.Injective x)
    (hfix : σ (affineParameter (centers x)) = affineParameter (centers x))
    (y : J → E) (hy : Function.Injective y) (a : Fin 4 → E) (b : J → E)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j) : Fintype.card J ≤ 3 := by
  obtain ⟨c,hc,w,hw,hn⟩ := normalize_rows σ x hx y hy a b ha hb h
  exact fixed_three_spheres_card_le_three σ (centers x) (centers_injective x hx)
    hfix w hw c hc hn

/-- The reciprocal affine parameter is the usual four-point cross-ratio. -/
lemma parameter_eq_crossRatio (x : Fin 4 → E) (hx : Function.Injective x) :
    affineParameter (centers x) =
      ((x 2-x 0)*(x 3-x 1))/((x 2-x 1)*(x 3-x 0)) := by
  have hd (i j : Fin 4) (hij : i ≠ j) : x i-x j ≠ 0 := sub_ne_zero.mpr (hx.ne hij)
  unfold affineParameter
  apply (div_eq_div_iff
    (sub_ne_zero.mpr ((centers_injective x hx).ne (by decide : (1 : Fin 3) ≠ 0)))
    (mul_ne_zero (hd 2 1 (by decide)) (hd 3 0 (by decide)))).mpr
  dsimp [centers]
  field_simp [hd 1 0 (by decide),hd 2 0 (by decide),hd 3 0 (by decide)]
  ring

open SimpleGraph
open Erdos714CubicSegre (normGraph)
variable {F : Type*} [Field F] [Algebra F E]

private lemma same_side {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A norm graph with this cubic conjugate formula is K4,7-free. -/
theorem graph_free_of_norm_formula (σ : E →+* E)
    (hN : ∀ z, algebraMap F E (Algebra.norm F z) = norm σ z) :
    (completeBipartiteGraph (Fin 4) (Fin 7)).Free (normGraph (F := F) (E := E)) := by
  rintro ⟨f⟩
  let L (i : Fin 4) := f (Sum.inl i)
  let R (j : Fin 7) := f (Sum.inr j)
  have he (i : Fin 4) (j : Fin 7) :
      (normGraph (F := F) (E := E)).Adj (L i) (R j) :=
    f.toHom.map_adj (by simp)
  have hx : Function.Injective (fun i => (L i).2.1) := by
    intro i j hij
    change (L i).2.1 = (L j).2.1 at hij
    have hw : ((L i).2.2 : F) = ((L j).2.2 : F) := by
      apply mul_right_cancel₀ (R 0).2.2.ne_zero
      rw [← (he i 0).2,← (he j 0).2,hij]
    have hv : L i = L j := Prod.ext (same_side (he i 0).1 (he j 0).1)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inl.inj (f.injective hv)
  have hy : Function.Injective (fun j => (R j).2.1) := by
    intro i j hij
    change (R i).2.1 = (R j).2.1 at hij
    have hw : ((R i).2.2 : F) = ((R j).2.2 : F) := by
      apply mul_left_cancel₀ (L 0).2.2.ne_zero
      rw [← (he 0 i).2,← (he 0 j).2,hij]
    have hv : R i = R j := Prod.ext (same_side (he 0 i).1.symm (he 0 j).1.symm)
      (Prod.ext hij (Units.ext hw))
    exact Sum.inr.inj (f.injective hv)
  have hbound := four_rows_card_le_six σ
    (fun i => (L i).2.1) hx (fun j => (R j).2.1) hy
    (fun i => algebraMap F E ((L i).2.2 : F)) (fun j => algebraMap F E ((R j).2.2 : F))
    (fun i => (_root_.map_ne_zero _).mpr (L i).2.2.ne_zero)
    (fun j => (_root_.map_ne_zero _).mpr (R j).2.2.ne_zero) (by
      intro i j
      rw [← hN,(he i j).2,map_mul])
  norm_num at hbound

/-- K4,7-freeness of the ordinary weighted norm graph over every finite cubic extension. -/
theorem normGraph_free [Fintype F] [Fintype E] (hdim : Module.finrank F E = 3) :
    (completeBipartiteGraph (Fin 4) (Fin 7)).Free (normGraph (F := F) (E := E)) := by
  let σ : E →+* E := (FiniteField.frobeniusAlgHom F E).toRingHom
  apply graph_free_of_norm_formula σ
  intro z
  change algebraMap F E (Algebra.norm F z) =
    z*(z^Fintype.card F)*((z^Fintype.card F)^Fintype.card F)
  rw [FiniteField.algebraMap_norm_eq_prod_pow F E z,hdim]
  simp only [Finset.prod_range_succ,Finset.prod_range_zero,pow_zero,pow_one,one_mul,
    Nat.card_eq_fintype_card,← pow_mul,pow_two]

#print axioms four_rows_card_le_six
#print axioms fixed_four_rows_card_le_three
#print axioms parameter_eq_crossRatio
#print axioms graph_free_of_norm_formula
#print axioms normGraph_free
end Erdos714CubicFour
