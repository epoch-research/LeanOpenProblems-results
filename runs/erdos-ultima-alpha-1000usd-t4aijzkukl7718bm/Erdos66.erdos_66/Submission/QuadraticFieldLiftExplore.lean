import Submission.ChangingFieldLogCapExplore
import Submission.DisjointCurvePaletteExplore
import Submission.ShearedParabolaPrefixExplore

/-! A non-Cartesian quadratic-field lift. The old coordinate depends on the
new row, and each lifted curve is again a single parabola over a field. -/
namespace Erdos66QuadraticFieldLift
open Erdos66OriginRepair Erdos66ParabolaRepair Erdos66DisjointCurvePalette
  Erdos66ShearedParabolaPrefix Erdos66FiniteField
open scoped Classical
set_option maxHeartbeats 3000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (d : F)

abbrev Quad := QuadraticAlgebra F d 0

noncomputable instance quadFintype : Fintype (Quad d) :=
  Fintype.ofEquiv (F×F) (QuadraticAlgebra.equivProd d 0).symm

instance quadNoRoot [Fact (¬IsSquare d)] : Fact (∀ r : F, r^2≠d+0*r) := by
  constructor
  intro r hr
  have h : d=r*r := by simpa only [zero_mul,add_zero,pow_two] using hr.symm
  exact (Fact.out : ¬IsSquare d) ⟨r,h⟩

lemma quad_card : Fintype.card (Quad d)=(Fintype.card F)^2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd d 0),Fintype.card_prod,pow_two]

lemma quad_char : ringChar (Quad d)=ringChar F := by
  letI : CharP (Quad d) (ringChar F) :=
    ((algebraMap F (Quad d)).charP_iff QuadraticAlgebra.algebraMap_injective (ringChar F)).mp
      (inferInstance : CharP F (ringChar F))
  exact ringChar.eq (Quad d) (ringChar F)

/-- Interleave the two input/output coordinates so that the old plane is
the zero slice of the new plane. This is an ADDITIVE equivalence. -/
def planeEquiv : ((F×F)×(F×F)) ≃+ (Quad d×Quad d) where
  toFun z := (⟨z.1.1,z.2.1⟩,⟨z.1.2,z.2.2⟩)
  invFun z := ((z.1.re,z.2.re),(z.1.im,z.2.im))
  left_inv z := by rfl
  right_inv z := by rfl
  map_add' z w := by rfl

variable [Fact (¬IsSquare d)]

noncomputable def liftCurve (u : F) : Finset ((F×F)×(F×F)) :=
  (curve (algebraMap F (Quad d) u)).image (planeEquiv d).symm

lemma mem_liftCurve (u r y x z : F) (hu : u≠0) :
    ((r,y),(x,z))∈liftCurve d u ↔
      y=(r^2+d*x^2)/u ∧ z=(2*r*x)/u := by
  have hu' : algebraMap F (Quad d) u≠0 := (map_ne_zero (algebraMap F (Quad d))).mpr hu
  have he : ((r,y),(x,z))=(planeEquiv d).symm (⟨r,x⟩,⟨y,z⟩) := rfl
  rw [he,liftCurve,Finset.mem_image]
  have hmem : (∃ a∈curve (algebraMap F (Quad d) u), (planeEquiv d).symm a=
      (planeEquiv d).symm (⟨r,x⟩,⟨y,z⟩)) ↔
      (⟨r,x⟩,⟨y,z⟩)∈curve (algebraMap F (Quad d) u) := by
    constructor
    · rintro ⟨a,ha,he⟩
      rwa [(planeEquiv d).symm.injective he] at ha
    · intro ha; exact ⟨_,ha,rfl⟩
  rw [hmem,mem_curve,eq_div_iff hu']
  change (⟨y,z⟩:Quad d)*algebraMap F (Quad d) u=(⟨r,x⟩:Quad d)^2 ↔ _
  rw [QuadraticAlgebra.ext_iff]
  simp only [pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
    mul_zero,zero_mul,add_zero,zero_add]
  rw [eq_div_iff hu,eq_div_iff hu]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h1,h2⟩
    constructor
    · linear_combination h1
    · linear_combination h2

/-- Every old point is retained exactly on the new zero slice. -/
lemma liftCurve_zero_slice (u : F) (hu : u≠0) (r y : F) :
    ((r,y),((0:F),0))∈liftCurve d u ↔ (r,y)∈curve u := by
  rw [mem_liftCurve d u r y 0 0 hu,mem_curve]
  simp

lemma curve_card {E : Type*} [Field E] [Fintype E] [DecidableEq E] (u : E) :
    (curve u).card=Fintype.card E := by
  rw [curve,Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h),Finset.card_univ]

lemma liftCurve_card (u : F) : (liftCurve d u).card=(Fintype.card F)^2 := by
  rw [liftCurve,Finset.card_image_of_injective _ (planeEquiv d).symm.injective,curve_card,quad_card]

lemma liftCurve_pairCount (u v : F) (z : (F×F)×(F×F)) :
    pairCount (liftCurve d u) (liftCurve d v) z=
      pairCount (curve (algebraMap F (Quad d) u)) (curve (algebraMap F (Quad d) v))
        (planeEquiv d z) := by
  have he := pairCount_addEquiv (planeEquiv d).symm
    (curve (algebraMap F (Quad d) u)) (curve (algebraMap F (Quad d) v)) (planeEquiv d z)
  simpa only [AddEquiv.symm_apply_apply,liftCurve] using he

/-- The joint cap is TWO, not twice the previous cap. The lift is a parabola
over a larger field, not a product of two old parabolas. -/
theorem liftCurve_joint_cap (hF : ringChar F≠2) (u v : F)
    (hu : u≠0) (hv : v≠0) (huv : u+v≠0) (z : (F×F)×(F×F)) :
    pairCount (liftCurve d u) (liftCurve d v) z≤2 := by
  rw [liftCurve_pairCount]
  have hE : ringChar (Quad d)≠2 := by rwa [quad_char]
  have hu' : algebraMap F (Quad d) u≠0 := (map_ne_zero (algebraMap F (Quad d))).mpr hu
  have hv' : algebraMap F (Quad d) v≠0 := (map_ne_zero (algebraMap F (Quad d))).mpr hv
  have huv' : algebraMap F (Quad d) u+algebraMap F (Quad d) v≠0 := by
    rw [←map_add]; exact (map_ne_zero (algebraMap F (Quad d))).mpr huv
  by_cases hz : planeEquiv d z=0
  · rw [hz,curve_origin _ _ hu' hv' huv']
    norm_num
  · exact curve_pairCount_le_two hE _ _ hu' hv' _ hz

/-- The individual curve mean is still one. This alone is not a logarithmic
profile and says nothing about intermediate natural-number prefixes. -/
lemma liftCurve_mean (u : F) :
    ((liftCurve d u).card:ℝ)^2/(Fintype.card ((F×F)×(F×F)):ℝ)=1 := by
  rw [liftCurve_card]
  simp only [Fintype.card_prod,Nat.cast_mul,Nat.cast_pow]
  have hq : (Fintype.card F:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Erdos66QuadraticFieldLift
