import Submission.DegenerateCrossGraphExplore
import Submission.CommonOriginFamilyExplore

/-! Parabolas with parameter-dependent intercepts preserve their parameter
set in row zero. Complete root counts have the usual character-fiber bound,
but curves can intersect away from the origin. We keep multiplicity explicit. -/
namespace Erdos66InterceptCurve
open Erdos66FiniteField Erdos66CrossGraph Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1600000

variable {F : Type*} [Field F] [DecidableEq F]

def value (u k : F) : F := u+k^2/u
def point (u k : F) : F × F := (value u k,k)

omit [DecidableEq F] in
lemma point_injective (u : F) : Function.Injective (point u) := by
  intro k l h
  exact congrArg Prod.snd h

omit [DecidableEq F] in
lemma value_zero (u : F) : value u 0=u := by simp [value]

omit [DecidableEq F] in
lemma value_collision (u v k : F) (hu : u≠0) (hv : v≠0) :
    value u k=value v k ↔ u=v ∨ u*v=k^2 := by
  have he : u*v*(value u k-value v k)=(u-v)*(u*v-k^2) := by
    unfold value
    field_simp
    ring
  rw [← sub_eq_zero,← mul_eq_zero_iff_left (mul_ne_zero hu hv),he,mul_eq_zero]
  simp only [sub_eq_zero]

variable [Fintype F]

def curve (u : F) : Finset (F × F) := Finset.univ.image (point u)
def curveUnion (U : Finset F) : Finset (F × F) := U.biUnion curve

def multiplicity (U : Finset F) (z : F × F) : ℕ :=
  (U.filter (fun u ↦ z∈curve u)).card

lemma mem_curve (u : F) (z : F × F) : z∈curve u ↔ z.1=value u z.2 := by
  constructor
  · intro h
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp h
    rfl
  · intro h
    exact Finset.mem_image.mpr ⟨z.2,Finset.mem_univ _,Prod.ext h.symm rfl⟩

lemma mem_curveUnion (U : Finset F) (z : F × F) :
    z∈curveUnion U ↔ ∃u∈U, z.1=value u z.2 := by
  simp only [curveUnion,Finset.mem_biUnion,mem_curve]

lemma curveUnion_row_zero (U : Finset F) (x : F) :
    (x,0)∈curveUnion U ↔ x∈U := by
  simp only [mem_curveUnion,value_zero]
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact hu
  · exact fun h ↦ ⟨x,h,rfl⟩

lemma curve_card (u : F) : (curve u).card=Fintype.card F := by
  rw [curve,Finset.card_image_of_injective _ (point_injective u),Finset.card_univ]

/-- Three distinct nonzero labels cannot pass through one point. -/
lemma multiplicity_le_two (U : Finset F) (hU : ∀u∈U,u≠0) (z : F × F) :
    multiplicity U z≤2 := by
  by_contra h
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ :=
    Finset.two_lt_card_iff.mp (show 2<(U.filter (fun u ↦ z∈curve u)).card by
      change ¬ (U.filter (fun u ↦ z∈curve u)).card≤2 at h
      omega)
  obtain ⟨hu,heu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv,hev⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw,hew⟩ := Finset.mem_filter.mp hw
  have hv0 := hU v hv
  have h₁ := (value_collision u v z.2 (hU u hu) hv0).mp
    ((mem_curve u z).mp heu |>.symm.trans ((mem_curve v z).mp hev))
  have h₂ := (value_collision v w z.2 hv0 (hU w hw)).mp
    ((mem_curve v z).mp hev |>.symm.trans ((mem_curve w z).mp hew))
  have h₁' := h₁.resolve_left huv
  have h₂' := h₂.resolve_left hvw
  have huew : u=w := mul_right_cancel₀ hv0 (by rw [h₁',mul_comm w v,h₂'])
  exact huw huew

def rootCount (u v q t : F) : ℕ :=
  (Finset.univ.filter (fun k ↦ value u k+value v (q-k)=t)).card

def weightedCount (U V : Finset F) (q t : F) : ℤ :=
  ∑u∈U, ∑v∈V, (rootCount u v q t : ℤ)

lemma rootCount_parabola (u v q t : F) :
    rootCount u v q t=Fintype.card {k : F // k^2/u+(q-k)^2/v=t-(u+v)} := by
  rw [Fintype.card_subtype]
  unfold rootCount
  congr 1
  ext k
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,value]
  constructor <;> intro h <;> linear_combination h

lemma rootCount_formula (hF : ringChar F≠2) (u v q t : F)
    (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    (rootCount u v q t : ℤ)=1+quadraticChar F u*quadraticChar F v*
      quadraticChar F ((u+v)*(t-(u+v))-q^2) := by
  rw [rootCount_parabola]
  exact parabola_sum_count hF u v q (t-(u+v)) hu hv huv

lemma weightedCount_formula (hF : ringChar F≠2) (U V : Finset F)
    (hU : ∀u∈U,u≠0) (hV : ∀v∈V,v≠0)
    (hUV : ∀u∈U,∀v∈V,u+v≠0) (q t : F) :
    weightedCount U V q t=(U.card : ℤ)*V.card+
      ∑s : F, crossCharFiber U V s*quadraticChar F (s*(t-s)-q^2) := by
  have he : weightedCount U V q t=(U.card : ℤ)*V.card+
      ∑u∈U,∑v∈V, quadraticChar F u*quadraticChar F v*
        quadraticChar F ((u+v)*(t-(u+v))-q^2) := by
    calc
      _ = ∑u∈U,∑v∈V, (1+quadraticChar F u*quadraticChar F v*
          quadraticChar F ((u+v)*(t-(u+v))-q^2)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact rootCount_formula hF u v q t (hU u hu) (hV v hv) (hUV u hu v hv)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  congr 1
  symm
  simp only [crossCharFiber,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]

lemma weightedCount_error (hF : ringChar F≠2) (U V : Finset F)
    (hU : ∀u∈U,u≠0) (hV : ∀v∈V,v≠0)
    (hUV : ∀u∈U,∀v∈V,u+v≠0) (q t : F) :
    |weightedCount U V q t-(U.card : ℤ)*V.card|≤∑s : F, |crossCharFiber U V s| := by
  rw [weightedCount_formula hF U V hU hV hUV,add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (quadraticChar_abs_le_one (s*(t-s)-q^2)) (abs_nonneg _)

lemma curve_pairCount (u v q t : F) :
    pairCount (curve u) (curve v) (t,q)=rootCount u v q t := by
  unfold pairCount
  rw [show curve u=Finset.univ.image (point u) from rfl,Finset.filter_image,
    Finset.card_image_of_injective _ (point_injective u)]
  unfold rootCount
  congr 1
  ext k
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_curve,Prod.fst_sub,Prod.snd_sub,
    point]
  constructor <;> intro h <;> linear_combination -h

end Erdos66InterceptCurve
