import Submission.QuadraticFieldLiftExplore

/-! Quadratic extensions preserve the curve class but erase quadratic
characters of old parameters. Actual inherited unions consequently have
holes, and have double counts at suitable square targets. -/
namespace Erdos66QuadraticExtensionCharacter
open Erdos66QuadraticFieldLift Erdos66FiniteField Erdos66OriginRepair
  Erdos66ParabolaRepair Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 3000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (d : F) [Fact (¬IsSquare d)]

/-- Every old scalar, not only d, becomes a square in the quadratic field. -/
lemma base_isSquare (u : F) : IsSquare (algebraMap F (Quad d) u) := by
  by_cases hu : IsSquare u
  · exact hu.map (algebraMap F (Quad d))
  · have hd : ¬IsSquare d := Fact.out
    have hd0 : d≠0 := by intro h; exact hd ⟨0,by simp [h]⟩
    have hu0 : u≠0 := by intro h; exact hu ⟨0,by simp [h]⟩
    have hχd := quadraticChar_neg_one_iff_not_isSquare.mpr hd
    have hχu := quadraticChar_neg_one_iff_not_isSquare.mpr hu
    have hid : d*(u/d)=u := by field_simp
    have hh := congrArg (quadraticChar F) hid
    rw [map_mul,hχd,hχu] at hh
    have hχ : quadraticChar F (u/d)=1 := by linarith
    obtain ⟨r,hr⟩ := (quadraticChar_one_iff_isSquare (div_ne_zero hu0 hd0)).mp hχ
    have hprod : u=(r*r)*d := (div_eq_iff hd0).mp hr
    refine ⟨(⟨0,r⟩:Quad d),?_⟩
    ext <;> simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,mul_zero,zero_mul,add_zero,zero_add]
    linear_combination hprod

lemma base_quadraticChar (u : F) (hu : u≠0) :
    quadraticChar (Quad d) (algebraMap F (Quad d) u)=1 :=
  (quadraticChar_one_iff_isSquare ((map_ne_zero (algebraMap F (Quad d))).mpr hu)).mpr
    (base_isSquare d u)

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E]

/-- This hole mechanism only needs an embedding whose image consists of
squares. It imposes no nonzero or opposite-pair restriction on the labels. -/
theorem mapped_union_nonsquare_hole (j : F →+* E) (hj : ∀ u : F, IsSquare (j u))
    (U V : Finset F) (s : E) (hs : ¬IsSquare s) :
    pairCount (parabolaSet (U.image j)) (parabolaSet (V.image j)) (0,s)=0 := by
  unfold pairCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨x,y⟩ hz
  obtain ⟨hU,hV⟩ := Finset.mem_filter.mp hz
  simp only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_image,Prod.fst_sub,Prod.snd_sub,zero_sub] at hU hV
  obtain ⟨u',⟨u,hu,rfl⟩,hy⟩ := hU
  obtain ⟨v',⟨v,hv,rfl⟩,hz⟩ := hV
  have he : s=x^2*j (u⁻¹+v⁻¹) := by
    simp only [map_add,map_inv₀]
    simp only [neg_sq,div_eq_mul_inv] at hy hz
    linear_combination hy+hz
  obtain ⟨r,hr⟩ := hj (u⁻¹+v⁻¹)
  apply hs
  refine ⟨x*r,?_⟩
  rw [he,hr]
  ring

lemma mapped_root_double (j : F →+* E) (hj : ∀ u : F, IsSquare (j u))
    (hE : ringChar E≠2) (u v : F) (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    (Fintype.card {x : E // x^2/j u+(0-x)^2/j v=1}:ℤ)=2 := by
  have hchar (a : F) (ha : a≠0) : quadraticChar E (j a)=1 :=
    (quadraticChar_one_iff_isSquare ((map_ne_zero j).mpr ha)).mpr (hj a)
  rw [parabola_sum_count hE (j u) (j v) 0 1 ((map_ne_zero j).mpr hu)
    ((map_ne_zero j).mpr hv) (by rw [←map_add]; exact (map_ne_zero j).mpr huv)]
  simp only [mul_one,zero_pow (by decide : 2≠0),sub_zero,←map_add,
    hchar u hu,hchar v hv,hchar (u+v) huv]
  norm_num

/-- With no opposite labels, every ordered parameter pair contributes TWO
roots at (0,1). At that target no common-origin multiplicity correction is
present, so this is an exact count for the actual union. -/
theorem mapped_union_double (j : F →+* E) (hj : ∀ u : F, IsSquare (j u))
    (hE : ringChar E≠2) (U V : Finset F)
    (hU : ∀ u∈U, u≠0) (hV : ∀ v∈V, v≠0)
    (hUV : ∀ u∈U, ∀ v∈V, u+v≠0) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    pairCount (parabolaSet (U.image j)) (parabolaSet (V.image j)) (0,1)=2*U.card*V.card := by
  have hcount : crossGraphCount (U.image j) (V.image j) 0 1=2*(U.card:ℤ)*V.card := by
    unfold crossGraphCount
    rw [Finset.sum_image (fun _ _ _ _ h ↦ j.injective h)]
    simp_rw [Finset.sum_image (fun _ _ _ _ h ↦ j.injective h)]
    calc
      _ = ∑ u∈U, ∑ v∈V, (2:ℤ) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact mapped_root_double j hj hE u v (hU u hu) (hV v hv) (hUV u hu v hv)
      _ = _ := by simp; ring
  have hU' : ∀ u∈U.image j, u≠0 := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    exact (map_ne_zero j).mpr (hU a ha)
  have hV' : ∀ u∈V.image j, u≠0 := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    exact (map_ne_zero j).mpr (hV a ha)
  have he := crossGraphCount_correction (U.image j) (V.image j) hU' hV'
    (hUne.image _) (hVne.image _) 0 1
  have hi (W : Finset E) : graphIndicator W (0,1)=0 := by simp [graphIndicator]
  rw [hcount,hi,hi] at he
  norm_num at he
  have hactual := parabolaSet_crossCount_eq (U.image j) (V.image j) (0,1)
  rw [←he] at hactual
  exact_mod_cast hactual

/-- In particular a quadratic field extension gives an actual inherited
union with a hole, regardless of how good the old character pattern was. -/
theorem quadratic_extension_hole (hF : ringChar F≠2) (U V : Finset F) :
    ∃ s : Quad d, s≠0 ∧
      pairCount (parabolaSet (U.image (algebraMap F (Quad d))))
        (parabolaSet (V.image (algebraMap F (Quad d)))) (0,s)=0 := by
  obtain ⟨s,hs⟩ := FiniteField.exists_nonsquare (F := Quad d) (by rwa [quad_char])
  have hs0 : s≠0 := by intro h; exact hs ⟨0,by simp [h]⟩
  exact ⟨s,hs0,mapped_union_nonsquare_hole (algebraMap F (Quad d)) (base_isSquare d) U V s hs⟩

end Erdos66QuadraticExtensionCharacter
