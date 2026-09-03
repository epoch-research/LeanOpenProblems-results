import Submission.InterceptCurveExplore
import Submission.TwofoldFamilyExplore

/-! The exact set-level correction and total mass for intercept parabolas.
The collision count is not silently discarded from the root formula. -/
namespace Erdos66InterceptCollisionCorrection
open Erdos66InterceptCurve Erdos66TwofoldFamily Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1800000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev collisionSet (U : Finset F) : Finset (F × F) := collisions U curve

lemma familyMult_eq (U : Finset F) (z : F × F) :
    familyMult U curve z=multiplicity U z := rfl

lemma weighted_set_correction (U : Finset F) (hU : ∀u∈U,u≠0) (q t : F) :
    (weightedCount U U q t : ℝ)=
      (pairCount (curveUnion U) (curveUnion U) (t,q) : ℝ)+
        2*pairCount (curveUnion U) (collisionSet U) (t,q)+
        pairCount (collisionSet U) (collisionSet U) (t,q) := by
  have hh := representation_correction U curve (fun z ↦ multiplicity_le_two U hU z) (t,q)
  simp_rw [curve_pairCount] at hh
  simpa only [weightedCount,Int.cast_sum,Int.cast_natCast] using hh

lemma curve_union_mass (U : Finset F) (hU : ∀u∈U,u≠0) :
    (U.card : ℝ)*Fintype.card F=(curveUnion U).card+(collisionSet U).card := by
  have hh := mass_correction U curve (fun z ↦ multiplicity_le_two U hU z)
  simpa only [curve_card,Finset.sum_const,nsmul_eq_mul] using hh

lemma curve_intersection_card (u v : F) (hu : u≠0) (hv : v≠0) (huv : u≠v) :
    (curve u∩curve v).card=(Finset.univ.filter (fun k : F ↦ k^2=u*v)).card := by
  have hset : curve u∩curve v=
      (Finset.univ.filter (fun k : F ↦ k^2=u*v)).image (point u) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzu,hzv⟩ := Finset.mem_inter.mp hz
      have hu' := (mem_curve u z).mp hzu
      have hv' := (mem_curve v z).mp hzv
      have hc := ((value_collision u v z.2 hu hv).mp (hu'.symm.trans hv')).resolve_left huv
      exact Finset.mem_image.mpr ⟨z.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc.symm⟩,
        Prod.ext hu'.symm rfl⟩
    · intro hz
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
      have hk' := (Finset.mem_filter.mp hk).2
      apply Finset.mem_inter.mpr
      constructor
      · exact (mem_curve u (point u k)).mpr rfl
      · apply (mem_curve v (point u k)).mpr
        exact (value_collision u v k hu hv).mpr (Or.inr hk'.symm)
  rw [hset,Finset.card_image_of_injective _ (point_injective u)]

lemma curve_intersection_character (hF : ringChar F≠2) (u v : F)
    (hu : u≠0) (hv : v≠0) (huv : u≠v) :
    ((curve u∩curve v).card : ℤ)=1+quadraticChar F u*quadraticChar F v := by
  rw [curve_intersection_card u v hu hv huv]
  have hh := quadraticChar_card_sqrts hF (u*v)
  have he : ({k : F | k^2=u*v}.toFinset)=Finset.univ.filter (fun k : F ↦ k^2=u*v) := by
    ext k
    simp
  rw [he,map_mul] at hh
  linarith

lemma intersection_formula (hF : ringChar F≠2) (u v : F) (hu : u≠0) (hv : v≠0) :
    ((curve u∩curve v).card : ℝ)=1+(quadraticChar F u : ℝ)*quadraticChar F v+
      (if u=v then (Fintype.card F : ℝ)-2 else 0) := by
  by_cases huv : u=v
  · subst v
    rw [Finset.inter_self,curve_card,if_pos rfl]
    have hh : (quadraticChar F u : ℝ)^2=1 := by exact_mod_cast quadraticChar_sq_one hu
    nlinarith
  · rw [if_neg huv,add_zero]
    exact_mod_cast curve_intersection_character hF u v hu hv huv

/-- The number of collision points depends only on the character imbalance
of the labels, not on their arrangement in the field. -/
theorem collision_card_formula (hF : ringChar F≠2) (U : Finset F)
    (hU : ∀u∈U,u≠0) :
    2*(collisionSet U).card=(U.card : ℝ)^2-2*U.card+
      (∑u∈U,(quadraticChar F u : ℝ))^2 := by
  have hh := collision_mass_formula U curve (fun z ↦ multiplicity_le_two U hU z)
  have hi : (∑u∈U,∑v∈U, ((curve u∩curve v).card : ℝ))=
      (U.card : ℝ)^2+(∑u∈U,(quadraticChar F u : ℝ))^2+
        (U.card : ℝ)*((Fintype.card F : ℝ)-2) := by
    calc
      _ = ∑u∈U,∑v∈U, (1+(quadraticChar F u : ℝ)*quadraticChar F v+
          (if u=v then (Fintype.card F : ℝ)-2 else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact intersection_formula hF u v (hU u hu) (hU v hv)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,
          Finset.sum_ite_eq,← Finset.mul_sum,← Finset.sum_mul]
        have hs : (∑u∈U, if u∈U then (Fintype.card F : ℝ)-2 else 0)=
            (U.card : ℝ)*((Fintype.card F : ℝ)-2) := by
          simp only [Finset.sum_ite_mem,Finset.inter_self,Finset.sum_const,nsmul_eq_mul]
        rw [hs]
        ring
  rw [hi] at hh
  simp only [curve_card,Finset.sum_const,nsmul_eq_mul] at hh
  convert hh using 1
  ring

lemma collision_card_le_square (hF : ringChar F≠2) (U : Finset F)
    (hU : ∀u∈U,u≠0) : (collisionSet U).card≤U.card^2 := by
  have hh := collision_card_formula hF U hU
  have hs : |∑u∈U,(quadraticChar F u : ℝ)|≤(U.card : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑_u∈U,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact_mod_cast Erdos66FiniteField.quadraticChar_abs_le_one u
      _ = _ := by simp
  have hsq : (∑u∈U,(quadraticChar F u : ℝ))^2≤(U.card : ℝ)^2 :=
    by
      have he := (sq_le_sq₀ (abs_nonneg (∑u∈U,(quadraticChar F u : ℝ)))
        (Nat.cast_nonneg U.card)).mpr hs
      simpa only [sq_abs] using he
  have hc : ((collisionSet U).card : ℝ)≤(U.card : ℝ)^2 := by
    nlinarith [Nat.cast_nonneg U.card (α := ℝ)]
  exact_mod_cast hc

end Erdos66InterceptCollisionCorrection
