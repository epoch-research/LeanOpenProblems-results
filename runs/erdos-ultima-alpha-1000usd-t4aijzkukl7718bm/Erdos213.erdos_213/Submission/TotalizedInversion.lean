import Submission.InversionReduction

/-! Totalized inversion at an included point fixes that point. In this case it
preserves general position and rational distances up to a common real scaling.
This is not a cardinality-growing construction and does not settle Erdős 213. -/
open EuclideanGeometry
namespace Erdos213.TotalizedInversion
open InversionReduction
noncomputable section
set_option maxHeartbeats 3000000

@[simp] lemma invert_zero : invert (0 : ℝ²)=0 := by simp [invert]

lemma image_invert_invert (S : Set ℝ²) : invert '' (invert '' S)=S := by
  rw [Set.image_image]
  simp only [invert_involutive,Set.image_id']

/-- The scale need not be rational. -/
def RationalAtScale (S : Set ℝ²) (r : ℝ) : Prop :=
  S.Pairwise (fun p q => r*dist p q ∈ Set.range ((↑) : ℚ → ℝ))

lemma rational_at_inverse_scale {S : Set ℝ²} {r : ℝ} (hr : r ≠ 0)
    (hzero : (0 : ℝ²) ∈ S) (h : RationalAtScale S r) :
    RationalAtScale (invert '' S) r⁻¹ := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
  have hpq' : p ≠ q := fun he => hpq (congrArg invert he)
  by_cases hp0 : p=0
  · subst p
    obtain ⟨a,ha⟩ := h hzero hq hpq'
    refine ⟨a⁻¹,?_⟩
    rw [invert_zero,invert_eq_inversion,dist_center_inversion]
    push_cast
    rw [ha]
    simp [mul_inv_rev,div_eq_mul_inv,mul_comm]
  by_cases hq0 : q=0
  · subst q
    obtain ⟨a,ha⟩ := h hp hzero hpq'
    refine ⟨a⁻¹,?_⟩
    rw [invert_zero,invert_eq_inversion,dist_inversion_center]
    push_cast
    rw [ha]
    simp [mul_inv_rev,div_eq_mul_inv,mul_comm]
  obtain ⟨a,ha⟩ := h hp hzero hp0
  obtain ⟨b,hb⟩ := h hq hzero hq0
  obtain ⟨c,hc⟩ := h hp hq hpq'
  refine ⟨c/(a*b),?_⟩
  rw [invert_eq_inversion,invert_eq_inversion,dist_inversion_inversion hp0 hq0]
  push_cast
  rw [ha,hb,hc]
  field_simp [hr,dist_ne_zero.mpr hp0,dist_ne_zero.mpr hq0]

lemma rational_at_scale_iff {S : Set ℝ²} {r : ℝ} (hr : r ≠ 0)
    (hzero : (0 : ℝ²) ∈ S) :
    RationalAtScale (invert '' S) r ↔ RationalAtScale S r⁻¹ := by
  constructor
  · intro h
    have hz : (0 : ℝ²) ∈ invert '' S := ⟨0,hzero,invert_zero⟩
    simpa only [image_invert_invert] using rational_at_inverse_scale hr hz h
  · intro h
    simpa only [inv_inv] using rational_at_inverse_scale (inv_ne_zero hr) hzero h

lemma rational_some_scale_iff {S : Set ℝ²} (hzero : (0 : ℝ²) ∈ S) :
    (∃ r : ℝ, 0<r ∧ RationalAtScale (invert '' S) r) ↔
      (∃ r : ℝ, 0<r ∧ RationalAtScale S r) := by
  constructor
  · rintro ⟨r,hr,h⟩
    exact ⟨r⁻¹,inv_pos.mpr hr,(rational_at_scale_iff (ne_of_gt hr) hzero).mp h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r⁻¹,inv_pos.mpr hr,rational_at_inverse_scale (ne_of_gt hr) hzero h⟩

lemma collinear_invert_of_zero {S : Set ℝ²} (hzero : (0 : ℝ²) ∈ S)
    (h : Collinear ℝ S) : Collinear ℝ (invert '' S) := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem hzero).mp h
  apply (collinear_iff_of_mem (show (0 : ℝ²)∈invert '' S from ⟨0,hzero,invert_zero⟩)).mpr
  refine ⟨v,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨t,ht⟩ := hv p hp
  refine ⟨(radiusSq p)⁻¹*t,?_⟩
  simp only [vadd_eq_add,add_zero] at ht ⊢
  rw [invert,ht,smul_smul]

lemma linear_equation_collinear {S : Set ℝ²} {b c d : ℝ}
    (hn : b≠0 ∨ c≠0) (h : ∀ p∈S, b*p 0+c*p 1+d=0) : Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  by_cases hb : b=0
  · have hc : c≠0 := hn.resolve_left (by simpa using hb)
    refine ⟨!₂[0,-d/c],!₂[1,0],?_⟩
    intro p hp
    refine ⟨p 0,?_⟩
    have hh := h p hp
    rw [hb] at hh
    ext i
    fin_cases i
    · simp
    · simp
      field_simp
      nlinarith only [hh]
  · refine ⟨!₂[-d/b,0],!₂[-c/b,1],?_⟩
    intro p hp
    refine ⟨p 1,?_⟩
    have hh := h p hp
    ext i
    fin_cases i
    · simp
      field_simp
      nlinarith only [hh]
    · simp

/-- A circle containing the fixed pole pulls back to a line off the pole. -/
lemma circle_through_zero_pullback {T : Set ℝ²} (hT : T.Nonempty) (hz : 0∉T)
    (h : Cospherical (insert 0 (invert '' T))) : Collinear ℝ T := by
  obtain ⟨o,r,ho⟩ := h
  have h0 := congrArg (fun x : ℝ => x^2) (ho 0 (by simp))
  have he (p : ℝ²) (hp : p∈T) :
      radiusSq (invert p)-2*o 0*(invert p) 0-2*o 1*(invert p) 1=0 := by
    have h1 := congrArg (fun x : ℝ => x^2) (ho (invert p) (Set.mem_insert_of_mem 0 (Set.mem_image_of_mem invert hp)))
    dsimp only at h0 h1
    rw [distance_sq] at h0 h1
    dsimp [radiusSq]
    simp at h0
    nlinarith only [h0,h1]
  have hline (p : ℝ²) (hp : p∈T) : (-2*o 0)*p 0+(-2*o 1)*p 1+1=0 := by
    have hp0 : p≠0 := fun hh => hz (hh ▸ hp)
    have hi := inverse_equation hp0 1 (-2*o 0) (-2*o 1) 0
    have hh := he p hp
    dsimp at hi
    linear_combination radiusSq p*hh-hi
  have hn : -2*o 0≠0 ∨ -2*o 1≠0 := by
    by_contra! hh
    obtain ⟨p,hp⟩ := hT
    have he := hline p hp
    rw [hh.1,hh.2] at he
    norm_num at he
  exact linear_equation_collinear hn hline

lemma general_position_invert {S : Set ℝ²} (hzero : (0 : ℝ²)∈S)
    (h : InGeneralPosition S) : InGeneralPosition (invert '' S) := by
  have haway := inversion_general_position hzero (noFour_of_general_position h)
  constructor
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ _ ⟨r,hr,rfl⟩ hpq hqr hpr hcol
    have hpq' : p≠q := fun he => hpq (congrArg invert he)
    have hqr' : q≠r := fun he => hqr (congrArg invert he)
    have hpr' : p≠r := fun he => hpr (congrArg invert he)
    by_cases hz : p=0 ∨ q=0 ∨ r=0
    · have hz' : (0 : ℝ²)∈({invert p,invert q,invert r} : Set ℝ²) := by
        rcases hz with rfl | rfl | rfl <;> simp
      have hh := collinear_invert_of_zero hz' hcol
      simp only [Set.image_insert_eq,Set.image_singleton,invert_involutive] at hh
      exact h.1 hp hq hr hpq' hqr' hpr' hh
    · push_neg at hz
      exact haway.1 ⟨p,⟨hp,by simpa using hz.1⟩,rfl⟩
        ⟨q,⟨hq,by simpa using hz.2.1⟩,rfl⟩
        ⟨r,⟨hr,by simpa using hz.2.2⟩,rfl⟩ hpq hqr hpr hcol
  · intro Q hQ hn hcos
    by_cases hz : (0 : ℝ²)∈Q
    · let T : Set ℝ² := invert '' (Q \ {0})
      have hTcard : T.ncard=3 := by
        change (invert '' (Q \ {0})).ncard=3
        rw [Set.ncard_image_of_injective _ invert_injective,
          Set.ncard_diff_singleton_of_mem hz,hn]
      have hTsub : T⊆S := by
        rintro _ ⟨p,hp,rfl⟩
        obtain ⟨q,hq,rfl⟩ := hQ hp.1
        simpa only [invert_involutive] using hq
      have hTzero : (0 : ℝ²)∉T := by
        rintro ⟨p,hp,he⟩
        exact invert_nonzero (by simpa using hp.2) he
      have hTcirc : Cospherical (insert 0 (invert '' T)) := by
        have he : insert (0 : ℝ²) (invert '' T)=Q := by
          change insert (0 : ℝ²) (invert '' (invert '' (Q \ {0})))=Q
          rw [image_invert_invert]
          ext p
          simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
          constructor
          · rintro (rfl | ⟨hp,_⟩)
            · exact hz
            · exact hp
          · intro hp
            by_cases hp0 : p=0
            · exact Or.inl hp0
            · exact Or.inr ⟨hp,hp0⟩
        rwa [he]
      have hTcol := circle_through_zero_pullback
        (Set.nonempty_of_ncard_ne_zero (by omega : T.ncard≠0)) hTzero hTcirc
      obtain ⟨p,q,r,hpq,hpr,hqr,he⟩ := Set.ncard_eq_three.mp hTcard
      rw [he] at hTsub hTcol
      exact h.1 (hTsub (by simp)) (hTsub (by simp)) (hTsub (by simp)) hpq hqr hpr hTcol
    · apply haway.2 Q ?_ hn hcos
      intro p hp
      obtain ⟨q,hq,rfl⟩ := hQ hp
      refine ⟨q,⟨hq,?_⟩,rfl⟩
      have hq0 : q≠0 := by
        rintro rfl
        exact hz (by simpa using hp)
      simpa using hq0

/-- Unlike deleting a pole, keeping an included pole fixed preserves strong
general position in both directions. No finiteness hypothesis is needed. -/
theorem general_position_iff {S : Set ℝ²} (hzero : (0 : ℝ²)∈S) :
    InGeneralPosition (invert '' S) ↔ InGeneralPosition S := by
  constructor
  · intro h
    simpa only [image_invert_invert] using
      general_position_invert (show (0 : ℝ²)∈invert '' S from ⟨0,hzero,invert_zero⟩) h
  · exact general_position_invert hzero

/-- This operation neither repairs general position nor creates rational
pairwise distances up to dilation when the pole is one of the retained points. -/
theorem general_position_rational_scale_iff {S : Set ℝ²} (hzero : (0 : ℝ²)∈S) :
    (InGeneralPosition (invert '' S) ∧ ∃ r : ℝ, 0<r ∧ RationalAtScale (invert '' S) r) ↔
      (InGeneralPosition S ∧ ∃ r : ℝ, 0<r ∧ RationalAtScale S r) := by
  rw [general_position_iff hzero,rational_some_scale_iff hzero]

lemma collinear_translate (v : ℝ²) {S : Set ℝ²} (h : Collinear ℝ S) :
    Collinear ℝ ((fun p : ℝ² => p+v) '' S) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o,w,hw⟩ := h
  refine ⟨o+v,w,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨t,rfl⟩ := hw p hp
  exact ⟨t,by simp [add_assoc]⟩

lemma cospherical_translate (v : ℝ²) {S : Set ℝ²} (h : Cospherical S) :
    Cospherical ((fun p : ℝ² => p+v) '' S) := by
  obtain ⟨o,r,ho⟩ := h
  refine ⟨o+v,r,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  simpa using ho p hp

lemma translate_injective (v : ℝ²) : Function.Injective (fun p : ℝ² => p+v) := by
  intro p q hh
  exact add_right_cancel hh

lemma image_translate_cancel (S : Set ℝ²) (v : ℝ²) :
    (fun p : ℝ² => p-v) '' ((fun p : ℝ² => p+v) '' S)=S := by
  rw [Set.image_image]
  simp

lemma general_position_translate (v : ℝ²) {S : Set ℝ²} (h : InGeneralPosition S) :
    InGeneralPosition ((fun p : ℝ² => p+v) '' S) := by
  constructor
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ _ ⟨r,hr,rfl⟩ hpq hqr hpr hcol
    have hh := collinear_translate (-v) hcol
    simp only [Set.image_insert_eq,Set.image_singleton,add_neg_cancel_right] at hh
    exact h.1 hp hq hr (fun he => hpq (congrArg (fun p => p+v) he))
      (fun he => hqr (congrArg (fun p => p+v) he))
      (fun he => hpr (congrArg (fun p => p+v) he)) hh
  · intro Q hQ hn hcos
    apply h.2 ((fun p : ℝ² => p+(-v)) '' Q) ?_ ?_ (cospherical_translate (-v) hcos)
    · rintro _ ⟨p,hp,rfl⟩
      obtain ⟨q,hq,rfl⟩ := hQ hp
      simpa using hq
    · rwa [Set.ncard_image_of_injective _ (translate_injective (-v))]

lemma general_position_translate_iff (v : ℝ²) (S : Set ℝ²) :
    InGeneralPosition ((fun p : ℝ² => p+v) '' S) ↔ InGeneralPosition S := by
  constructor
  · intro h
    have hh := general_position_translate (-v) h
    simpa only [←sub_eq_add_neg,image_translate_cancel] using hh
  · exact general_position_translate v

lemma rational_translate (v : ℝ²) {S : Set ℝ²} {r : ℝ} (h : RationalAtScale S r) :
    RationalAtScale ((fun p : ℝ² => p+v) '' S) r := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
  simpa using h hp hq (fun he => hpq (congrArg (fun p => p+v) he))

lemma rational_translate_iff (v : ℝ²) (S : Set ℝ²) (r : ℝ) :
    RationalAtScale ((fun p : ℝ² => p+v) '' S) r ↔ RationalAtScale S r := by
  constructor
  · intro h
    have hh := rational_translate (-v) h
    simpa only [←sub_eq_add_neg,image_translate_cancel] using hh
  · exact rational_translate v

lemma centered_inversion_formula (o p : ℝ²) : inversion o 1 p=invert (p-o)+o := by
  rw [invert_eq_inversion]
  simp [inversion,dist_eq_norm]

lemma centered_inversion_image (o : ℝ²) (S : Set ℝ²) :
    inversion o 1 '' S =
      (fun p : ℝ² => p+o) '' (invert '' ((fun p : ℝ² => p-o) '' S)) := by
  rw [Set.image_image,Set.image_image]
  congr 1
  funext p
  exact centered_inversion_formula o p

/-- General-position equivalence at any retained center, for Mathlib's actual
Euclidean inversion, including its fixed-center value. -/
theorem centered_general_position_iff {S : Set ℝ²} {o : ℝ²} (ho : o∈S) :
    InGeneralPosition (inversion o 1 '' S) ↔ InGeneralPosition S := by
  have hz : (0 : ℝ²) ∈ ((fun p : ℝ² => p-o) '' S) := ⟨o,ho,by simp⟩
  rw [centered_inversion_image,general_position_translate_iff,general_position_iff hz]
  simpa only [sub_eq_add_neg] using general_position_translate_iff (-o) S

/-- The exact scale changes from `r` to `r⁻¹`; the retained center is essential. -/
theorem centered_rational_at_scale_iff {S : Set ℝ²} {o : ℝ²} (ho : o∈S)
    {r : ℝ} (hr : r≠0) :
    RationalAtScale (inversion o 1 '' S) r ↔ RationalAtScale S r⁻¹ := by
  have hz : (0 : ℝ²) ∈ ((fun p : ℝ² => p-o) '' S) := ⟨o,ho,by simp⟩
  rw [centered_inversion_image,rational_translate_iff,rational_at_scale_iff hr hz]
  simpa only [sub_eq_add_neg] using rational_translate_iff (-o) S r⁻¹

/-- Inversion at a selected center followed by a positive common dilation
cannot turn a source without general position or common-scale rational
lengths into one having both properties. -/
theorem centered_rational_general_position_iff {S : Set ℝ²} {o : ℝ²} (ho : o∈S) :
    (InGeneralPosition (inversion o 1 '' S) ∧
      ∃ r : ℝ, 0<r ∧ RationalAtScale (inversion o 1 '' S) r) ↔
    (InGeneralPosition S ∧ ∃ r : ℝ, 0<r ∧ RationalAtScale S r) := by
  rw [centered_general_position_iff ho]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨r,hr,h⟩
    exact ⟨r⁻¹,inv_pos.mpr hr,(centered_rational_at_scale_iff ho (ne_of_gt hr)).mp h⟩
  · rintro ⟨r,hr,h⟩
    refine ⟨r⁻¹,inv_pos.mpr hr,?_⟩
    apply (centered_rational_at_scale_iff ho (inv_ne_zero (ne_of_gt hr))).mpr
    simpa using h

/-- Adding the pole after inversion is equivalent to first adding it to the
source. The missing distance conditions cannot be bypassed this way. -/
theorem adjoin_pole_iff (S : Set ℝ²) (o : ℝ²) :
    (InGeneralPosition (insert o (inversion o 1 '' S)) ∧
      ∃ r : ℝ, 0<r ∧ RationalAtScale (insert o (inversion o 1 '' S)) r) ↔
    (InGeneralPosition (insert o S) ∧
      ∃ r : ℝ, 0<r ∧ RationalAtScale (insert o S) r) := by
  simpa only [Set.image_insert_eq,inversion_self] using
    centered_rational_general_position_iff (show o∈insert o S from Set.mem_insert o S)

#print axioms adjoin_pole_iff
#print axioms centered_general_position_iff
#print axioms centered_rational_at_scale_iff
#print axioms centered_rational_general_position_iff
#print axioms rational_at_scale_iff
#print axioms general_position_iff
#print axioms general_position_rational_scale_iff

end
end Erdos213.TotalizedInversion
