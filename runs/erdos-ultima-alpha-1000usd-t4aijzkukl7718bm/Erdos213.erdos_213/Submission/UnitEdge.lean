import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.PiL2
import FormalConjecturesForMathlib.Geometry.«2d»

/-! A necessary separation condition for arbitrary nontrilinear integral-distance
sets. This does not impose a scale-independent upper bound on their cardinality. -/
open EuclideanGeometry
namespace Erdos213.UnitEdge

lemma rational_square_not_three_mod_four (r : ℤ) :
    ¬ IsSquare ((4*r^2-1 : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨m,hm⟩
  have hh := congrArg (fun z : ℤ => (z : ZMod 4)) hm
  push_cast at hh
  rw [show (4 : ZMod 4)=0 by decide,zero_mul,zero_sub] at hh
  have hm4 : ∀ z : ZMod 4, z*z ≠ -1 := by decide
  exact hm4 m hh.symm

lemma half_abscissa_unique {p q : ℂ} {r s k : ℤ}
    (hp : p.re=1/2) (hq : q.re=1/2)
    (hr : ‖p‖=(r : ℝ)) (hs : ‖q‖=(s : ℝ))
    (hk : dist p q=(k : ℝ)) : p=q := by
  by_contra hpq
  have hk0 : k ≠ 0 := by
    intro hz
    exact hpq (dist_eq_zero.mp (by simpa [hz] using hk))
  have hn1 : p.im^2=(r : ℝ)^2-1/4 := by
    have hh := Complex.sq_norm p
    rw [hr,Complex.normSq_apply,hp] at hh
    nlinarith only [hh]
  have hn2 : q.im^2=(s : ℝ)^2-1/4 := by
    have hh := Complex.sq_norm q
    rw [hs,Complex.normSq_apply,hq] at hh
    nlinarith only [hh]
  have hv2 : (p.im-q.im)^2=(k : ℝ)^2 := by
    have hh := Complex.sq_norm (p-q)
    rw [← dist_eq_norm,hk,Complex.normSq_apply] at hh
    simp only [Complex.sub_re,Complex.sub_im,hp,hq,sub_self,zero_mul,zero_add] at hh
    nlinarith only [hh]
  obtain ⟨d,hd,hd0⟩ : ∃ d : ℤ, p.im-q.im=(d : ℝ) ∧ d ≠ 0 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hv2 with hv | hv
    · exact ⟨k,hv,hk0⟩
    · exact ⟨-k,by simpa only [Int.cast_neg] using hv,neg_ne_zero.mpr hk0⟩
  let v : ℚ := ((r : ℚ)^2-(s : ℚ)^2+(d : ℚ)^2)/(d : ℚ)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hv : (v : ℝ)=2*p.im := by
    dsimp [v]
    push_cast
    apply (div_eq_iff hdR).mpr
    rw [← hd]
    nlinarith only [hn1,hn2]
  have hsq : IsSquare ((4*r^2-1 : ℤ) : ℚ) := by
    refine ⟨v,?_⟩
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [hv]
    nlinarith only [hn1]
  exact rational_square_not_three_mod_four r hsq

lemma distances_equal_of_unit_edge {a b p : ℂ} {r s : ℤ}
    (hab : dist a b=1) (hr : dist a p=(r : ℝ)) (hs : dist b p=(s : ℝ))
    (htri : ¬ Collinear ℝ ({a,b,p} : Set ℂ)) : r=s := by
  have h1 : dist a p < dist a b + dist b p := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro h
    exact htri h.collinear
  have h2 : dist b p < dist b a + dist a p := by
    apply dist_lt_dist_add_dist_iff.mpr
    intro h
    apply htri
    simpa only [Set.insert_comm] using h.collinear
  rw [hab,hr,hs] at h1
  rw [dist_comm b a,hab,hr,hs] at h2
  have h1' : r < 1+s := by exact_mod_cast h1
  have h2' : s < 1+r := by exact_mod_cast h2
  omega

lemma third_point_unique {a b p q : ℂ}
    (hab : dist a b=1)
    (hap : dist a p ∈ Set.range ((↑) : ℤ → ℝ))
    (hbp : dist b p ∈ Set.range ((↑) : ℤ → ℝ))
    (haq : dist a q ∈ Set.range ((↑) : ℤ → ℝ))
    (hbq : dist b q ∈ Set.range ((↑) : ℤ → ℝ))
    (hpq : dist p q ∈ Set.range ((↑) : ℤ → ℝ))
    (hpt : ¬ Collinear ℝ ({a,b,p} : Set ℂ))
    (hqt : ¬ Collinear ℝ ({a,b,q} : Set ℂ)) : p=q := by
  obtain ⟨r,hr⟩ := hap
  obtain ⟨s,hs⟩ := hbp
  obtain ⟨u,hu⟩ := haq
  obtain ⟨v,hv⟩ := hbq
  obtain ⟨k,hk⟩ := hpq
  have hrs := distances_equal_of_unit_edge hab hr.symm hs.symm hpt
  have huv := distances_equal_of_unit_edge hab hu.symm hv.symm hqt
  subst s v
  let f : ℂ → ℂ := fun z => (starRingEnd ℂ) (b-a)*(z-a)
  have hf (z w : ℂ) : dist (f z) (f w)=dist z w := by
    simp only [f,dist_eq_norm,← mul_sub,sub_sub_sub_cancel_right,norm_mul,Complex.norm_conj]
    have hn : ‖b-a‖=1 := by simpa only [dist_eq_norm, norm_sub_rev] using hab
    rw [hn,one_mul]
  have hfa : f a=0 := by simp [f]
  have hfn (z : ℂ) : ‖f z‖=dist a z := by
    rw [← dist_zero_right,← hfa,hf,dist_comm]
  have hfr (z : ℂ) : 2*(f z).re=dist a b^2+dist a z^2-dist b z^2 := by
    simp only [f,dist_eq_norm,Complex.sq_norm,Complex.normSq_apply,
      Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im]
    ring
  have hpr : (f p).re=1/2 := by
    have hh := hfr p
    rw [hab,← hr,← hs] at hh
    linarith only [hh]
  have hqr : (f q).re=1/2 := by
    have hh := hfr q
    rw [hab,← hu,← hv] at hh
    linarith only [hh]
  have he := half_abscissa_unique hpr hqr
    ((hfn p).trans hr.symm) ((hfn q).trans hu.symm) ((hf p q).trans hk.symm)
  apply dist_eq_zero.mp
  rw [← hf p q,he,dist_self]

/-- A unit edge in a nontrilinear integral-distance set forces cardinality at
most three. Finiteness and the no-four-on-a-circle condition are not needed. -/
theorem ncard_le_three_of_unit_edge {S : Set ℂ}
    (htri : NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hab : dist a b=1) : S.ncard ≤ 3 := by
  classical
  have hab' : a ≠ b := by intro he; simpa [he] using hab
  by_cases hsub : S ⊆ {a,b}
  · have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair hab'] at hh
    omega
  · obtain ⟨c,hc,hcn⟩ := Set.not_subset.mp hsub
    have hca : c ≠ a := by intro he; exact hcn (by simp [he])
    have hcb : c ≠ b := by intro he; exact hcn (by simp [he])
    have hsub' : S ⊆ {a,b,c} := by
      intro p hp
      by_cases hpa : p=a
      · simp [hpa]
      by_cases hpb : p=b
      · simp [hpb]
      by_cases hpc : p=c
      · simp [hpc]
      have he := third_point_unique hab
        (hint ha hp (Ne.symm hpa)) (hint hb hp (Ne.symm hpb))
        (hint ha hc hca.symm) (hint hb hc hcb.symm) (hint hp hc hpc)
        (htri ha hb hp hab' (Ne.symm hpb) (Ne.symm hpa))
        (htri ha hb hc hab' hcb.symm hca.symm)
      exact (hpc he).elim
    calc S.ncard ≤ ({a,b,c} : Set ℂ).ncard := Set.ncard_le_ncard hsub'
         _ ≤ ({b,c} : Set ℂ).ncard+1 := Set.ncard_insert_le _ _
         _ = 3 := by rw [Set.ncard_pair hcb.symm]

lemma collinear_affine_image {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) {T : Set E} (h : Collinear ℝ T) :
    Collinear ℝ (f '' T) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o,v,h⟩ := h
  refine ⟨f o, f.linear v, ?_⟩
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨r,rfl⟩ := h p hp
  refine ⟨r, ?_⟩
  simp only [AffineMap.map_vadd, map_smul]

lemma nontrilinear_affine_image {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E ≃ᵃ[ℝ] F) {S : Set E} (htri : NonTrilinear S) :
    NonTrilinear (f '' S) := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hxy hyz hxz hc
  have hback := collinear_affine_image f.symm.toAffineMap hc
  have hc' : Collinear ℝ ({x,y,z} : Set E) := by
    simpa only [Set.image_insert_eq,Set.image_singleton,AffineEquiv.coe_toAffineMap,
      AffineEquiv.symm_apply_apply] using hback
  exact htri hx hy hz (fun he => hxy (he ▸ rfl)) (fun he => hyz (he ▸ rfl))
    (fun he => hxz (he ▸ rfl)) hc'

theorem plane_ncard_le_three_of_unit_edge {S : Set ℝ²}
    (htri : NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hab : dist a b=1) : S.ncard ≤ 3 := by
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  have hT : NonTrilinear (e '' S) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hxy hyz hxz hc
    have hback := collinear_affine_image e.symm.toLinearEquiv.toAffineEquiv.toAffineMap hc
    have hc' : Collinear ℝ ({x,y,z} : Set ℝ²) := by
      simpa only [Set.image_insert_eq,Set.image_singleton,LinearEquiv.coe_toAffineEquiv,
        AffineEquiv.coe_toAffineMap,LinearIsometryEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.symm_apply_apply] using hback
    exact htri hx hy hz (fun he => hxy (he ▸ rfl)) (fun he => hyz (he ▸ rfl))
      (fun he => hxz (he ▸ rfl)) hc'
  have hI : (e '' S).Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    rw [e.isometry.dist_eq]
    exact hint hx hy (fun he => hxy (he ▸ rfl))
  have hh := ncard_le_three_of_unit_edge hT hI
    (Set.mem_image_of_mem e ha) (Set.mem_image_of_mem e hb)
    ((e.isometry.dist_eq a b).trans hab)
  rwa [Set.ncard_image_of_injective _ e.injective] at hh

/-- This applies to every witness of the original conjecture with n>=4.
It is only a lower bound on separation, not a bound on the number of points. -/
theorem plane_distance_ge_two {S : Set ℝ²} (hcard : 3 < S.ncard)
    (htri : NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : 2 ≤ dist a b := by
  obtain ⟨k,hk⟩ := hint ha hb hab
  have hkpos : (0 : ℝ)<k := hk ▸ dist_pos.mpr hab
  have hkpos' : (0 : ℤ)<k := by exact_mod_cast hkpos
  have hk1 : k ≠ 1 := by
    intro he
    have hu : dist a b=1 := by simpa [he] using hk.symm
    exact (not_lt_of_ge (plane_ncard_le_three_of_unit_edge htri hint ha hb hu)) hcard
  have hk2 : (2 : ℤ) ≤ k := by omega
  rw [← hk]
  exact_mod_cast hk2

#print axioms third_point_unique
#print axioms ncard_le_three_of_unit_edge
#print axioms plane_ncard_le_three_of_unit_edge
#print axioms plane_distance_ge_two
end Erdos213.UnitEdge
