import FormalConjecturesUtil

/-! A characteristic-coordinate normalization for integral-distance sets.
This file develops necessary arithmetic conditions, not a solution to Erdős 213. -/

open EuclideanGeometry

namespace Erdos213.Normalization

set_option maxHeartbeats 1000000

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
    (f : E ≃ᵃ[ℝ] F) {T : Set E} (h : NonTrilinear T) :
    NonTrilinear (f '' T) := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩ hxy hyz hxz hc
  have hb := collinear_affine_image f.symm.toAffineMap hc
  simp only [Set.image_insert_eq, Set.image_singleton, AffineEquiv.coe_toAffineMap,
    AffineEquiv.symm_apply_apply] at hb
  exact h hx hy hz (fun he => hxy (he ▸ rfl)) (fun he => hyz (he ▸ rfl))
    (fun he => hxz (he ▸ rfl)) hb

lemma general_position_affine_similarity
    (f : ℝ² ≃ᵃ[ℝ] ℝ²) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ x y, dist (f x) (f y) = c * dist x y)
    {T : Set ℝ²} (h : InGeneralPosition T) : InGeneralPosition (f '' T) := by
  refine ⟨nontrilinear_affine_image f h.1, ?_⟩
  intro Q hQT hcard hcos
  let Q' : Set ℝ² := f.symm '' Q
  have hsub : Q' ⊆ T := by
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨q,hq,rfl⟩ := hQT hp
    simpa using hq
  have hcard' : Q'.ncard = 4 := by
    rw [Set.ncard_image_of_injective _ f.symm.injective]
    exact hcard
  apply h.2 Q' hsub hcard'
  obtain ⟨o,r,ho⟩ := hcos
  refine ⟨f.symm o, r/c, ?_⟩
  rintro _ ⟨p,hp,rfl⟩
  have he := hf (f.symm p) (f.symm o)
  simp only [AffineEquiv.apply_symm_apply] at he
  rw [ho p hp] at he
  apply (eq_div_iff hc).mpr
  nlinarith [he]

noncomputable def complexSimilarity (a k : ℂ) (hk : k ≠ 0) : ℂ ≃ᵃ[ℝ] ℂ :=
  (AffineEquiv.constVAdd ℝ ℂ (-a)).trans
    ((LinearEquiv.smulOfNeZero ℂ ℂ k hk).restrictScalars ℝ).toAffineEquiv

@[simp] lemma complexSimilarity_apply (a k : ℂ) (hk : k ≠ 0) (z : ℂ) :
    complexSimilarity a k hk z = k * (z-a) := by
  change k * (-a+z) = k * (z-a)
  ring

lemma complexSimilarity_dist (a k : ℂ) (hk : k ≠ 0) (z w : ℂ) :
    dist (complexSimilarity a k hk z) (complexSimilarity a k hk w) = ‖k‖ * dist z w := by
  simp only [complexSimilarity_apply, dist_eq_norm]
  rw [← mul_sub, sub_sub_sub_cancel_right, norm_mul]

noncomputable def frame (a b z : ℂ) : ℂ := (starRingEnd ℂ) (b-a) * (z-a)

lemma frame_re (a b p : ℂ) :
    2 * (frame a b p).re = dist a b^2 + dist a p^2 - dist b p^2 := by
  simp only [frame, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

lemma frame_im_product (a b c p : ℂ) :
    4 * (frame a b c).im * (frame a b p).im =
      2 * dist a b^2 * (dist a c^2+dist a p^2-dist c p^2) -
      (dist a b^2+dist a c^2-dist b c^2) * (dist a b^2+dist a p^2-dist b p^2) := by
  simp only [frame, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im]
  ring

lemma frame_discriminant (a b c : ℂ) :
    (2 * (frame a b c).im)^2 =
      4 * dist a b^2 * dist a c^2 - (dist a b^2+dist a c^2-dist b c^2)^2 := by
  have h := frame_im_product a b c c
  simp only [dist_self, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  nlinarith [h]

lemma frame_im_ne_zero {a b c : ℂ} (h : ¬Collinear ℝ {a,b,c}) :
    (frame a b c).im ≠ 0 := by
  intro hz
  apply h
  by_cases hab : b = a
  · subst b
    simpa using (collinear_pair ℝ a c)
  have hv : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hdiv : ((c-a)/(b-a)).im = 0 := by
    rw [Complex.div_im]
    have hn : (c-a).im*(b-a).re-(c-a).re*(b-a).im = 0 := by
      simp only [frame, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hz
      linear_combination hz
    rw [← sub_div, hn, zero_div]
  let r : ℝ := ((c-a)/(b-a)).re
  have he : (c-a)/(b-a) = (r : ℂ) := by
    apply Complex.ext <;> simp [r, hdiv]
  have he' : c = r • (b-a) + a := by
    have hmul := (div_eq_iff hv).mp he
    rw [Complex.real_smul]
    linear_combination hmul
  rw [collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℂ))]
  refine ⟨b-a, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨r, he'⟩

lemma integral_dist_all {S : Set ℂ}
    (h : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) : dist a b ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_cases hab : a = b
  · subst b
    exact ⟨0, by simp⟩
  · exact h ha hb hab

/-- Every noncollinear integral-distance set in the complex plane can be
normalized into an integer lattice with one common square-root characteristic.
The normalizing similarity has a positive integer scale factor. No finiteness
assumption is needed for this reduction. -/
lemma integral_complex_normalization {S : Set ℂ}
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b c : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (htri : ¬Collinear ℝ {a,b,c}) :
    ∃ D L : ℕ, 0 < D ∧ 0 < L ∧ ∃ f : ℂ ≃ᵃ[ℝ] ℂ,
      (∀ z w, dist (f z) (f w) = (L : ℝ) * dist z w) ∧
      ∀ z ∈ S, ∃ x y : ℤ, f z = (x : ℂ) + (y : ℂ) * (Real.sqrt D : ℂ) * Complex.I := by
  obtain ⟨K,hK⟩ := integral_dist_all hint ha hb
  obtain ⟨M,hM⟩ := integral_dist_all hint ha hc
  obtain ⟨N,hN⟩ := integral_dist_all hint hb hc
  have hab : a ≠ b := by
    intro he
    subst b
    exact htri (by simpa using collinear_pair ℝ a c)
  have hKpos : (0 : ℝ) < K := by rw [hK]; exact dist_pos.mpr hab
  have hKzero : K ≠ 0 := by exact_mod_cast (ne_of_gt hKpos)
  let C : ℤ := K^2+M^2-N^2
  let d : ℤ := 4*K^2*M^2-C^2
  let α : ℝ := 2*(frame a b c).im
  have hα0 : α ≠ 0 := mul_ne_zero (by norm_num) (frame_im_ne_zero htri)
  have hαsq : α^2 = (d : ℝ) := by
    dsimp [α,d,C]
    rw [frame_discriminant, ← hK, ← hM, ← hN]
    push_cast
    rfl
  have hdpos : 0 < d := by
    have hh : (0 : ℝ) < d := hαsq ▸ sq_pos_of_ne_zero hα0
    exact_mod_cast hh
  let D : ℕ := d.toNat
  have hDcast : (D : ℤ) = d := Int.toNat_of_nonneg hdpos.le
  have hDreal : (D : ℝ) = (d : ℝ) := by exact_mod_cast hDcast
  have hDpos : 0 < D := by exact_mod_cast (hDcast ▸ hdpos : (0 : ℤ) < (D : ℤ))
  have hDα : (D : ℝ) = α^2 := hDreal.trans hαsq.symm
  have hKabs : (K.natAbs : ℝ) = dist a b := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hKpos, hK]
  let L : ℕ := 2*D*K.natAbs
  have hLpos : 0 < L := Nat.mul_pos (Nat.mul_pos (by decide) hDpos) (Int.natAbs_pos.mpr hKzero)
  let κ : ℂ := (2*(D : ℂ)) * (starRingEnd ℂ) (b-a)
  have hκ : κ ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hDpos))
    · intro hzero
      have hh := congrArg (starRingEnd ℂ) hzero
      simp only [map_zero, RingHomCompTriple.comp_apply] at hh
      exact (sub_ne_zero.mpr hab.symm) hh
  let f := complexSimilarity a κ hκ
  have hκnorm : ‖κ‖ = (L : ℝ) := by
    dsimp [κ,L]
    simp only [norm_mul, Complex.norm_conj, norm_natCast]
    rw [← dist_eq_norm, dist_comm, ← hKabs]
    push_cast
    norm_num
  refine ⟨D,L,hDpos,hLpos,f,?_,?_⟩
  · intro z w
    rw [complexSimilarity_dist, hκnorm]
  · intro p hp
    obtain ⟨R,hR⟩ := integral_dist_all hint ha hp
    obtain ⟨U,hU⟩ := integral_dist_all hint hb hp
    obtain ⟨V,hV⟩ := integral_dist_all hint hc hp
    let A : ℤ := K^2+R^2-U^2
    let B : ℤ := M^2+R^2-V^2
    let Y : ℤ := 2*K^2*B-C*A
    have hA : 2*(frame a b p).re = (A : ℝ) := by
      rw [frame_re, ← hK, ← hR, ← hU]
      dsimp [A]
      push_cast
      rfl
    have hY : 2*α*(frame a b p).im = (Y : ℝ) := by
      dsimp [α]
      rw [show 2*(2*(frame a b c).im)*(frame a b p).im =
        4*(frame a b c).im*(frame a b p).im by ring,
        frame_im_product, ← hK, ← hM, ← hN, ← hR, ← hU, ← hV]
      dsimp [Y,B,C,A]
      push_cast
      ring
    have hf : f p = (2*(D : ℂ))*frame a b p := by
      dsimp [f]
      rw [complexSimilarity_apply]
      dsimp [κ,frame]
      ring
    have hx : (f p).re = (((D : ℤ)*A : ℤ) : ℝ) := by
      rw [hf]
      norm_num only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      push_cast
      linear_combination (D : ℝ) * hA
    have hy : (f p).im = (Y : ℝ)*α := by
      rw [hf]
      norm_num only [Complex.mul_im, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, zero_add]
      rw [hDα]
      linear_combination α * hY
    have hsqrt : Real.sqrt D = |α| := by rw [hDα, Real.sqrt_sq_eq_abs]
    rcases le_total 0 α with hpos | hneg
    · refine ⟨(D : ℤ)*A,Y,?_⟩
      apply Complex.ext <;> simp [hx,hy,hsqrt,abs_of_nonneg hpos]
    · refine ⟨(D : ℤ)*A,-Y,?_⟩
      apply Complex.ext <;> simp [hx,hy,hsqrt,abs_of_nonpos hneg]

#print axioms integral_complex_normalization

/-- The normalization theorem in the Euclidean plane used by the conjecture. -/
lemma integral_plane_normalization {S : Set ℝ²}
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b c : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (htri : ¬Collinear ℝ {a,b,c}) :
    ∃ D L : ℕ, 0 < D ∧ 0 < L ∧ ∃ f : ℝ² ≃ᵃ[ℝ] ℝ²,
      (∀ z w, dist (f z) (f w) = (L : ℝ) * dist z w) ∧
      ∀ z ∈ S, ∃ x y : ℤ, f z = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D] := by
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let T : Set ℂ := e '' S
  have hT : T.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
    rw [e.isometry.dist_eq]
    exact hint hp hq (fun he => hpq (he ▸ rfl))
  have htriangle : ¬Collinear ℝ {e a,e b,e c} := by
    intro hh
    have hback := collinear_affine_image e.symm.toLinearEquiv.toAffineEquiv.toAffineMap hh
    apply htri
    simpa only [Set.image_insert_eq, Set.image_singleton, LinearEquiv.coe_toAffineEquiv,
      AffineEquiv.coe_toAffineMap, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using hback
  obtain ⟨D,L,hD,hL,f,hf,hcoords⟩ := integral_complex_normalization hT
    (Set.mem_image_of_mem e ha) (Set.mem_image_of_mem e hb) (Set.mem_image_of_mem e hc) htriangle
  let g : ℝ² ≃ᵃ[ℝ] ℝ² := (e.toLinearEquiv.toAffineEquiv.trans f).trans
    e.symm.toLinearEquiv.toAffineEquiv
  refine ⟨D,L,hD,hL,g,?_,?_⟩
  · intro z w
    change dist (e.symm (f (e z))) (e.symm (f (e w))) = (L : ℝ)*dist z w
    rw [e.symm.isometry.dist_eq, hf, e.isometry.dist_eq]
  · intro z hz
    obtain ⟨x,y,hxy⟩ := hcoords (e z) (Set.mem_image_of_mem e hz)
    refine ⟨x,y,?_⟩
    change e.symm (f (e z)) = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]
    apply e.injective
    rw [e.apply_symm_apply, hxy]
    simp [e, Complex.orthonormalBasisOneI_repr_symm_apply]

/-- Any finite general-position integral-distance set of at least three points
has a same-cardinality general-position representative with integer
characteristic coordinates. -/
lemma general_position_integer_coordinates {S : Set ℝ²} (hfin : S.Finite)
    (hthree : 3 ≤ S.ncard) (hgen : InGeneralPosition S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ))) :
    ∃ D : ℕ, 0 < D ∧ ∃ T : Set ℝ², T.Finite ∧ T.ncard = S.ncard ∧
      InGeneralPosition T ∧
      T.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ∀ p ∈ T, ∃ x y : ℤ, p = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D] := by
  obtain ⟨U,hUS,hU3⟩ := Set.exists_subset_card_eq hthree
  obtain ⟨a,b,c,hab,hac,hbc,hU⟩ := Set.ncard_eq_three.mp hU3
  subst U
  have ha : a ∈ S := hUS (by simp)
  have hb : b ∈ S := hUS (by simp)
  have hc : c ∈ S := hUS (by simp)
  obtain ⟨D,L,hD,hL,f,hf,hcoords⟩ := integral_plane_normalization hint ha hb hc
    (hgen.1 ha hb hc hab hbc hac)
  refine ⟨D,hD,f '' S,hfin.image _,Set.ncard_image_of_injective _ f.injective,?_,?_,?_⟩
  · exact general_position_affine_similarity f (L : ℝ)
      (by exact_mod_cast (ne_of_gt hL)) hf hgen
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
    obtain ⟨r,hr⟩ := hint hp hq (fun he => hpq (he ▸ rfl))
    refine ⟨(L : ℤ)*r,?_⟩
    rw [hf, ← hr]
    push_cast
    rfl
  · rintro _ ⟨p,hp,rfl⟩
    exact hcoords p hp

#print axioms integral_plane_normalization
#print axioms general_position_integer_coordinates

/-- A rational-angle rotation followed by an integer dilation can make the
first coordinates of a finite characteristic-lattice set distinct. -/
lemma exists_injective_integer_projection {ι : Type*} [Finite ι]
    (D : ℕ) (hD : 0 < D) (x y : ι → ℤ)
    (hxy : Function.Injective (fun i => (x i,y i))) :
    ∃ m : ℤ, Function.Injective (fun i => (m^2-D)*x i-2*m*D*y i) := by
  classical
  let P (i j : ι) : Polynomial ℤ :=
    Polynomial.C (x i-x j)*Polynomial.X^2 -
      Polynomial.C (2*(D : ℤ)*(y i-y j))*Polynomial.X - Polynomial.C ((D : ℤ)*(x i-x j))
  have hP {i j : ι} (hij : i ≠ j) : P i j ≠ 0 := by
    intro he
    have h2 := congrArg (fun q : Polynomial ℤ => q.coeff 2) he
    simp only [P,Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,
      Polynomial.coeff_C,Polynomial.coeff_X,Polynomial.coeff_zero] at h2
    norm_num at h2
    have h1 := congrArg (fun q : Polynomial ℤ => q.coeff 1) he
    simp only [P,Polynomial.coeff_sub,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,
      Polynomial.coeff_C,Polynomial.coeff_X,Polynomial.coeff_zero] at h1
    norm_num at h1
    have hy : y i = y j := sub_eq_zero.mp (h1.resolve_left (ne_of_gt hD))
    apply hij
    exact hxy (Prod.ext (sub_eq_zero.mp h2) hy)
  let bad : Set ℤ := ⋃ i, ⋃ j, {m | i ≠ j ∧ (P i j).IsRoot m}
  have hbad : bad.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    by_cases hij : i = j
    · simp [hij]
    · exact (Polynomial.finite_setOf_isRoot (hP hij)).subset (by simp)
  obtain ⟨m,hm⟩ := hbad.exists_notMem
  refine ⟨m,?_⟩
  intro i j he
  by_contra hij
  apply hm
  simp only [bad,Set.mem_iUnion,Set.mem_setOf_eq]
  refine ⟨i,j,hij,?_⟩
  rw [Polynomial.IsRoot.def]
  simp only [P,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X]
  linear_combination he

#print axioms exists_injective_integer_projection

/-- Multiplication by `(m²-D)+2m√D i` is an integer-scale similarity which
preserves the characteristic lattice. -/
lemma integer_lattice_similarity (D : ℕ) (hD : 0 < D) (m : ℤ) :
    ∃ f : ℝ² ≃ᵃ[ℝ] ℝ²,
      (∀ z w, dist (f z) (f w) = (((m^2+D : ℤ) : ℝ)) * dist z w) ∧
      ∀ x y : ℤ, f !₂[(x : ℝ), (y : ℝ)*Real.sqrt D] =
        !₂[(((m^2-D)*x-2*m*D*y : ℤ) : ℝ),
          (((2*m*x+(m^2-D)*y : ℤ) : ℝ))*Real.sqrt D] := by
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let κ : ℂ := (((m^2-D : ℤ) : ℂ)) + (2*m : ℂ)*(Real.sqrt D : ℂ)*Complex.I
  have hsqrt : Real.sqrt D^2 = (D : ℝ) := Real.sq_sqrt (by positivity)
  have hsq : Complex.normSq κ = (((m^2+D : ℤ) : ℝ))^2 := by
    dsimp [κ]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero]
    push_cast
    linear_combination 4*(m : ℝ)^2*hsqrt
  have hpos : (0 : ℝ) < ((m^2+D : ℤ) : ℝ) := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    push_cast
    nlinarith [sq_nonneg (m : ℝ)]
  have hnorm : ‖κ‖ = (((m^2+D : ℤ) : ℝ)) := by
    apply (sq_eq_sq₀ (norm_nonneg _) hpos.le).mp
    rw [Complex.sq_norm,hsq]
  have hκ : κ ≠ 0 := by
    intro hh
    rw [hh,norm_zero] at hnorm
    linarith
  let fC := complexSimilarity 0 κ hκ
  let f : ℝ² ≃ᵃ[ℝ] ℝ² := (e.toLinearEquiv.toAffineEquiv.trans fC).trans
    e.symm.toLinearEquiv.toAffineEquiv
  refine ⟨f,?_,?_⟩
  · intro z w
    change dist (e.symm (fC (e z))) (e.symm (fC (e w))) =
      (((m^2+D : ℤ) : ℝ))*dist z w
    rw [e.symm.dist_map,complexSimilarity_dist,hnorm,e.dist_map]
  · intro x y
    apply e.injective
    change e (e.symm (fC (e !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]))) = _
    rw [e.apply_symm_apply,complexSimilarity_apply,sub_zero]
    simp only [e,Complex.orthonormalBasisOneI_repr_symm_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    apply Complex.ext
    · simp only [κ,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.intCast_re,Complex.intCast_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
      push_cast
      linear_combination -2*(m : ℝ)*(y : ℝ)*hsqrt
    · simp only [κ,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
        Complex.intCast_re,Complex.intCast_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        mul_zero,zero_mul,mul_one,add_zero,zero_add,sub_zero]
      push_cast
      ring

#print axioms integer_lattice_similarity

lemma integer_coordinates_with_injective_projection {D : ℕ} (hD : 0 < D)
    {S : Set ℝ²} (hfin : S.Finite) (hgen : InGeneralPosition S)
    (hint : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)))
    (hcoords : ∀ p ∈ S, ∃ x y : ℤ, p = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]) :
    ∃ T : Set ℝ², T.Finite ∧ T.ncard = S.ncard ∧ InGeneralPosition T ∧
      T.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ p ∈ T, ∃ x y : ℤ, p = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]) ∧
      Set.InjOn (fun p : ℝ² => p 0) T := by
  classical
  letI : Fintype S := hfin.fintype
  choose x y hxy using (fun p : S => hcoords p p.property)
  have hpair : Function.Injective (fun p : S => (x p,y p)) := by
    intro p q he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    change x p = x q at hx
    change y p = y q at hy
    apply Subtype.ext
    rw [hxy p,hxy q,hx,hy]
  obtain ⟨m,hm⟩ := exists_injective_integer_projection D hD x y hpair
  obtain ⟨f,hf,hfcoords⟩ := integer_lattice_similarity D hD m
  have hpos : (0 : ℝ) < ((m^2+D : ℤ) : ℝ) := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    push_cast
    nlinarith [sq_nonneg (m : ℝ)]
  refine ⟨f '' S,hfin.image _,Set.ncard_image_of_injective _ f.injective,?_,?_,?_,?_⟩
  · exact general_position_affine_similarity f _ (ne_of_gt hpos) hf hgen
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
    obtain ⟨r,hr⟩ := hint hp hq (fun he => hpq (he ▸ rfl))
    refine ⟨(m^2+D)*r,?_⟩
    rw [hf, ← hr]
    push_cast
    rfl
  · rintro _ ⟨p,hp,rfl⟩
    obtain ⟨a,b,hab⟩ := hcoords p hp
    rw [hab,hfcoords]
    exact ⟨(m^2-D)*a-2*m*D*b,2*m*a+(m^2-D)*b,rfl⟩
  · rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ he
    have hpxy := hxy ⟨p,hp⟩
    have hqxy := hxy ⟨q,hq⟩
    change p = _ at hpxy
    change q = _ at hqxy
    rw [hpxy,hqxy,hfcoords,hfcoords] at he
    simp only [Matrix.cons_val_zero] at he
    have he' : (m^2-D)*x ⟨p,hp⟩-2*m*D*y ⟨p,hp⟩ =
        (m^2-D)*x ⟨q,hq⟩-2*m*D*y ⟨q,hq⟩ := by exact_mod_cast he
    exact congrArg f (congrArg Subtype.val (hm he'))

/-- Characteristic-lattice coordinates with injective first coordinates are
not a restriction on the finite general-position integral-distance problem. -/
lemma general_position_integer_coordinates_injective {S : Set ℝ²} (hfin : S.Finite)
    (hthree : 3 ≤ S.ncard) (hgen : InGeneralPosition S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ))) :
    ∃ D : ℕ, 0 < D ∧ ∃ T : Set ℝ², T.Finite ∧ T.ncard = S.ncard ∧
      InGeneralPosition T ∧
      T.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ p ∈ T, ∃ x y : ℤ, p = !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]) ∧
      Set.InjOn (fun p : ℝ² => p 0) T := by
  obtain ⟨D,hD,T,hTf,hTc,hTg,hTi,hTxy⟩ :=
    general_position_integer_coordinates hfin hthree hgen hint
  obtain ⟨U,hUf,hUc,hUg,hUi,hUxy,hUinj⟩ :=
    integer_coordinates_with_injective_projection hD hTf hTg hTi hTxy
  exact ⟨D,hD,U,hUf,hUc.trans hTc,hUg,hUi,hUxy,hUinj⟩

#print axioms integer_coordinates_with_injective_projection
#print axioms general_position_integer_coordinates_injective

end Erdos213.Normalization
