import Submission.FixedTriangleExtensions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Finiteness of integral-distance extensions of any fixed noncollinear
triangle, including points on the anchor lines. This does not give a bound
independent of the triangle and does not settle the finite Erdős conjecture. -/

namespace Erdos213.ErdosAnning
open FixedTriangleExtensions
set_option maxHeartbeats 3000000

lemma coefficients_not_both_zero {a b c k l : ℝ}
    (hb : 0 < b) (hH : 0 < heron a b c) :
    ¬ (qa a b c k l = 0 ∧ qc a b c k l = 0) := by
  rintro ⟨hqa,hqc⟩
  have hid : 4*b^2*qc a b c k l =
      (2*b^2*(a^2-k^2)-(a^2+b^2-c^2)*(b^2-l^2))^2 +
      heron a b c*(b^2-l^2)^2 := by simp only [qc,heron]; ring
  have hprod : heron a b c*(b^2-l^2)^2 = 0 := by
    rw [hqc] at hid
    nlinarith [sq_nonneg (2*b^2*(a^2-k^2)-(a^2+b^2-c^2)*(b^2-l^2)),
      mul_nonneg (le_of_lt hH) (sq_nonneg (b^2-l^2))]
  have hV : b^2-l^2 = 0 := by
    have hsq := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hH)
    nlinarith [sq_nonneg (b^2-l^2)]
  have hU : a^2-k^2 = 0 := by
    rw [hqc,hV] at hid
    have hh : (2*b^2*(a^2-k^2))^2 = 0 := by nlinarith [hid]
    have hz : 2*b^2*(a^2-k^2) = 0 := by nlinarith [hh]
    exact (mul_eq_zero.mp hz).resolve_left (by positivity)
  have hk : k^2=a^2 := by linarith
  have hl : l^2=b^2 := by linarith
  have hid2 : qa a b c k l = (a^2+b^2-c^2-2*k*l)^2 := by
    unfold qa heron
    nlinarith [hk,hl,show k^2*l^2=a^2*b^2 by rw [hk,hl]]
  have hh : a^2+b^2-c^2 = 2*k*l := by rw [hqa] at hid2; nlinarith
  unfold heron at hH
  rw [hh] at hH
  nlinarith [show k^2*l^2=a^2*b^2 by rw [hk,hl]]

lemma radiusPolynomial_ne_zero {a b c k l : ℝ}
    (hb : 0 < b) (hH : 0 < heron a b c) :
    radiusPolynomial a b c k l ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  have h1 := congrArg (Polynomial.eval 1) h
  have hm := congrArg (Polynomial.eval (-1)) h
  norm_num [radiusPolynomial] at h0 h1 hm
  exact coefficients_not_both_zero hb hH ⟨by linarith, h0⟩

/-- No exclusions of collinear triples or of boundary differences are needed. -/
lemma finite_fiber_all {a : ℝ} {z : ℂ} (ha : a ≠ 0) (hz : z.im ≠ 0) (k l : ℤ) :
    Set.Finite {p : ℂ | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧
      dist p z=‖p‖+(l : ℝ)} := by
  have hb : 0 < ‖z‖ := norm_pos_iff.mpr (fun he => hz (by simp [he]))
  have hH : 0 < heron a ‖z‖ (dist z (a : ℂ)) := by
    have h1 := Complex.sq_norm z
    rw [Complex.normSq_apply] at h1
    have h2 := complex_dist_sq z (a : ℂ)
    simp only [Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h2
    rw [heron_of_coordinates (by nlinarith only [h1]) h2.symm]
    positivity
  have hp := radiusPolynomial_ne_zero (k := (k : ℝ)) (l := (l : ℝ)) hb hH
  apply Set.Finite.of_finite_image (f := fun p : ℂ => ‖p‖)
  · apply (Polynomial.finite_setOf_isRoot hp).subset
    rintro r ⟨p,hp,rfl⟩
    change (radiusPolynomial a ‖z‖ (dist z (a : ℂ)) k l).eval ‖p‖=0
    simp only [radiusPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    exact complex_radius_equation rfl rfl rfl hp.1 hp.2
  · exact norm_injective_on_fiber ha hz

/-- Fixing the two distance differences leaves at most two possible points. -/
lemma fiber_ncard_le_two {a : ℝ} {z : ℂ} (ha : a ≠ 0) (hz : z.im ≠ 0) (k l : ℤ) :
    {p : ℂ | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧
      dist p z=‖p‖+(l : ℝ)}.ncard ≤ 2 := by
  classical
  let F : Set ℂ := {p | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧
    dist p z=‖p‖+(l : ℝ)}
  have hF : F.Finite := finite_fiber_all ha hz k l
  let R : Set ℝ := (fun p : ℂ => ‖p‖) '' F
  have hR : R.Finite := hF.image _
  have hb : 0 < ‖z‖ := norm_pos_iff.mpr (fun he => hz (by simp [he]))
  have hH : 0 < heron a ‖z‖ (dist z (a : ℂ)) := by
    have h1 := Complex.sq_norm z
    rw [Complex.normSq_apply] at h1
    have h2 := complex_dist_sq z (a : ℂ)
    simp only [Complex.ofReal_re,Complex.ofReal_im,sub_zero] at h2
    rw [heron_of_coordinates (by nlinarith only [h1]) h2.symm]
    positivity
  let P := radiusPolynomial a ‖z‖ (dist z (a : ℂ)) k l
  have hP : P ≠ 0 := radiusPolynomial_ne_zero hb hH
  have hsub : hR.toFinset.val ⊆ P.roots := by
    intro r hr
    have hr' : r ∈ R := hR.mem_toFinset.mp hr
    obtain ⟨p,hp,rfl⟩ := hr'
    apply (Polynomial.mem_roots hP).mpr
    change (radiusPolynomial a ‖z‖ (dist z (a : ℂ)) k l).eval ‖p‖=0
    simp only [radiusPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    exact complex_radius_equation rfl rfl rfl hp.1 hp.2
  have hcard : R.ncard ≤ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hR]
    exact (Polynomial.card_le_degree_of_subset_roots hsub).trans Polynomial.natDegree_quadratic_le
  change F.ncard ≤ 2
  have he : R.ncard=F.ncard := Set.ncard_image_of_injOn (norm_injective_on_fiber ha hz)
  rwa [← he]

/-- The zero-constant boundary fiber is genuine, but its polynomial is nonzero. -/
lemma boundary_control : qc (3 : ℝ) 4 5 3 4=0 ∧ qa (3 : ℝ) 4 5 3 4=576 ∧
    radiusPolynomial 3 4 5 3 4 = Polynomial.C (576 : ℝ)*Polynomial.X^2 := by
  norm_num [qc,qa,qb,heron,radiusPolynomial]

/-- The three anchors need not themselves have integer mutual distances. -/
theorem normalized_extensions_finite {a : ℝ} {z : ℂ} (ha : a ≠ 0) (hz : z.im ≠ 0) :
    Set.Finite {p : ℂ |
      dist p 0 ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p (a : ℂ) ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p z ∈ Set.range ((↑) : ℤ → ℝ)} := by
  obtain ⟨M,hM⟩ := exists_nat_gt |a|
  obtain ⟨N,hN⟩ := exists_nat_gt ‖z‖
  let K : Finset ℤ := Finset.Icc (-(M : ℤ)) M
  let L : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let F (k l : ℤ) : Set ℂ :=
    {p | dist p (a : ℂ)=‖p‖+(k : ℝ) ∧ dist p z=‖p‖+(l : ℝ)}
  have hf : Set.Finite (⋃ k∈(K : Set ℤ), ⋃ l∈(L : Set ℤ), F k l) := by
    apply K.finite_toSet.biUnion
    intro k hk
    apply L.finite_toSet.biUnion
    intro l hl
    exact finite_fiber_all ha hz k l
  apply hf.subset
  rintro p ⟨⟨r,hr⟩,⟨s,hs⟩,⟨t,ht⟩⟩
  have hka := abs_dist_sub_le (a : ℂ) 0 p
  have hlz := abs_dist_sub_le z 0 p
  rw [dist_comm (a : ℂ) p,dist_comm 0 p,← hs,← hr] at hka
  rw [dist_comm z p,dist_comm 0 p,← ht,← hr] at hlz
  simp only [dist_zero_right,Complex.norm_real,Real.norm_eq_abs] at hka
  simp only [dist_zero_right] at hlz
  have hk : s-r ∈ (K : Set ℤ) := by
    change s-r ∈ Finset.Icc (-(M : ℤ)) M
    apply Finset.mem_Icc.mpr
    have hh : |(s : ℝ)-r| ≤ (M : ℝ) := le_trans hka (le_of_lt hM)
    exact_mod_cast (abs_le.mp hh)
  have hl : t-r ∈ (L : Set ℤ) := by
    change t-r ∈ Finset.Icc (-(N : ℤ)) N
    apply Finset.mem_Icc.mpr
    have hh : |(t : ℝ)-r| ≤ (N : ℝ) := le_trans hlz (le_of_lt hN)
    exact_mod_cast (abs_le.mp hh)
  apply Set.mem_iUnion.mpr ⟨s-r,?_⟩
  apply Set.mem_iUnion.mpr ⟨hk,?_⟩
  apply Set.mem_iUnion.mpr ⟨t-r,?_⟩
  apply Set.mem_iUnion.mpr ⟨hl,?_⟩
  change dist p (a : ℂ)=‖p‖+((s-r : ℤ) : ℝ) ∧
    dist p z=‖p‖+((t-r : ℤ) : ℝ)
  have hr' : ‖p‖=(r : ℝ) := by simpa only [dist_zero_right] using hr.symm
  rw [hr',Int.cast_sub,Int.cast_sub]
  constructor <;> linarith

lemma ratio_representation {A B C : ℂ}
    (hAB : B-A ≠ 0) (hC : ((C-A)/(B-A)).im = 0) :
    C = ((C-A)/(B-A)).re • (B-A) +ᵥ A := by
  have hh : (((C-A)/(B-A)).re : ℂ) = (C-A)/(B-A) := by
    apply Complex.ext <;> simp [hC]
  simp only [vadd_eq_add,Complex.real_smul,hh]
  rw [div_mul_cancel₀ _ hAB]
  abel

lemma collinear_of_ratio_im_zero {A B C : ℂ}
    (hAB : B-A ≠ 0) (hC : ((C-A)/(B-A)).im = 0) :
    Collinear ℝ ({A,B,C} : Set ℂ) := by
  rw [collinear_iff_of_mem (by simp : A ∈ ({A,B,C} : Set ℂ))]
  refine ⟨B-A,?_⟩
  rintro p (rfl | rfl | rfl)
  · exact ⟨0,by simp⟩
  · exact ⟨1,by simp⟩
  · exact ⟨((p-A)/(B-A)).re,ratio_representation hAB hC⟩

/-- A unit-modulus change of complex coordinates, without any scale change. -/
noncomputable def normalize (A B p : ℂ) : ℂ :=
  (p-A)/((B-A)/(‖B-A‖ : ℂ))

lemma normalize_distance {A B : ℂ} (hAB : B-A ≠ 0) (p q : ℂ) :
    dist (normalize A B p) (normalize A B q) = dist p q := by
  have hu : ‖(B-A)/(‖B-A‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hAB)
  rw [dist_eq_norm,dist_eq_norm]
  unfold normalize
  rw [← sub_div,norm_div,hu,div_one]
  congr 1
  abel

lemma normalize_left (A B : ℂ) : normalize A B A = 0 := by simp [normalize]

lemma normalize_right {A B : ℂ} (hAB : B-A ≠ 0) :
    normalize A B B = (‖B-A‖ : ℂ) := by
  unfold normalize
  rw [div_div_eq_mul_div]
  field_simp

lemma normalize_im_ne_zero {A B C : ℂ} (hAB : B-A ≠ 0)
    (hC : ((C-A)/(B-A)).im ≠ 0) : (normalize A B C).im ≠ 0 := by
  have he : normalize A B C = (‖B-A‖ : ℂ)*((C-A)/(B-A)) := by
    unfold normalize
    rw [div_div_eq_mul_div]
    ring
  rw [he,Complex.mul_im]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  exact mul_ne_zero (norm_ne_zero_iff.mpr hAB) hC

theorem extensions_finite_of_ratio {A B C : ℂ}
    (hAB : B-A ≠ 0) (hC : ((C-A)/(B-A)).im ≠ 0) :
    Set.Finite {p : ℂ |
      dist p A ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p B ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p C ∈ Set.range ((↑) : ℤ → ℝ)} := by
  have hf := normalized_extensions_finite (a := ‖B-A‖)
    (norm_ne_zero_iff.mpr hAB) (normalize_im_ne_zero hAB hC)
  apply Set.Finite.of_finite_image (f := normalize A B)
  · apply hf.subset
    rintro p ⟨q,hq,rfl⟩
    change dist (normalize A B q) 0 ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist (normalize A B q) (‖B-A‖ : ℂ) ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist (normalize A B q) (normalize A B C) ∈ Set.range ((↑) : ℤ → ℝ)
    rw [← normalize_left A B,← normalize_right hAB]
    simpa only [normalize_distance hAB] using hq
  · intro p hp q hq he
    have hh := normalize_distance hAB p q
    rw [he,dist_self] at hh
    exact dist_eq_zero.mp hh.symm

/-- Finitely many common integral-distance points for any fixed noncollinear
triangle. There is no fixed diameter assumption or excluded anchor line. -/
theorem extensions_finite {A B C : ℂ}
    (h : ¬ Collinear ℝ ({A,B,C} : Set ℂ)) :
    Set.Finite {p : ℂ |
      dist p A ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p B ∈ Set.range ((↑) : ℤ → ℝ) ∧
      dist p C ∈ Set.range ((↑) : ℤ → ℝ)} := by
  have hAB : B-A ≠ 0 := sub_ne_zero.mpr (ne₁₂_of_not_collinear h).symm
  exact extensions_finite_of_ratio hAB (fun hz => h (collinear_of_ratio_im_zero hAB hz))

lemma integral_distance_of_mem {S : Set ℂ}
    (hd : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)))
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) :
    dist p q ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_cases he : p=q
  · subst q
    exact ⟨0,by simp⟩
  · exact hd hp hq he

/-- A fixed noncollinear triangle imposes one finite bound on every integral
configuration containing it. The bound is allowed to depend on the triangle. -/
theorem fixed_triangle_bound {A B C : ℂ}
    (h : ¬ Collinear ℝ ({A,B,C} : Set ℂ)) :
    ∃ N : ℕ, ∀ S : Set ℂ, A ∈ S → B ∈ S → C ∈ S →
      S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) →
      S.Finite ∧ S.ncard ≤ N := by
  let E : Set ℂ := {p | dist p A ∈ Set.range ((↑) : ℤ → ℝ) ∧
    dist p B ∈ Set.range ((↑) : ℤ → ℝ) ∧ dist p C ∈ Set.range ((↑) : ℤ → ℝ)}
  have hf : E.Finite := extensions_finite h
  refine ⟨E.ncard,?_⟩
  intro S hA hB hC hd
  have hs : S ⊆ E := by
    intro p hp
    exact ⟨integral_distance_of_mem hd hp hA,integral_distance_of_mem hd hp hB,
      integral_distance_of_mem hd hp hC⟩
  exact ⟨hf.subset hs,Set.ncard_le_ncard hs hf⟩

/-- Erdős--Anning: an infinite integral-distance subset of the complex plane
is collinear. The fixed-anchor finiteness proof includes all boundary cases. -/
theorem infinite_integral_collinear {S : Set ℂ} (hS : S.Infinite)
    (hd : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ))) :
    Collinear ℝ S := by
  classical
  obtain ⟨A,hA,B,hB,hAB⟩ := hS.nontrivial
  have hn : B-A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hr : ∀ C ∈ S, ((C-A)/(B-A)).im = 0 := by
    intro C hC
    by_contra h
    apply hS
    apply (extensions_finite_of_ratio hn h).subset
    intro p hp
    exact ⟨integral_distance_of_mem hd hp hA,integral_distance_of_mem hd hp hB,
      integral_distance_of_mem hd hp hC⟩
  rw [collinear_iff_of_mem hA]
  refine ⟨B-A,?_⟩
  intro C hC
  exact ⟨((C-A)/(B-A)).re,ratio_representation hn (hr C hC)⟩

/-- The same statement for the Euclidean plane used in the conjecture. -/
theorem infinite_integral_plane_collinear {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : S.Infinite)
    (hd : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ))) :
    Collinear ℝ S := by
  let e := Complex.orthonormalBasisOneI.repr
  have hT : (e.symm '' S).Infinite := hS.image e.symm.injective.injOn
  have hTd : (e.symm '' S).Pairwise
      (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ)) := by
    rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ hpq
    rw [e.symm.dist_map]
    exact hd hp hq (fun he => hpq (he ▸ rfl))
  have hc := infinite_integral_collinear hT hTd
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc ⊢
  obtain ⟨o,v,hv⟩ := hc
  refine ⟨e o,e v,?_⟩
  intro p hp
  obtain ⟨r,hr⟩ := hv (e.symm p) ⟨p,hp,rfl⟩
  refine ⟨r,?_⟩
  have he := congrArg e hr
  simpa only [vadd_eq_add,map_add,map_smul,e.apply_symm_apply] using he

/-- This dichotomy is not a uniform cardinality bound on its finite branch. -/
theorem finite_or_collinear {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hd : S.Pairwise (fun p q => dist p q ∈ Set.range ((↑) : ℤ → ℝ))) :
    S.Finite ∨ Collinear ℝ S := by
  classical
  by_cases hs : S.Finite
  · exact Or.inl hs
  · exact Or.inr (infinite_integral_plane_collinear hs hd)

#print axioms coefficients_not_both_zero
#print axioms radiusPolynomial_ne_zero
#print axioms finite_fiber_all
#print axioms fiber_ncard_le_two
#print axioms boundary_control
#print axioms normalized_extensions_finite
#print axioms extensions_finite
#print axioms fixed_triangle_bound
#print axioms infinite_integral_collinear
#print axioms infinite_integral_plane_collinear
#print axioms finite_or_collinear
end Erdos213.ErdosAnning
