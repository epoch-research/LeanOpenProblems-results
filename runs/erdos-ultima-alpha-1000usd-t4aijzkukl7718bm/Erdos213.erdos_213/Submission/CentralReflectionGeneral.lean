import Submission.CentralReflectionPairing

/-! Removing the normalization from the central reflection obstruction. -/
namespace Erdos213.CentralReflection
open CentralQuadratic
noncomputable section
set_option maxHeartbeats 4000000

lemma rationalNorm_div {z w : ℂ} (hz : RationalNorm z) (hw : RationalNorm w) :
    RationalNorm (z/w) := by
  obtain ⟨r,hr⟩ := hz
  obtain ⟨s,hs⟩ := hw
  refine ⟨r/s,?_⟩
  rw [norm_div]
  simp only [Rat.cast_div,hr,hs]

lemma point_homogeneous (a t w : ℂ) (i : Fin 7) :
    CentralQuadratic.point a (a*t) (a*w) i=a^2*points t w i := by
  fin_cases i <;> simp [CentralQuadratic.point,points] <;> ring

lemma point_normalize (a b c : ℂ) (ha : a≠0) (i : Fin 7) :
    CentralQuadratic.point a b c i=a^2*points (b/a) (c/a) i := by
  simpa only [mul_div_cancel₀ b ha,mul_div_cancel₀ c ha] using
    point_homogeneous a (b/a) (c/a) i

lemma first_parameter_ne_zero (a b c : ℂ)
    (hi : Function.Injective (CentralQuadratic.point a b c)) : a≠0 := by
  intro ha
  have he : CentralQuadratic.point a b c (3 : Fin 7)=CentralQuadratic.point a b c 6 := by
    change (a+b)*(a+c)=(a-b)*(a-c)
    rw [ha]
    ring
  exact (show (3 : Fin 7)≠6 by decide) (hi he)

/-- The fixed-singleton conclusion applies at any nonzero complex scale.
No assumption of full general position is needed for this conclusion. -/
theorem arbitrary_source_paired_singleton_fixed (a b c : ℂ)
    (ha : RationalNorm a) (hb : RationalNorm b) (hab : RationalNorm (a-b))
    (hi : Function.Injective (CentralQuadratic.point a b c))
    (σ : Equiv.Perm (Fin 7)) (C : ℂ)
    (hp : ∀ k : Fin 3,
      CentralQuadratic.point a b c (permPair σ k 0)+
      CentralQuadratic.point a b c (permPair σ k 1)=C) :
    C-CentralQuadratic.point a b c (σ 6)=CentralQuadratic.point a b c (σ 6) := by
  have ha0 := first_parameter_ne_zero a b c hi
  have ha2 : a^2≠0 := pow_ne_zero _ ha0
  have ht := rationalNorm_div hb ha
  have hs : RationalNorm (1-b/a) := by
    have he : 1-b/a=(a-b)/a := by field_simp
    rw [he]
    exact rationalNorm_div hab ha
  have hi' : Function.Injective (points (b/a) (c/a)) := by
    intro i j hij
    apply hi
    rw [point_normalize a b c ha0 i,point_normalize a b c ha0 j,hij]
  have hp' (k : Fin 3) :
      points (b/a) (c/a) (permPair σ k 0)+points (b/a) (c/a) (permPair σ k 1)=C/a^2 := by
    apply (eq_div_iff ha2).mpr
    have hh := hp k
    rw [point_normalize a b c ha0 _,point_normalize a b c ha0 _] at hh
    linear_combination hh
  have hf := paired_singleton_fixed (b/a) (c/a) ht hs hi' σ (C/a^2) hp'
  rw [point_normalize a b c ha0 (σ 6)]
  have he := congrArg (fun z : ℂ => a^2*z) hf
  simpa only [mul_sub,mul_div_cancel₀ C ha2] using he

/-- The central quadratic seven-point construction cannot be iterated by
finding a centrally paired six-point subset inside a nontrilinear output. -/
theorem arbitrary_source_nontrilinear_no_paired_six (a b c : ℂ)
    (ha : RationalNorm a) (hb : RationalNorm b) (hab : RationalNorm (a-b))
    (hi : Function.Injective (CentralQuadratic.point a b c))
    (hgp : EuclideanGeometry.NonTrilinear (Set.range (CentralQuadratic.point a b c)))
    (σ : Equiv.Perm (Fin 7)) (C : ℂ)
    (hp : ∀ k : Fin 3,
      CentralQuadratic.point a b c (permPair σ k 0)+
      CentralQuadratic.point a b c (permPair σ k 1)=C) : False := by
  have hf := arbitrary_source_paired_singleton_fixed a b c ha hb hab hi σ C hp
  have h0 := hp 0
  change CentralQuadratic.point a b c (σ 0)+CentralQuadratic.point a b c (σ 1)=C at h0
  have he : CentralQuadratic.point a b c (σ 0)+CentralQuadratic.point a b c (σ 1)=
      2*CentralQuadratic.point a b c (σ 6) := by linear_combination h0+hf
  have hne (i j : Fin 7) (hij : i≠j) :
      CentralQuadratic.point a b c (σ i)≠CentralQuadratic.point a b c (σ j) :=
    fun hh => hij (σ.injective (hi hh))
  exact hgp (Set.mem_range_self (σ 0)) (Set.mem_range_self (σ 1))
    (Set.mem_range_self (σ 6)) (hne 0 1 (by decide)) (hne 1 6 (by decide))
    (hne 0 6 (by decide)) (collinear_of_pair_sum _ _ _ he)

#print axioms rationalNorm_div
#print axioms point_normalize
#print axioms arbitrary_source_paired_singleton_fixed
#print axioms arbitrary_source_nontrilinear_no_paired_six
end
end Erdos213.CentralReflection
