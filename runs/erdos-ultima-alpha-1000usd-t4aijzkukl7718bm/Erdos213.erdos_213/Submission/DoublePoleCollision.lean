import Submission.DoublePoleMotion
import Submission.CollisionMotion

/-! The double-pole obstruction also covers initial collisions, as long
as the initial positions are nonzero. A collision forces a rectangular
four-position model; no distinct-initial-position assumption is needed. -/
namespace Erdos213.DoublePoleMotion
open Polynomial
noncomputable section
set_option maxHeartbeats 3000000

lemma collision_square_iff (a b d : ℝ) (ha : a ≠ 0) :
    IsSquare (squaredChord a b a d) ↔ b=d ∨ b= -d := by
  rw [chord_square_iff_numerator]
  constructor
  · intro h
    by_cases hbd : b=d
    · exact Or.inl hbd
    right
    rw [pairNorm_as_quadratic] at h
    have hh : IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
        (QuadraticMotion.normPolynomial 0
          ⟨0,-2*(a*d-a*b)⟩ ⟨a*b^2-a*d^2,0⟩)) := by simpa using h
    have hx := QuadraticMotion.collision_type _ _ hh
    change 0*0-(-2*(a*d-a*b))*(a*b^2-a*d^2)=0 at hx
    have hz : (2*a^2*(b-d)^2)*(b+d)=0 := by linear_combination -hx
    have hn : 2*a^2*(b-d)^2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha))
        (pow_ne_zero 2 (sub_ne_zero.mpr hbd))
    have hh := (mul_eq_zero.mp hz).resolve_left hn
    linarith
  · rintro (rfl | h)
    · simp [pairNorm,IsSquare]
    · have hc : a*b^2-a*d^2=0 := by rw [h]; ring
      simp only [pairNorm,hc,sub_self,C_0,zero_mul,add_zero,zero_add,
        zero_pow (by decide : (2 : ℕ) ≠ 0),map_pow]
      exact IsSquare.sq _

lemma pair_square_iff_all (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    IsSquare (squaredChord a b c d) ↔
      b=d ∨ a*d=c*b ∨ (a=c ∧ b= -d) := by
  by_cases hac : a=c
  · subst c
    rw [collision_square_iff _ _ _ ha]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨rfl,h⟩)
    · rintro (h | h | ⟨_,h⟩)
      · exact Or.inl h
      · exact Or.inl (mul_left_cancel₀ ha h).symm
      · exact Or.inr h
  · rw [pair_square_iff _ _ _ _ ha hc hac]
    simp [hac]

/-- A nontrivial collision at (a,b),(a,-b) leaves just four possible
parameter pairs for any compatible nonzero motion. -/
lemma rectangle_constraints (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₁ : b=d ∨ a*d=c*b ∨ (a=c ∧ b= -d))
    (h₂ : -b=d ∨ a*d=c*(-b) ∨ (a=c ∧ -b= -d)) :
    c^2=a^2 ∧ d^2=b^2 := by
  have hd : d=b ∨ d= -b := by
    rcases h₁ with h | h | ⟨hca,hbd⟩
    · exact Or.inl h.symm
    · rcases h₂ with h' | h' | ⟨hca,hbd⟩
      · exact Or.inr h'.symm
      · have hz : c*b=0 := by linarith
        exact False.elim ((mul_ne_zero hc hb) hz)
      · exact Or.inl (neg_injective hbd).symm
    · right
      linarith
  rcases hd with hd | hd
  · subst d
    have hca : c= -a ∨ c=a := by
      rcases h₂ with h | h | ⟨h,_⟩
      · exact False.elim (hb (by linarith))
      · left
        have hz : (c+a)*b=0 := by linear_combination h
        have hh := (mul_eq_zero.mp hz).resolve_right hb
        linarith
      · exact Or.inr h.symm
    constructor
    · rcases hca with rfl | rfl <;> ring
    · rfl
  · subst d
    have hca : c= -a ∨ c=a := by
      rcases h₁ with h | h | ⟨h,_⟩
      · exact False.elim (hb (by linarith))
      · left
        have hz : (c+a)*b=0 := by linear_combination -h
        have hh := (mul_eq_zero.mp hz).resolve_right hb
        linarith
      · exact Or.inr h.symm
    constructor
    · rcases hca with rfl | rfl <;> ring
    · ring

lemma point_origin_sq (a b t : ℝ) :
    dist (point a b t) 0 ^2 = (a/(1+b^2*t^2))^2 := by
  have hd := ne_of_gt (den_pos b t)
  rw [dist_zero_right,Complex.sq_norm,Complex.normSq_apply]
  simp only [point]
  field_simp
  ring

/-- Removing the injectivity hypothesis: universal square identities still
force a line or circle, even when distinct motions initially collide. -/
theorem motions_line_or_circle_with_collisions {ι : Type*} [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, a i ≠ 0)
    (hsq : ∀ i j, IsSquare (squaredChord (a i) (b i) (a j) (b j))) (t : ℝ) :
    Collinear ℝ (Set.range (fun i => point (a i) (b i) t)) ∨
      EuclideanGeometry.Cospherical (Set.range (fun i => point (a i) (b i) t)) := by
  have hpair (i j) := (pair_square_iff_all _ _ _ _ (ha i) (ha j)).mp (hsq i j)
  classical
  by_cases h : ∀ i j, b i=b j ∨ a i*b j=a j*b i
  · obtain ⟨B,hB⟩ | ⟨K,hK⟩ := global_compatibility a b ha h
    · left
      simp_rw [hB]
      exact common_pole_collinear a B t
    · simp_rw [hK]
      exact proportional_line_or_circle a K t
  · push_neg at h
    obtain ⟨i,j,hbij,hrij⟩ := h
    obtain ⟨haij,hbsign⟩ := ((hpair i j).resolve_left hbij).resolve_left hrij
    have hbj : b j= -b i := by linarith
    have hbi : b i ≠ 0 := by
      intro hz
      apply hbij
      rw [hbj,hz]
      ring
    have hrect (k) : (a k)^2=(a i)^2 ∧ (b k)^2=(b i)^2 := by
      refine rectangle_constraints (a i) (b i) (a k) (b k)
        (ha i) hbi (ha k) (hpair i k) ?_
      simpa only [← haij,hbj] using hpair j k
    right
    refine ⟨(0 : ℂ),|a i/(1+b i^2*t^2)|,?_⟩
    rintro _ ⟨k,rfl⟩
    apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
    rw [sq_abs,point_origin_sq,div_pow,div_pow,(hrect k).1,(hrect k).2]

#print axioms collision_square_iff
#print axioms pair_square_iff_all
#print axioms rectangle_constraints
#print axioms motions_line_or_circle_with_collisions
end
end Erdos213.DoublePoleMotion
