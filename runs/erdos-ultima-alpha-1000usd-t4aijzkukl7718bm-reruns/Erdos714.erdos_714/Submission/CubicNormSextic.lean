import Submission.CubicNormFiveStandalone

/-!
A nonzero sextic eliminant for three cubic norm spheres. This proves an
upper bound of SIX common points, not the THREE needed for K44-freeness.
All exceptional denominators in the elimination are accounted for.
-/
noncomputable section
open Classical Polynomial Finset
set_option maxHeartbeats 4000000
namespace Erdos714CubicSextic
open Erdos714CubicSegre (norm norm_mul norm_div norm_ne_zero)
variable {E : Type*} [Field E]

/-- The middle coefficient in the first quadratic after eliminating the third variable. -/
def middle (a b : E) : E[X] := (X+1)*(X+C a)-C b*X

/-- The coefficient of the second conjugate after eliminating its square. -/
def line (u v w a b c : E) : E[X] :=
  (X+1)*(X+C u)*(C (w*(v-1))*X+C (a*(1-w)))-C c*X*(X+1)+C (w*b)*X*(X+C u)

/-- The residual polynomial after the two quadratic equations are combined. -/
def sextic (u v w a b c : E) : E[X] :=
  (line u v w a b c)^2-C (v-w)*(X+C u)*middle a b*line u v w a b c+
    C (a*(v-w)^2)*X*(X+1)^2*(X+C u)^2

lemma degree_le (u v w a b c : E) : (sextic u v w a b c).natDegree ≤ 6 := by
  unfold sextic line middle
  compute_degree!

/-- Evaluating at a pole of the original substitution proves nonvanishing
without an unproved claim about a generic leading coefficient. -/
lemma eval_neg_u (u v w a b c : E) :
    (sextic u v w a b c).eval (-u) = c^2*u^2*(u-1)^2 := by
  simp [sextic,line,middle]
  ring

lemma ne_zero (u v w a b c : E) (hu : u ≠ 0) (hu₁ : u ≠ 1) (hc : c ≠ 0) :
    sextic u v w a b c ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.eval (-u)) hz
  rw [eval_neg_u,eval_zero] at he
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hu))
    (pow_ne_zero 2 (sub_ne_zero.mpr hu₁)) he

/-- Pure algebraic elimination, with both cancelled factors explicit. -/
theorem root_of_quadratics (u v w a b c x y : E) (ha : a ≠ 0) (hx : x+1 ≠ 0)
    (hf : (x+1)*(y+1)*(x*y+a)-b*x*y = 0)
    (hg : (x+u)*(y+v)*(w*x*y+a)-c*x*y = 0) :
    (sextic u v w a b c).eval x = 0 := by
  let L := (line u v w a b c).eval x
  let M := a*(v-w)*(x+1)*(x+u)
  let Q := (middle a b).eval x
  have hL : L*y+M = 0 := by
    dsimp [L,M,line]
    simp only [eval_add,eval_sub,eval_mul,eval_C,eval_X,eval_one]
    linear_combination (x+1)*hg-w*(x+u)*hf
  apply (mul_eq_zero.mp (show a*(x+1)*(sextic u v w a b c).eval x = 0 from ?_)).resolve_left
    (mul_ne_zero ha hx)
  have hid : (sextic u v w a b c).eval x =
      L^2-(v-w)*(x+u)*Q*L+a*(v-w)^2*x*(x+1)^2*(x+u)^2 := by
    simp [sextic,L,Q]
  rw [hid]
  dsimp [Q,M] at hL ⊢
  simp only [middle,eval_mul,eval_add,eval_sub,eval_C,eval_X,eval_one] at hL ⊢
  linear_combination L^2*hf-
    (x*(x+1)*(L*y-a*(v-w)*(x+1)*(x+u))+((x+1)*(x+a)-b*x)*L)*hL

/-- The actual norm equations imply the two quadratics, without dividing by
any conjugate coordinate. The needed nonzero factor follows from b!=0. -/
theorem norm_root (σ : E →+* E) (u a b c x : E) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : norm σ x = a) (h₁ : norm σ (x+1) = b) (h₂ : norm σ (x+u) = c) :
    (sextic u (σ u) (σ (σ u)) a b c).eval x = 0 := by
  have hx : x+1 ≠ 0 := by
    intro he
    rw [he] at h₁
    exact hb (by simpa [Erdos714CubicSegre.norm] using h₁.symm)
  apply root_of_quadratics u (σ u) (σ (σ u)) a b c x (σ x) ha hx
  · simp only [Erdos714CubicSegre.norm,map_add,map_one] at h₀ h₁
    linear_combination x*σ x*h₁-(x+1)*(σ x+1)*h₀
  · simp only [Erdos714CubicSegre.norm,map_add] at h₀ h₂
    linear_combination x*σ x*h₂-(x+u)*(σ x+σ u)*h₀

/-- Three nonzero norm values at three distinct affine shifts have at most
six solutions, uniformly in all coefficients and in the characteristic. -/
theorem fiber_card_le_six (σ : E →+* E) (u a b c : E)
    (hu : u ≠ 0) (hu₁ : u ≠ 1) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, norm σ x = a ∧ norm σ (x+1) = b ∧ norm σ (x+u) = c) :
    S.card ≤ 6 := by
  have hp := ne_zero u (σ u) (σ (σ u)) a b c hu hu₁ hc
  have hs : S ⊆ (sextic u (σ u) (σ (σ u)) a b c).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hp]
    obtain ⟨h₀,h₁,h₂⟩ := hS x hx
    exact norm_root σ u a b c x ha hb h₀ h₁ h₂
  exact (Finset.card_le_card hs).trans <| (Multiset.toFinset_card_le _).trans <|
    (Polynomial.card_roots' _).trans (degree_le _ _ _ _ _ _)

/-- When the shift is fixed, the sextic is a square and the fiber has at most
three points. This exceptional improvement is NOT asserted for other shifts. -/
theorem fixed_fiber_card_le_three (σ : E →+* E) (u a b c : E)
    (hfix : σ u = u) (hu : u ≠ 0) (hu₁ : u ≠ 1)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, norm σ x = a ∧ norm σ (x+1) = b ∧ norm σ (x+u) = c) :
    S.card ≤ 3 := by
  have hp : line u u u a b c ≠ 0 := by
    intro hz
    have hs := ne_zero u u u a b c hu hu₁ hc
    apply hs
    simp [sextic,hz]
  have hd : (line u u u a b c).natDegree ≤ 3 := by unfold line; compute_degree!
  have hs : S ⊆ (line u u u a b c).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset,Polynomial.mem_roots hp]
    obtain ⟨h₀,h₁,h₂⟩ := hS x hx
    have hr := norm_root σ u a b c x ha hb h₀ h₁ h₂
    rw [hfix,hfix] at hr
    simpa [sextic] using hr
  exact (Finset.card_le_card hs).trans <| (Multiset.toFinset_card_le _).trans <|
    (Polynomial.card_roots' _).trans hd

#print axioms root_of_quadratics
#print axioms norm_root
#print axioms fiber_card_le_six
#print axioms fixed_fiber_card_le_three
end Erdos714CubicSextic
