import Submission.CollisionMotion

/-! A restriction on quadratic motions with a three-point initial collision.
This is not a bound on arbitrary rational-distance configurations. -/
namespace Erdos213.QuadraticMotion
open Polynomial CircleLineRigidity
noncomputable section

private def nullPhase (a r : ℝ) (z v w x : ℂ) : Prop :=
  (v-x)^2-4*(w-((r : ℂ)*x+z))*(a : ℂ)=0
private def horizontalPhase (r : ℝ) (z v w x : ℂ) : Prop :=
  (v-x).im=0 ∧ (w-((r : ℂ)*x+z)).im=0

private lemma null_pair_sum (a r : ℝ) (z v w x y : ℂ) (hxy : x ≠ y)
    (hx : nullPhase a r z v w x) (hy : nullPhase a r z v w y) :
    x+y=2*v-4*(a : ℂ)*r := by
  have h : (x-y)*(x+y-2*v+4*(a : ℂ)*r)=0 := by
    dsimp [nullPhase] at hx hy
    linear_combination hx-hy
  have hh := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hxy)
  linear_combination hh

private lemma phase_mean (a r : ℝ) (z v w : ℂ) (b : Fin 3 → ℂ)
    (hb : Function.Injective b)
    (h : ∀ i, nullPhase a r z v w (b i) ∨ horizontalPhase r z v w (b i))
    (hh : ∀ i j, i ≠ j →
      ¬(horizontalPhase r z v w (b i) ∧ horizontalPhase r z v w (b j))) :
    ∃ i, horizontalPhase r z v w (b i) ∧
      3*(b i).im=(b 0).im+(b 1).im+(b 2).im := by
  have hn (i j : Fin 3) (hij : i ≠ j) (hi : horizontalPhase r z v w (b i)) :
      nullPhase a r z v w (b j) :=
    (h j).resolve_right (fun hj => hh i j hij ⟨hi,hj⟩)
  have hm (i j k : Fin 3) (hjk : j ≠ k)
      (hi : horizontalPhase r z v w (b i))
      (hj : nullPhase a r z v w (b j)) (hk : nullPhase a r z v w (b k)) :
      3*(b i).im=(b i).im+(b j).im+(b k).im := by
    have he := congrArg Complex.im (null_pair_sum a r z v w (b j) (b k)
      (hb.ne hjk) hj hk)
    simp [Complex.mul_im] at he
    have hi' := hi.1
    simp only [Complex.sub_im] at hi'
    linarith
  by_cases h0 : horizontalPhase r z v w (b 0)
  · exact ⟨0,h0,hm 0 1 2 (by decide) h0
      (hn 0 1 (by decide) h0) (hn 0 2 (by decide) h0)⟩
  by_cases h1 : horizontalPhase r z v w (b 1)
  · refine ⟨1,h1,?_⟩
    have he := hm 1 0 2 (by decide) h1
      (hn 1 0 (by decide) h1) (hn 1 2 (by decide) h1)
    linarith
  by_cases h2 : horizontalPhase r z v w (b 2)
  · refine ⟨2,h2,?_⟩
    have he := hm 2 0 1 (by decide) h2
      (hn 2 0 (by decide) h2) (hn 2 1 (by decide) h2)
    linarith
  have he01 := null_pair_sum a r z v w (b 0) (b 1) (hb.ne (by decide))
    ((h 0).resolve_right h0) ((h 1).resolve_right h1)
  have he02 := null_pair_sum a r z v w (b 0) (b 2) (hb.ne (by decide))
    ((h 0).resolve_right h0) ((h 2).resolve_right h2)
  have he : b 1=b 2 := by linear_combination he01-he02
  exact False.elim ((by decide : (1 : Fin 3) ≠ 2) (hb he))

private lemma unique_mean_index (b : Fin 3 → ℂ) (i j : Fin 3)
    (hn : cross (b 1-b 0) (b 2-b 0) ≠ 0)
    (hi : 3*(b i).im=(b 0).im+(b 1).im+(b 2).im)
    (hj : 3*(b j).im=(b 0).im+(b 1).im+(b 2).im) : i=j := by
  by_contra hne
  fin_cases i <;> fin_cases j <;> try exact hne rfl
  all_goals
    dsimp at hi hj
    have h01 : (b 1).im=(b 0).im := by linarith
    have h02 : (b 2).im=(b 0).im := by linarith
    exact hn (by simp [cross,h01,h02])

lemma motion_diff_im_zero (a d : ℝ) (v w b c : ℂ)
    (hb : (v-b).im=0) (hc : (w-c).im=0) (t : ℝ) :
    (motion a v w t-motion d b c t).im=0 := by
  have hb' : v.im=b.im := sub_eq_zero.mp (by simpa using hb)
  have hc' : w.im=c.im := sub_eq_zero.mp (by simpa using hc)
  simp [motion,pow_two,Complex.mul_im,hb',hc']

/-- A homothetically separating noncollinear triangle cannot retain two
exterior anchors on the initial real axis without a fixed collinear triple.
No distance assumption between the two anchors is needed. -/
lemma three_point_split_two_anchors (r : ℝ) (z : ℂ) (b : Fin 3 → ℂ)
    (a : Fin 2 → ℝ) (v w : Fin 2 → ℂ)
    (ha : ∀ q, a q ≠ 0) (hb : Function.Injective b)
    (hn : cross (b 1-b 0) (b 2-b 0) ≠ 0)
    (hsq : ∀ q i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a q) (v q-b i) (w q-((r : ℂ)*b i+z))))) :
    (∃ q i j, i ≠ j ∧ ∀ t : ℝ,
      cross (motion (a q) (v q) (w q) t-motion 0 (b i) ((r : ℂ)*b i+z) t)
        (motion (a q) (v q) (w q) t-motion 0 (b j) ((r : ℂ)*b j+z) t)=0) ∨
    (∃ i, ∀ t : ℝ,
      cross (motion (a 0) (v 0) (w 0) t-motion 0 (b i) ((r : ℂ)*b i+z) t)
        (motion (a 1) (v 1) (w 1) t-motion 0 (b i) ((r : ℂ)*b i+z) t)=0) := by
  classical
  have h (q : Fin 2) (i : Fin 3) :
      nullPhase (a q) r z (v q) (w q) (b i) ∨ horizontalPhase r z (v q) (w q) (b i) :=
    quadratic_type_ratFunc _ _ _ (ha q) (hsq q i)
  have him (q : Fin 2) (i : Fin 3) (hi : horizontalPhase r z (v q) (w q) (b i))
      (t : ℝ) :
      (motion (a q) (v q) (w q) t-motion 0 (b i) ((r : ℂ)*b i+z) t).im=0 :=
    motion_diff_im_zero _ _ _ _ _ _ hi.1 hi.2 t
  by_cases hp : ∃ q i j, i ≠ j ∧ horizontalPhase r z (v q) (w q) (b i) ∧
      horizontalPhase r z (v q) (w q) (b j)
  · obtain ⟨q,i,j,hij,hi,hj⟩ := hp
    exact Or.inl ⟨q,i,j,hij,fun t => by simp [cross,him q i hi t,him q j hj t]⟩
  have hh (q : Fin 2) (i j : Fin 3) (hij : i ≠ j) :
      ¬(horizontalPhase r z (v q) (w q) (b i) ∧ horizontalPhase r z (v q) (w q) (b j)) := by
    rintro ⟨hi,hj⟩
    exact hp ⟨q,i,j,hij,hi,hj⟩
  obtain ⟨i,hi,hmi⟩ := phase_mean (a 0) r z (v 0) (w 0) b hb (h 0) (hh 0)
  obtain ⟨j,hj,hmj⟩ := phase_mean (a 1) r z (v 1) (w 1) b hb (h 1) (hh 1)
  have hij := unique_mean_index b i j hn hmi hmj
  subst j
  exact Or.inr ⟨i,fun t => by simp [cross,him 0 i hi t,him 1 i hj t]⟩

/-- The two-anchor obstruction for a general three-point collision cluster
with a noncollinear first-order velocity triangle. -/
lemma collision_cluster_three_two_anchors (b c : Fin 3 → ℂ)
    (a : Fin 2 → ℝ) (v w : Fin 2 → ℂ)
    (ha : ∀ q, a q ≠ 0) (hb : Function.Injective b)
    (hn : cross (b 1-b 0) (b 2-b 0) ≠ 0)
    (hin : ∀ i j, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial 0 (b j-b i) (c j-c i))))
    (hout : ∀ q i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a q) (v q-b i) (w q-c i)))) :
    (∃ q i j, i ≠ j ∧ ∀ t : ℝ,
      cross (motion (a q) (v q) (w q) t-motion 0 (b i) (c i) t)
        (motion (a q) (v q) (w q) t-motion 0 (b j) (c j) t)=0) ∨
    (∃ i, ∀ t : ℝ,
      cross (motion (a 0) (v 0) (w 0) t-motion 0 (b i) (c i) t)
        (motion (a 1) (v 1) (w 1) t-motion 0 (b i) (c i) t)=0) := by
  obtain ⟨r,z,h⟩ := parallel_redrawing b c 0 1 2 hn
    (fun i j => collision_type _ _ (hin i j))
  have hs : ∀ q i, IsSquare (algebraMap ℝ[X] (RatFunc ℝ)
      (normPolynomial (a q) (v q-b i) (w q-((r : ℂ)*b i+z)))) := by
    intro q i
    simpa only [← h i] using hout q i
  simpa only [← h] using three_point_split_two_anchors r z b a v w ha hb hn hs

#print axioms three_point_split_two_anchors
#print axioms collision_cluster_three_two_anchors
end
end Erdos213.QuadraticMotion
