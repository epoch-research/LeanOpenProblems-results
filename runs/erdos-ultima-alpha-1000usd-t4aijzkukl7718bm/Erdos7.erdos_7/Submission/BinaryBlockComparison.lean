import Submission.RealChain

/-! A weighted binary two-coordinate comparison. This finite four-pattern
lemma does not assert the analogous theorem for arbitrary exponent rectangles. -/
namespace Erdos7BinaryBlockComparison
open scoped BigOperators
open Erdos7RealChain
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The point group and the row-column intersection share one upper bound.
Convexity allocates their common charge without assuming equal group weights. -/
theorem corner_majorant (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (z a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    ∃ c e : ℝ, 0 ≤ c ∧ 0 ≤ e ∧
      c+e = φ (z+a+b+d)-φ (z+a)-φ (z+b)+φ z ∧
      ∀ r s t : Bool,
        φ (z+a*bit r+b*bit s+d*bit t) ≤ φ z+
          (φ (z+a)-φ z)*bit r+(φ (z+b)-φ z)*bit s+c*bit t+e*bit r*bit s := by
  let c := max (φ (z+a+d)-φ (z+a)) (φ (z+b+d)-φ (z+b))
  let e := φ (z+a+b+d)-φ (z+a)-φ (z+b)+φ z-c
  have inc := convex_increasingIncrements φ hφ
  have hcA : φ (z+a+d)-φ (z+a) ≤ c := le_max_left _ _
  have hcB : φ (z+b+d)-φ (z+b) ≤ c := le_max_right _ _
  have hc0 : 0 ≤ c := (sub_nonneg.mpr (hmφ (by linarith : z+a ≤ z+a+d))).trans hcA
  have hcD : φ (z+d)-φ z ≤ c :=
    (inc z (z+a) d (by linarith) hd).trans hcA
  have hcAB : c ≤ φ (z+a+b+d)-φ (z+a+b) := by
    apply max_le
    · exact inc (z+a) (z+a+b) d (by linarith) hd
    · exact inc (z+b) (z+a+b) d (by linarith) hd
  have hab : 0 ≤ φ (z+a+b)-φ (z+a)-φ (z+b)+φ z := by
    have hh := inc z (z+a) b (by linarith) hb
    linarith
  have heAB : φ (z+a+b)-φ (z+a)-φ (z+b)+φ z ≤ e := by
    dsimp only [e]
    linarith
  have he0 : 0 ≤ e := hab.trans heAB
  refine ⟨c,e,hc0,he0,by dsimp [e]; ring,?_⟩
  intro r s t
  cases r <;> cases s <;> cases t <;> simp only [bit, Bool.false_eq_true, if_false,
    if_true, mul_zero, mul_one, add_zero, zero_mul]
  all_goals dsimp only [e] at * <;> linarith

noncomputable def bernoulli (s : ℝ) (b : Bool) : ℝ := if b then s else 1-s

lemma bernoulli_nonneg (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (b : Bool) :
    0 ≤ bernoulli s b := by
  cases b <;> simp only [bernoulli, Bool.false_eq_true, if_false, if_true]
  · exact sub_nonneg.mpr hs.2
  · exact hs.1

/-- Multilinear interpolation extends a Boolean corner majorant to three
normalized real group counts. -/
theorem polynomial_majorant (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (z a b d u v c e : ℝ)
    (hcorner : ∀ r s t : Bool, φ (z+a*bit r+b*bit s+d*bit t) ≤
      φ z+u*bit r+v*bit s+c*bit t+e*bit r*bit s)
    (x y w : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hw : w ∈ Set.Icc (0:ℝ) 1) :
    φ (z+a*x+b*y+d*w) ≤ φ z+u*x+v*y+c*w+e*x*y := by
  let P : Bool × Bool × Bool → ℝ := fun r =>
    bernoulli x r.1 * bernoulli y r.2.1 * bernoulli w r.2.2
  let V : Bool × Bool × Bool → ℝ := fun r =>
    z+a*bit r.1+b*bit r.2.1+d*bit r.2.2
  have hP (r : Bool × Bool × Bool) : 0 ≤ P r :=
    mul_nonneg (mul_nonneg (bernoulli_nonneg x hx r.1) (bernoulli_nonneg y hy r.2.1))
      (bernoulli_nonneg w hw r.2.2)
  have hm : (∑ r, P r) = 1 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, P, bernoulli,
      Bool.false_eq_true, if_false, if_true]
    ring
  have hv : (∑ r, P r*V r) = z+a*x+b*y+d*w := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, P, V, bernoulli, bit,
      Bool.false_eq_true, if_false, if_true]
    ring
  calc
    _ = φ (∑ r, P r*V r) := congrArg φ hv.symm
    _ ≤ ∑ r, P r*φ (V r) := by
      simpa only [smul_eq_mul] using hφ.map_sum_le
        (fun r (_ : r ∈ Finset.univ) => hP r) hm (fun r _ => Set.mem_univ (V r))
    _ ≤ ∑ r, P r*(φ z+u*bit r.1+v*bit r.2.1+c*bit r.2.2+e*bit r.1*bit r.2.1) :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_left
        (hcorner r.1 r.2.1 r.2.2) (hP r))
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, P, bernoulli, bit,
        Bool.false_eq_true, if_false, if_true]
      ring

/-- Four-pattern comparison under independent marginal caps and a joint cap.
The three real weights a,b,d may differ. No common actual extremizer is used. -/
theorem weighted_comparison {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (A B D : Ω → ℝ) (hA : ∀ x, A x ∈ Set.Icc (0:ℝ) 1)
    (hB : ∀ x, B x ∈ Set.Icc (0:ℝ) 1) (hD : ∀ x, D x ∈ Set.Icc (0:ℝ) 1)
    (m r s t : ℝ) (hm : (∑ x, μ x) = m)
    (hr : (∑ x, μ x*A x) ≤ r) (hs : (∑ x, μ x*B x) ≤ s)
    (ht : (∑ x, μ x*D x) ≤ t) (htAB : (∑ x, μ x*A x*B x) ≤ t)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (z a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    (∑ x, μ x*φ (z+a*A x+b*B x+d*D x)) ≤
      (m-r-s+t)*φ z+(r-t)*φ (z+a)+(s-t)*φ (z+b)+t*φ (z+a+b+d) := by
  obtain ⟨c,e,hc,he,hce,hcorner⟩ := corner_majorant φ hφ hmφ z a b d ha hb hd
  have hu : 0 ≤ φ (z+a)-φ z := sub_nonneg.mpr (hmφ (by linarith))
  have hv : 0 ≤ φ (z+b)-φ z := sub_nonneg.mpr (hmφ (by linarith))
  have hpoint (x : Ω) := polynomial_majorant φ hφ z a b d
    (φ (z+a)-φ z) (φ (z+b)-φ z) c e hcorner (A x) (B x) (D x) (hA x) (hB x) (hD x)
  have hp := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint x) (hμ x))
  have hexp : (∑ x, μ x*(φ z+(φ (z+a)-φ z)*A x+(φ (z+b)-φ z)*B x+c*D x+e*A x*B x)) =
      m*φ z+(φ (z+a)-φ z)*(∑ x, μ x*A x)+(φ (z+b)-φ z)*(∑ x, μ x*B x)+
        c*(∑ x, μ x*D x)+e*(∑ x, μ x*A x*B x) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hm]
    simp_rw [Finset.mul_sum]
    congr 1
    · congr 1
      · congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intro x _
          ring
        · apply Finset.sum_congr rfl
          intro x _
          ring
      · apply Finset.sum_congr rfl
        intro x _
        ring
    · apply Finset.sum_congr rfl
      intro x _
      ring
  rw [hexp] at hp
  have h₁ := mul_le_mul_of_nonneg_left hr hu
  have h₂ := mul_le_mul_of_nonneg_left hs hv
  have h₃ := mul_le_mul_of_nonneg_left ht hc
  have h₄ := mul_le_mul_of_nonneg_left htAB he
  calc
    _ ≤ m*φ z+(φ (z+a)-φ z)*r+(φ (z+b)-φ z)*s+c*t+e*t := by linarith
    _ = _ := by
      have hh := congrArg (fun x : ℝ => x*t) hce
      nlinarith

lemma coefficients_nonneg (m r s t : ℝ) (ht0 : 0 ≤ t) (htr : t ≤ r) (hts : t ≤ s)
    (hm : r+s-t ≤ m) :
    0 ≤ m-r-s+t ∧ 0 ≤ r-t ∧ 0 ≤ s-t ∧ 0 ≤ t := by
  exact ⟨by linarith, sub_nonneg.mpr htr, sub_nonneg.mpr hts, ht0⟩

#print axioms weighted_comparison
#print axioms polynomial_majorant
end Erdos7BinaryBlockComparison
