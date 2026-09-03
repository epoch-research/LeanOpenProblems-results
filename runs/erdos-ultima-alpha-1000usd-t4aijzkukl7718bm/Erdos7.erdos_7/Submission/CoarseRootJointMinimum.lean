import FormalConjecturesUtil

/-! A two-family necessary inequality on the conditioned ternary root.
This is an auxiliary comparison, not a solution of the odd-cover conjecture. -/
namespace Erdos7CoarseRootJointMinimum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Two complementary branch weights. -/
def branchValue (y : ℝ) (b : Bool) : ℝ := if b then y else 1-y

lemma branch_min_bound (t y z : ℝ) (ht : 1/3 ≤ t ∧ t ≤ 2/3)
    (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    2*(t*y+(1-t)*(1-y)+t*z+(1-t)*(1-z))-2 ≤
      t*min y z+(1-t)*min (1-y) (1-z) := by
  have hproof (y z : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
      (hyz : y ≤ z) :
      2*(t*y+(1-t)*(1-y)+t*z+(1-t)*(1-z))-2 ≤
        t*y+(1-t)*(1-z) := by
    have hA : 0 ≤ (2-3*t)*y := mul_nonneg (by linarith) hy.1
    have hB : 0 ≤ (3*t-1)*(1-z) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  rcases le_total y z with hyz | hzy
  · rw [min_eq_left hyz, min_eq_right (by linarith : 1-z ≤ 1-y)]
    exact hproof y z hy hz hyz
  · rw [min_eq_right hzy, min_eq_left (by linarith : 1-y ≤ 1-z)]
    have hh := hproof z y hz hy hzy
    nlinarith

lemma sum_branch {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (b : Ω → Bool)
    (hm : (∑ x, μ x) = 1) (t : ℝ) (ht : (∑ x, μ x * if b x then 1 else 0) = t)
    (v w : ℝ) : (∑ x, μ x * if b x then v else w) = t*v+(1-t)*w := by
  have he (x : Ω) : μ x * (if b x then v else w) =
      (μ x * if b x then 1 else 0)*v + (μ x - μ x*(if b x then 1 else 0))*w := by
    cases b x <;> simp <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,
    Finset.sum_sub_distrib,hm,ht]

/-- Shared branch geometry forces overlap even when the two families have
independently chosen branch weights and completely unrelated tails. -/
theorem joint_minimum_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (b : Ω → Bool) (t : ℝ) (ht : 1/3 ≤ t ∧ t ≤ 2/3)
    (hbt : (∑ x, μ x * if b x then 1 else 0) = t)
    (y z : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (u v : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (humean : (∑ x, μ x*u x) ≤ 1/3)
    (hvmean : (∑ x, μ x*v x) ≤ 1/3)
    (K N : Ω → ℝ)
    (hK : ∀ x, K x = 1+branchValue y (b x)+u x)
    (hN : ∀ x, N x = 1+branchValue z (b x)+v x) :
    2*((∑ x, μ x*K x)+(∑ x, μ x*N x))-22/3 ≤
      ∑ x, μ x*min (K x-1) (N x-1) := by
  have hmin (x : Ω) : min (branchValue y (b x)) (branchValue z (b x)) ≤
      min (K x-1) (N x-1) := by
    apply min_le_min <;> [rw [hK]; rw [hN]] <;> linarith [hu x,hv x]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (hmin x) (hμ x))
  have hbmin : (∑ x, μ x*min (branchValue y (b x)) (branchValue z (b x))) =
      t*min y z+(1-t)*min (1-y) (1-z) := by
    have he (x : Ω) : min (branchValue y (b x)) (branchValue z (b x)) =
        if b x then min y z else min (1-y) (1-z) := by cases b x <;> rfl
    simp_rw [he]
    exact sum_branch μ b hm t hbt _ _
  have hmeanK : (∑ x, μ x*K x) ≤ 4/3+t*y+(1-t)*(1-y) := by
    simp_rw [hK,mul_add,mul_one]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hm]
    have hh := sum_branch μ b hm t hbt y (1-y)
    change (∑ x, μ x*branchValue y (b x)) = _ at hh
    rw [hh]
    linarith
  have hmeanN : (∑ x, μ x*N x) ≤ 4/3+t*z+(1-t)*(1-z) := by
    simp_rw [hN,mul_add,mul_one]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hm]
    have hh := sum_branch μ b hm t hbt z (1-z)
    change (∑ x, μ x*branchValue z (b x)) = _ at hh
    rw [hh]
    linarith
  rw [hbmin] at hsum
  have hh := branch_min_bound t y z ht hy hz
  linarith

/-- The correction is monotone in each count, so pointwise upper bounds
on the two decompositions suffice; empty/padded patterns need not be filled. -/
lemma correction_mono (k n k' n' : ℝ) (hk : k ≤ k') (hn : n ≤ n') :
    2*(k+n)-min (k-1) (n-1) ≤ 2*(k'+n')-min (k'-1) (n'-1) := by
  simp only [min_def]
  split_ifs <;> linarith

theorem dominated_joint_minimum_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (b : Ω → Bool) (t : ℝ) (ht : 1/3 ≤ t ∧ t ≤ 2/3)
    (hbt : (∑ x, μ x * if b x then 1 else 0) = t)
    (y z : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (u v : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (humean : (∑ x, μ x*u x) ≤ 1/3)
    (hvmean : (∑ x, μ x*v x) ≤ 1/3)
    (K N : Ω → ℝ)
    (hK : ∀ x, K x ≤ 1+branchValue y (b x)+u x)
    (hN : ∀ x, N x ≤ 1+branchValue z (b x)+v x) :
    2*((∑ x, μ x*K x)+(∑ x, μ x*N x))-22/3 ≤
      ∑ x, μ x*min (K x-1) (N x-1) := by
  let K' (x : Ω) := 1+branchValue y (b x)+u x
  let N' (x : Ω) := 1+branchValue z (b x)+v x
  have hh := joint_minimum_bound μ hμ hm b t ht hbt y z hy hz u v hu hv
    humean hvmean K' N' (fun _ => rfl) (fun _ => rfl)
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (correction_mono (K x) (N x) (K' x) (N' x)
      (hK x) (hN x)) (hμ x))
  simp_rw [mul_sub, mul_add, ← mul_assoc] at hc
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hc
  have he (f : Ω → ℝ) : (∑ x, μ x*2*f x) = 2*∑ x, μ x*f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [he] at hc
  linarith

#print axioms branch_min_bound
#print axioms joint_minimum_bound
#print axioms dominated_joint_minimum_bound
end Erdos7CoarseRootJointMinimum
