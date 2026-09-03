import Submission.FiniteHingeComparison
import Submission.FiniteHingeFunctions

/-! Integer-hinge comparison for bounded real counts. Unlike a count of
individual boxes, a normalized family average need not be integer-valued. -/
namespace Erdos7RealHingeComparison
open scoped BigOperators
open Erdos7FiniteHingeComparison
set_option maxHeartbeats 2000000
set_option autoImplicit false

noncomputable def linearExtension (f : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  f 0 + (f 1 - f 0) * x +
    ∑ t ∈ Finset.range N, curvature f t * max 0 (x - (t + 1))

lemma nat_hinge_eq (n k : ℕ) : ((n-k : ℕ) : ℝ) = max 0 ((n : ℝ) - k) := by
  by_cases h : k ≤ n
  · rw [Nat.cast_sub h, max_eq_right (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero,
      max_eq_left (sub_nonpos.mpr (by exact_mod_cast (show n ≤ k by omega)))]

lemma linearExtension_nat (f : ℕ → ℝ) (N n : ℕ) (hn : n ≤ N) :
    linearExtension f N n = f n := by
  rw [hinge_expansion f N n hn]
  unfold linearExtension
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [nat_hinge_eq]
  simp

lemma linearExtension_cell (f : ℕ → ℝ) (N j : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    linearExtension f N (a*j+b*(j+1)) =
      a*linearExtension f N j+b*linearExtension f N (j+1) := by
  have he (t : ℕ) :
      max 0 (a*j+b*(j+1)-(t+1)) =
        a*max 0 ((j:ℝ)-(t+1))+b*max 0 ((j:ℝ)+1-(t+1)) := by
    apply Erdos7FiniteHingeFunctions.hinge_on_segment (t+1) j (j+1) a b ha hb hab
    by_cases ht : t < j
    · left
      have hh : (t : ℝ) + 1 ≤ j := by exact_mod_cast ht
      exact ⟨hh, by linarith⟩
    · right
      have hh : (j : ℝ) ≤ t := by exact_mod_cast (Nat.le_of_not_gt ht)
      exact ⟨by linarith, by linarith⟩
  unfold linearExtension
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  have hsum₁ : (∑ t ∈ Finset.range N, curvature f t*(a*max 0 ((j:ℝ)-(t+1)))) =
      a*(∑ t ∈ Finset.range N, curvature f t*max 0 ((j:ℝ)-(t+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hsum₂ : (∑ t ∈ Finset.range N, curvature f t*(b*max 0 ((j:ℝ)+1-(t+1)))) =
      b*(∑ t ∈ Finset.range N, curvature f t*max 0 ((j:ℝ)+1-(t+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hsum₁, hsum₂]
  have hh : (a+b)*f 0=f 0 := by rw [hab, one_mul]
  nlinarith

/-- A convex function lies below its piecewise-linear interpolation on an
integer grid. The argument is valid at every real point of the interval. -/
theorem convex_below_linearExtension (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxN : x ≤ N) :
    φ x ≤ linearExtension (fun n => φ n) N x := by
  by_cases hN : N=0
  · subst N
    have he : x=0 := by simp only [Nat.cast_zero] at hxN; linarith
    subst x
    simp [linearExtension]
  · obtain ⟨j, hj, hxj⟩ := Erdos7FiniteHingeFunctions.exists_unit_interval N (by omega)
      (x+1) (by linarith) (by linarith)
    have hcell : x ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
      obtain ⟨h₁,h₂⟩ := hxj
      exact ⟨by linarith, by linarith⟩
    obtain ⟨a,b,ha,hb,hab,he⟩ := Erdos7FiniteHingeFunctions.interval_combination
      (j:ℝ) ((j:ℝ)+1) x hcell
    rw [he]
    apply Erdos7FiniteHingeFunctions.convex_below_affine_cell φ
      (linearExtension (fun n => φ n) N) hφ j (j+1) a b ha hb hab
      (linearExtension_cell _ N j a b ha hb hab)
    · rw [linearExtension_nat _ N j (by omega)]
    · have hh := linearExtension_nat (fun n => φ n) N (j+1) (by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using hh.ge

lemma sum_linearExtension {A : Type*} [Fintype A]
  (f : ℕ → ℝ) (N : ℕ) (ρ : A → ℝ) (V : A → ℝ) :
    (∑ x, ρ x*linearExtension f N (V x)) =
      (∑ x, ρ x)*f 0+(f 1-f 0)*(∑ x, ρ x*V x)+
        ∑ t ∈ Finset.range N, curvature f t*(∑ x, ρ x*max 0 (V x-(t+1))) := by
  unfold linearExtension
  simp_rw [mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro x _
    ring

/-- Real counts may be tested against integer hinge thresholds, provided the
reference law is supported on that integer grid. -/
theorem real_integer_hinge_comparison {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : Ω → ℝ) (ν : Ξ → ℝ) (X : Ω → ℝ) (Y : Ξ → ℕ) (N : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ z, 0 ≤ ν z)
    (hX : ∀ x, X x ∈ Set.Icc (0:ℝ) (N:ℝ)) (hY : ∀ z, Y z ≤ N)
    (hmass : (∑ x, μ x) = ∑ z, ν z)
    (hmean : (∑ x, μ x*X x) ≤ ∑ z, ν z*(Y z : ℝ))
    (hhinge : ∀ t<N, (∑ x, μ x*max 0 (X x-(t+1))) ≤
      ∑ z, ν z*max 0 ((Y z : ℝ)-(t+1)))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, μ x*φ (X x)) ≤ ∑ z, ν z*φ (Y z) := by
  let f : ℕ → ℝ := fun n => φ n
  have hf : 0 ≤ f 1-f 0 := sub_nonneg.mpr (hmφ (by norm_num))
  have hc (t : ℕ) : 0 ≤ curvature f t := by
    simpa only [zero_add] using convex_nat_curvature φ hφ 0 t

  calc
    _ ≤ ∑ x, μ x*linearExtension f N (X x) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
        (convex_below_linearExtension φ hφ N (X x) (hX x).1 (hX x).2) (hμ x))
    _ ≤ ∑ z, ν z*linearExtension f N (Y z) := by
      rw [sum_linearExtension f N μ X, sum_linearExtension f N ν (fun z => (Y z : ℝ)), hmass]
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean hf)
      · exact Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left
          (hhinge t (Finset.mem_range.mp ht)) (hc t))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [linearExtension_nat f N (Y z) (hY z)]

#print axioms convex_below_linearExtension
#print axioms real_integer_hinge_comparison
end Erdos7RealHingeComparison
