import Submission.UniformColorMomentsExplore

/-! Exact quadratic moments for color kernels on disjoint unordered pairs.
The underlying sign/weight pattern is fixed before assigning the colors. -/
namespace Erdos66MatchingColorMoments
open Erdos66UniformSelection Erdos66UniformColorMoments
open scoped Classical
set_option maxHeartbeats 2200000

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [Nonempty α] [DecidableEq α]

lemma matching_pair_moment (S : Finset (ι×ι))
    (hne : ∀ e∈S, e.1≠e.2)
    (hdis : (S:Set (ι×ι)).Pairwise (fun e d ↦ Disjoint ({e.1,e.2}:Set ι) ({d.1,d.2}:Set ι)))
    (K : α → α → ℝ) (e d : ι×ι) (he : e∈S) (hd : d∈S) :
    mean (fun ω : ι → α ↦ K (ω e.1) (ω e.2)*K (ω d.1) (ω d.2)) =
      (kernelMean K)^2+
        if d=e then kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2 else 0 := by
  by_cases hde : d=e
  · subst d
    rw [if_pos rfl, add_sub_cancel]
    simp only [←pow_two]
    exact mean_pair_sq e.1 e.2 (hne e he) K
  · rw [if_neg hde,add_zero]
    rw [mean_pair_product_disjoint e.1 e.2 d.1 d.2 (hne e he) (hne d hd)
      (hdis he hd (Ne.symm hde))]
    ring

/-- A weighted sum over a matching has exactly the usual independent-pair
variance, even though its kernel is nonlinear in the two color values. -/
theorem matching_kernel_second_moment (S : Finset (ι×ι))
    (hne : ∀ e∈S, e.1≠e.2)
    (hdis : (S:Set (ι×ι)).Pairwise (fun e d ↦ Disjoint ({e.1,e.2}:Set ι) ({d.1,d.2}:Set ι)))
    (v : ι×ι → ℝ) (K : α → α → ℝ) :
    mean (fun ω : ι → α ↦ (∑ e∈S, v e*K (ω e.1) (ω e.2))^2) =
      (kernelMean K)^2*(∑ e∈S, v e)^2+
        (kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2)*(∑ e∈S, (v e)^2) := by
  have he (ω : ι → α) : (∑ e∈S, v e*K (ω e.1) (ω e.2))^2 =
      ∑ e∈S, ∑ d∈S, (v e*v d)*(K (ω e.1) (ω e.2)*K (ω d.1) (ω d.2)) := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp_rw [he]
  rw [mean_sum]
  have hrow (e : ι×ι) (he : e∈S) :
      mean (fun ω : ι → α ↦ ∑ d∈S,
        (v e*v d)*(K (ω e.1) (ω e.2)*K (ω d.1) (ω d.2))) =
      ∑ d∈S, (v e*v d)*((kernelMean K)^2+
        if d=e then kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2 else 0) := by
    rw [mean_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [mean_const_mul, matching_pair_moment S hne hdis K e d he hd]
  rw [Finset.sum_congr rfl hrow]
  simp only [mul_add, Finset.sum_add_distrib]
  have hmain : (∑ e∈S, ∑ d∈S, (v e*v d)*(kernelMean K)^2) =
      (kernelMean K)^2*(∑ e∈S, v e)^2 := by
    rw [pow_two (∑ e∈S, v e), Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hmain]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',he,if_true]
  ring

end Erdos66MatchingColorMoments
