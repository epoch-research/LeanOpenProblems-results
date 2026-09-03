import Submission.CenteredColorSelectionExplore

/-! Exponential rather than only quadratic control of color kernels on a
matching. All averages are finite uniform averages. -/
namespace Erdos66MatchingColorExponential
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66DisjointMean
open scoped Classical
set_option maxHeartbeats 2500000

variable {γ : Type*} [Fintype γ] [Nonempty γ]

lemma mean_exp_centered_bounded (X : γ → ℝ) (hmean : mean X=0)
    (hX : ∀ x, |X x|≤1) (t : ℝ) (ht : |t|≤1) :
    mean (fun x ↦ Real.exp (t*X x))≤Real.exp (t^2) := by
  have hpt (x : γ) : Real.exp (t*X x)≤1+t*X x+t^2 := by
    have hx : |t*X x|≤1 := by
      rw [abs_mul]
      exact (mul_le_mul ht (hX x) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have he := Real.abs_exp_sub_one_sub_id_le hx
    have hsq : (t*X x)^2≤t^2 := by
      have hx2 : (X x)^2≤1 := by nlinarith only [sq_abs (X x),hX x,abs_nonneg (X x)]
      nlinarith only [mul_le_mul_of_nonneg_left hx2 (sq_nonneg t)]
    have he' := (le_abs_self _).trans he
    linarith
  have hm := mean_mono _ _ hpt
  simp only [mean_add,mean_const,mean_const_mul,hmean,mul_zero,add_zero] at hm
  exact hm.trans (by linarith [Real.add_one_le_exp (t^2)])

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [Nonempty α] [DecidableEq α]

omit [DecidableEq α] in
lemma matching_exp_factorization (S : Finset (ι×ι))
    (hdis : (S:Set (ι×ι)).Pairwise
      (fun e d ↦ Disjoint ({e.1,e.2}:Set ι) ({d.1,d.2}:Set ι)))
    (v : ι×ι → ℝ) (K : α → α → ℝ) (t : ℝ) :
    mean (fun ω : ι → α ↦ Real.exp (t*∑ e∈S, v e*K (ω e.1) (ω e.2)))=
      ∏ e∈S, mean (fun ω : ι → α ↦ Real.exp (t*(v e*K (ω e.1) (ω e.2)))) := by
  simp only [Finset.mul_sum,Real.exp_sum]
  apply mean_prod_of_disjoint S (fun e ↦ ({e.1,e.2}:Finset ι))
  · intro e he d hd hed
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Set.disjoint_left.mp (hdis he hd hed)
      (by simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using hi)
      (by simpa only [Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using hj)
  · intro e he
    intro x y hxy
    have h1 : x e.1=y e.1 := hxy e.1 (by simp)
    have h2 : x e.2=y e.2 := hxy e.2 (by simp)
    dsimp only
    rw [h1,h2]

/-- Bounded centered kernels on a matching satisfy a Gaussian MGF bound
for |t|<=1. No symmetry assumption is needed. -/
theorem matching_centered_mgf (S : Finset (ι×ι))
    (hne : ∀ e∈S, e.1≠e.2)
    (hdis : (S:Set (ι×ι)).Pairwise
      (fun e d ↦ Disjoint ({e.1,e.2}:Set ι) ({d.1,d.2}:Set ι)))
    (v : ι×ι → ℝ) (hv : ∀ e∈S, |v e|≤1)
    (K : α → α → ℝ) (hmean : kernelMean K=0) (hK : ∀ a b, |K a b|≤1)
    (t : ℝ) (ht : |t|≤1) :
    mean (fun ω : ι → α ↦ Real.exp (t*∑ e∈S, v e*K (ω e.1) (ω e.2)))≤
      Real.exp ((S.card:ℝ)*t^2) := by
  rw [matching_exp_factorization S hdis]
  have hpt (e : ι×ι) (he : e∈S) :
      mean (fun ω : ι → α ↦ Real.exp (t*(v e*K (ω e.1) (ω e.2))))≤Real.exp (t^2) := by
    apply mean_exp_centered_bounded
    · rw [mean_const_mul,mean_pair_kernel e.1 e.2 (hne e he),hmean,mul_zero]
    · intro ω
      rw [abs_mul]
      exact (mul_le_mul (hv e he) (hK _ _) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    · exact ht
  calc
    _ ≤ ∏ _e∈S, Real.exp (t^2) := by
      apply Finset.prod_le_prod
      · intro e he
        exact div_nonneg (Finset.sum_nonneg (fun ω _ ↦ (Real.exp_pos _).le)) (Nat.cast_nonneg _)
      · exact hpt
    _ = _ := by rw [←Real.exp_sum]; simp

end Erdos66MatchingColorExponential
