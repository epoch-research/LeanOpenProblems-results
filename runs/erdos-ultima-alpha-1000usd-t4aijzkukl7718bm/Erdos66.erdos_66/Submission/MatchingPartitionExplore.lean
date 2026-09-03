import Submission.DisjointMeanExplore

/-! A matching partition function bounds large collections of realized
events while its expectation factors on disjoint coordinate supports. -/
namespace Erdos66MatchingPartition
open Erdos66UniformSelection Erdos66DisjointMean
open scoped Classical
set_option maxHeartbeats 1200000
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
variable {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]

noncomputable def matchings (S : Finset κ) (E : κ → Finset ι) : Finset (Finset κ) :=
  S.powerset.filter (fun M ↦ (M : Set κ).Pairwise (fun e f ↦ Disjoint (E e) (E f)))

noncomputable def partition (S : Finset κ) (E : κ → Finset ι)
    (f : κ → (∀ i, α i) → ℝ) (t : ℝ) (ω : ∀ i, α i) : ℝ :=
  ∑ M ∈ matchings S E, ∏ e ∈ M, (Real.exp t - 1) * f e ω

lemma partition_nonneg (S : Finset κ) (E : κ → Finset ι)
    (f : κ → (∀ i, α i) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : ∀ e ∈ S, ∀ ω, 0 ≤ f e ω) (ω : ∀ i, α i) :
    0 ≤ partition S E f t ω := by
  apply Finset.sum_nonneg
  intro M hM
  apply Finset.prod_nonneg
  intro e he
  exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))
    (hf e (Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1 he) ω)

lemma mean_partition_le (S : Finset κ) (E : κ → Finset ι)
    (f : κ → (∀ i, α i) → ℝ) (t : ℝ) (ht : 0 ≤ t) (p : κ → ℝ)
    (hf : ∀ e ∈ S, ∀ ω, 0 ≤ f e ω)
    (hdep : ∀ e ∈ S, DependsOn (f e) (E e))
    (hp : ∀ e ∈ S, mean (f e) ≤ p e) :
    mean (partition S E f t) ≤ Real.exp ((Real.exp t - 1) * ∑ e ∈ S, p e) := by
  have hw : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht)
  have hm (e : κ) (he : e ∈ S) : 0 ≤ mean (f e) := by
    exact (mean_mono (fun _ ↦ 0) (f e) (hf e he)).trans_eq' (mean_const 0)
  have hp0 (e : κ) (he : e ∈ S) : 0 ≤ p e := (hm e he).trans (hp e he)
  unfold partition
  rw [mean_sum]
  have hfirst : (∑ M ∈ matchings S E,
      mean (fun ω ↦ ∏ e ∈ M, (Real.exp t - 1) * f e ω)) =
      ∑ M ∈ matchings S E, ∏ e ∈ M, (Real.exp t - 1) * mean (f e) := by
    apply Finset.sum_congr rfl
    intro M hM
    obtain ⟨hMS,hM⟩ := Finset.mem_filter.mp hM
    have hs : M ⊆ S := Finset.mem_powerset.mp hMS
    rw [mean_prod_of_disjoint M E _ hM]
    · simp only [mean_const_mul]
    · intro e he x y hxy
      dsimp only
      rw [hdep e (hs he) hxy]
  rw [hfirst]
  calc
    _ ≤ ∑ M ∈ matchings S E, ∏ e ∈ M, (Real.exp t - 1) * p e := by
      apply Finset.sum_le_sum
      intro M hM
      have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
      apply Finset.prod_le_prod
      · intro e he; exact mul_nonneg hw (hm e (hs he))
      · intro e he; exact mul_le_mul_of_nonneg_left (hp e (hs he)) hw
    _ ≤ ∑ M ∈ S.powerset, ∏ e ∈ M, (Real.exp t - 1) * p e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro M hM hnot
      exact Finset.prod_nonneg (fun e he ↦ mul_nonneg hw (hp0 e (Finset.mem_powerset.mp hM he)))
    _ = ∏ e ∈ S, (1 + (Real.exp t - 1) * p e) := Finset.prod_one_add S |>.symm
    _ ≤ ∏ e ∈ S, Real.exp ((Real.exp t - 1) * p e) := by
      apply Finset.prod_le_prod
      · intro e he; exact add_nonneg (by norm_num) (mul_nonneg hw (hp0 e he))
      · intro e he; linarith [Real.add_one_le_exp ((Real.exp t - 1) * p e)]
    _ = _ := by rw [← Real.exp_sum,← Finset.mul_sum]

lemma exp_card_le_partition (S M : Finset κ) (E : κ → Finset ι)
    (f : κ → (∀ i, α i) → ℝ) (t : ℝ) (ht : 0 ≤ t) (ω : ∀ i, α i)
    (hf : ∀ e ∈ S, 0 ≤ f e ω) (hMS : M ⊆ S)
    (hM : (M : Set κ).Pairwise (fun e f ↦ Disjoint (E e) (E f)))
    (hreal : ∀ e ∈ M, f e ω = 1) :
    Real.exp (t * M.card) ≤ partition S E f t ω := by
  have hw : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht)
  have hsub : M.powerset ⊆ matchings S E := by
    intro T hT
    have hTM := Finset.mem_powerset.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hTM.trans hMS),hM.mono hTM⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun T ↦ ∏ e ∈ T, (Real.exp t-1)*f e ω)
    hsub (fun T hT _ ↦ Finset.prod_nonneg (fun e he ↦ mul_nonneg hw
      (hf e (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1 he))))
  have he : (∑ T ∈ M.powerset, ∏ e ∈ T, (Real.exp t-1)*f e ω) = Real.exp (t*M.card) := by
    rw [← Finset.prod_one_add]
    have hp : (∏ e ∈ M, (1+(Real.exp t-1)*f e ω)) = ∏ _e ∈ M, Real.exp t := by
      apply Finset.prod_congr rfl
      intro e he
      rw [hreal e he]
      ring
    rw [hp, ← Real.exp_sum]
    simp [mul_comm]
  rw [he] at hh
  exact hh

end Erdos66MatchingPartition
