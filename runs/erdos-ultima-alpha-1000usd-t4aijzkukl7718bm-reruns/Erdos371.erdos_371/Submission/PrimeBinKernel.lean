import FormalConjecturesUtil
import Submission.CofactorPrimeGap

/-! A signed dyadic-prime-bin kernel agreeing with the original comparison
  outside a density-zero exceptional set. No cancellation of its mean is claimed. -/

namespace Erdos371PrimeBinKernel

open Finset Filter Erdos371PrimeHarmonicBlocks
open Erdos371Cofactor (cofactor)
open Erdos371PrimeDiscrepancy Erdos371ReflectionRange Erdos371SmallPrimeAveraging
open scoped Topology

attribute [local instance] Classical.propDecidable

def smooth (k n : ℕ) : Prop := 0<n ∧ P n<2^k
def primeSmooth (k n : ℕ) : Prop :=
  0<n ∧ P n∈block k ∧ P (cofactor n)<2^k

def up (k n : ℕ) : Prop := smooth k n ∧ primeSmooth k (n+1)
def down (k n : ℕ) : Prop := primeSmooth k n ∧ smooth k (n+1)

noncomputable def kernel (k n : ℕ) : ℤ :=
  (if up k n then 1 else 0) - (if down k n then 1 else 0)

def index (n : ℕ) : ℕ := Nat.log 2 (winner n)
noncomputable def binnedSign (n : ℕ) : ℤ := kernel (index n) n

lemma up_order {k n : ℕ} (h : up k n) : P n<P (n+1) :=
  h.1.2.trans_le (mem_block.mp h.2.2.1).2.1

lemma down_order {k n : ℕ} (h : down k n) : P (n+1)<P n :=
  h.2.2.trans_le (mem_block.mp h.1.2.1).2.1

lemma kernel_abs_le_one (k n : ℕ) : |kernel k n| ≤ 1 := by
  unfold kernel
  split_ifs <;> norm_num

lemma kernel_support {k n : ℕ} (h : kernel k n ≠ 0) : winner n∈block k := by
  by_cases hu : up k n
  · simpa only [winner,max_eq_right (up_order hu).le] using hu.2.2.1
  · have hd : down k n := by
      by_contra hd
      simp [kernel,hu,hd] at h
    simpa only [winner,max_eq_left (down_order hd).le] using hd.1.2.1

lemma log_eq_of_mem_block {p k : ℕ} (hp : p∈block k) : Nat.log 2 p=k := by
  obtain ⟨hp,hlo,hhi⟩ := mem_block.mp hp
  have h1 := Nat.le_log_of_pow_le (by decide : 1<(2:ℕ)) hlo
  have h2 := (Nat.log_lt_iff_lt_pow (by decide : 1<(2:ℕ)) hp.ne_zero).mpr hhi
  omega

lemma kernel_eq_zero_of_ne_index {k n : ℕ} (hk : k≠index n) : kernel k n=0 := by
  by_contra h
  have he := log_eq_of_mem_block (kernel_support h)
  exact hk he.symm

lemma kernel_eq_single (k n : ℕ) :
    kernel k n = if k=index n then binnedSign n else 0 := by
  by_cases h : k=index n
  · simp only [h,if_true,binnedSign]
  · simp only [if_neg h,kernel_eq_zero_of_ne_index h]

lemma sum_kernel {n N : ℕ} (hn : n<N) :
    (∑ k ∈ Finset.range (N+1), kernel k n) = binnedSign n := by
  have hindex : index n < N+1 := by
    have h1 := Nat.log_le_self 2 (winner n)
    have h2 := winner_le hn
    dsimp [index]
    omega
  simp only [kernel_eq_single,Finset.sum_ite_eq',Finset.mem_range,hindex,if_true]

def good (n : ℕ) : Prop := 1<n ∧
  2*min (P n) (P (n+1))<winner n ∧
  2*P (cofactor n)<P n ∧ 2*P (cofactor (n+1))<P (n+1)

lemma good_complement_density_zero : {n | ¬good n}.HasDensity 0 := by
  let A : Set ℕ := Erdos371BoundedPrimeGap.lowSet 2
  let B : Set ℕ := {n | max (P n) (P (n+1)) ≤ 2*min (P n) (P (n+1))}
  let C : Set ℕ := {n | 1<n ∧ P n≤2*P (cofactor n)}
  let D : Set ℕ := {n | n+1∈C}
  have hA : A.HasDensity 0 := Erdos371BoundedPrimeGap.lowSet_hasDensity_zero 2
  have hB : B.HasDensity 0 := Erdos371ComparableRatio.fixed_ratio_hasDensity_zero 2
  have hC : C.HasDensity 0 := Erdos371CofactorPrimeGap.fixed_ratio_cofactor_hasDensity_zero 2
  have hD : D.HasDensity 0 := Erdos371CofactorDensity.density_zero_shift hC
  have hU := Erdos371CofactorDensity.density_zero_union
    (Erdos371CofactorDensity.density_zero_union (Erdos371CofactorDensity.density_zero_union hA hB) hC) hD
  apply Erdos371Exploration.density_zero_of_subset (T := ((A∪B)∪C)∪D) _ hU
  intro n hn
  by_cases ha : n∈A
  · exact Or.inl (Or.inl (Or.inl ha))
  · have hn1 : 1<n := by
      have hp : P n≤n := Nat.maxPrimeFac_le
      change ¬(P n≤2 ∨ P (n+1)≤2) at ha
      omega
    by_cases hb : n∈B
    · exact Or.inl (Or.inl (Or.inr hb))
    · by_cases hc : n∈C
      · exact Or.inl (Or.inr hc)
      · apply Or.inr
        change 1<n+1 ∧ P (n+1)≤2*P (cofactor (n+1))
        change ¬(1<n ∧ P n≤2*P (cofactor n)) at hc
        change ¬max (P n) (P (n+1))≤2*min (P n) (P (n+1)) at hb
        change ¬(1<n ∧ 2*min (P n) (P (n+1))< max (P n) (P (n+1)) ∧
          2*P (cofactor n)<P n ∧ 2*P (cofactor (n+1))<P (n+1)) at hn
        omega

lemma below_bin_of_double_lt {m p k : ℕ} (hp : p∈block k) (h : 2*m<p) : m<2^k := by
  have hh := (mem_block.mp hp).2.2
  rw [pow_succ] at hh
  omega

lemma binnedSign_eq_sign_of_good {n : ℕ} (hg : good n) : binnedSign n=sign n := by
  have hn1 := hg.1
  have hp : (winner n).Prime := winner_prime (by omega)
  have hblock : winner n∈block (index n) :=
    Erdos371ComparableLowProduct.block_of_log hp
  by_cases h : P n<P (n+1)
  · have hw : winner n=P (n+1) := max_eq_right h.le
    have hu : up (index n) n := by
      refine ⟨⟨by omega,?_⟩,⟨by omega,hw ▸ hblock,?_⟩⟩
      · apply below_bin_of_double_lt hblock
        simpa only [min_eq_left h.le] using hg.2.1
      · apply below_bin_of_double_lt (hw ▸ hblock)
        exact hg.2.2.2
    have hd : ¬down (index n) n := fun hh => (not_lt_of_gt h) (down_order hh)
    simp [binnedSign,kernel,hu,hd,sign,h]
  · have hne := consecutive_ne n
    have hr : P (n+1)<P n := by omega
    have hw : winner n=P n := max_eq_left hr.le
    have hd : down (index n) n := by
      refine ⟨⟨by omega,hw ▸ hblock,?_⟩,⟨by omega,?_⟩⟩
      · exact below_bin_of_double_lt (hw ▸ hblock) hg.2.2.1
      · apply below_bin_of_double_lt hblock
        simpa only [min_eq_right hr.le] using hg.2.1
    have hu : ¬up (index n) n := fun hh => h (up_order hh)
    simp [binnedSign,kernel,hu,hd,sign,h]

lemma error_abs_le (n : ℕ) : |(sign n:ℝ)-(binnedSign n:ℝ)| ≤ if good n then 0 else 2 := by
  by_cases hg : good n
  · simp [hg,binnedSign_eq_sign_of_good hg]
  · simp only [if_neg hg]
    have hb : |(binnedSign n:ℝ)| ≤ 1 := by exact_mod_cast kernel_abs_le_one (index n) n
    have hs : |(sign n:ℝ)|=1 := by unfold sign; split_ifs <;> norm_num
    have hh := abs_sub (sign n:ℝ) (binnedSign n:ℝ)
    linarith

lemma mean_error_bound (N : ℕ) :
    |mean (fun n => (sign n:ℝ)-(binnedSign n:ℝ)) N| ≤
      2*{n | ¬good n}.partialDensity Set.univ N := by
  rw [← indicator_mean_eq_density,← mean_const_mul]
  unfold mean
  rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Set.mem_setOf_eq,ite_not,mul_ite,mul_one,mul_zero] using error_abs_le n

lemma mean_error_tendsto_zero :
    Tendsto (mean (fun n => (sign n:ℝ)-(binnedSign n:ℝ))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht : Tendsto (fun N => 2*{n | ¬good n}.partialDensity Set.univ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using good_complement_density_zero.const_mul (2:ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => abs_nonneg _) mean_error_bound

/-- The new kernel has exactly the same mean-zero problem as the original
  signs. This is a reduction, not an assertion that either mean vanishes. -/
theorem density_half_iff_binned_mean_zero :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (mean (fun n => (binnedSign n:ℝ))) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  have he (N : ℕ) : (total N:ℝ)/N - mean (fun n => (binnedSign n:ℝ)) N =
      mean (fun n => (sign n:ℝ)-(binnedSign n:ℝ)) N := by
    simp [mean,total,Finset.sum_sub_distrib,sub_div]
  constructor
  · intro h
    have hh := h.sub mean_error_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    rw [← he]
    ring
  · intro h
    have hh := h.add mean_error_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    rw [← he]
    ring

end Erdos371PrimeBinKernel

#print axioms Erdos371PrimeBinKernel.binnedSign_eq_sign_of_good
#print axioms Erdos371PrimeBinKernel.mean_error_tendsto_zero
#print axioms Erdos371PrimeBinKernel.density_half_iff_binned_mean_zero
