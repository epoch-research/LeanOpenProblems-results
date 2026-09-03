import FormalConjecturesUtil
import Submission.PrimeBinKernel

/-! Exact bilinear reindexing of the dyadic signed kernel. The final mean-zero
  condition is stated as a criterion, not proved by this reindexing. -/

namespace Erdos371PrimeBinBilinear

open Finset Filter Erdos371PrimeBinKernel Erdos371PrimeHarmonicBlocks
open Erdos371PrimeDiscrepancy Erdos371SmallPrimeAveraging
open Erdos371Cofactor (cofactor)
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def smoothRow (k n : ℕ) : ℤ := if smooth k n then 1 else 0
noncomputable def primeRow (k n : ℕ) : ℤ := if primeSmooth k n then 1 else 0
noncomputable def dilate (p : ℕ) (f : ℕ → ℤ) (n : ℕ) : ℤ := if p∣n then f (n/p) else 0

lemma smoothRow_zero (k : ℕ) : smoothRow k 0=0 := by simp [smoothRow,smooth]

lemma kernel_eq_rows (k n : ℕ) : kernel k n =
    smoothRow k n*primeRow k (n+1) - primeRow k n*smoothRow k (n+1) := by
  unfold kernel up down smoothRow primeRow
  split_ifs <;> simp_all

lemma quotient_smooth_iff {p k n : ℕ} (hp : p∈block k) (hn : 0<n) :
    p∣n ∧ smooth k (n/p) ↔ P n=p ∧ P (cofactor n)<2^k := by
  obtain ⟨hprime,hlo,hhi⟩ := mem_block.mp hp
  constructor
  · rintro ⟨hd,ha,hs⟩
    have he : P n=p := by
      have hnfac := Nat.div_mul_cancel hd
      rw [← hnfac, P, Nat.maxPrimeFac_mul (by omega : n/p≠0) hprime.ne_zero,
        hprime.maxPrimeFac_eq_self,max_eq_right (hs.le.trans hlo)]
    exact ⟨he,by simpa only [cofactor,he] using hs⟩
  · rintro ⟨he,hs⟩
    have hn1 : 1<n := hprime.one_lt.trans_le (he ▸ (Nat.maxPrimeFac_le : P n≤n))
    refine ⟨he ▸ Nat.maxPrimeFac_dvd,?_,?_⟩
    · have hh := Erdos371Cofactor.cofactor_pos hn1
      simpa only [cofactor,he] using hh
    · simpa only [cofactor,he] using hs

lemma dilate_smooth_eq {p k : ℕ} (hp : p∈block k) (n : ℕ) :
    dilate p (smoothRow k) n = if p=P n then primeRow k n else 0 := by
  by_cases hn : n=0
  · subst n
    simp [dilate,smoothRow_zero,primeRow,primeSmooth]
  · have hn0 : 0<n := by omega
    have he := quotient_smooth_iff hp hn0
    have hleft : dilate p (smoothRow k) n = if p∣n ∧ smooth k (n/p) then 1 else 0 := by
      simp only [dilate,smoothRow,ite_and]
    rw [hleft]
    simp only [he]
    by_cases h : p=P n
    · subst p
      simp [primeRow,primeSmooth,hn0,hp]
    · have hh : P n≠p := Ne.symm h
      simp [h,hh]

lemma primeRow_eq_sum (k n : ℕ) :
    primeRow k n = ∑ p ∈ block k, dilate p (smoothRow k) n := by
  rw [Finset.sum_congr rfl (fun p hp => dilate_smooth_eq hp n)]
  rw [Finset.sum_ite_eq']
  by_cases h : P n∈block k
  · simp [h]
  · simp [primeRow,primeSmooth,h]

lemma sum_before_dilate {p : ℕ} (hp : 0<p) (f g : ℕ → ℤ) (N : ℕ) :
    (∑ n ∈ Finset.range N, g n*dilate p f (n+1)) =
      ∑ a ∈ Finset.Icc 1 (N/p), f a*g (a*p-1) := by
  have he : (∑ n ∈ Finset.range N, g n*dilate p f (n+1)) =
      ∑ n ∈ (Finset.range N).filter (fun n => p∣n+1), g n*f ((n+1)/p) := by
    simp only [dilate,Finset.sum_filter,mul_ite,mul_zero]
  rw [he]
  apply Finset.sum_bij (fun n _ => (n+1)/p)
  · intro n hn
    obtain ⟨hnN,hd⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    refine Finset.mem_Icc.mpr ⟨?_,Nat.div_le_div_right (by omega : n+1≤N)⟩
    have hdiv := Nat.div_pos (Nat.le_of_dvd (by omega : 0<n+1) hd) hp
    omega
  · intro n hn m hm he
    have hnfac := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    have hmfac := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    change (n+1)/p=(m+1)/p at he
    rw [he] at hnfac
    omega
  · intro a ha
    obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp ha
    have hap : 0<a*p := Nat.mul_pos (by omega) hp
    have hapN := (Nat.le_div_iff_mul_le hp).mp haN
    have he : a*p-1+1=a*p := by omega
    refine ⟨a*p-1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩,?_⟩
    · rw [he]; exact dvd_mul_left p a
    · rw [he,Nat.mul_div_cancel _ hp]
  · intro n hn
    have he := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    rw [he,Nat.add_sub_cancel]
    ring

lemma sum_after_dilate_full {p : ℕ} (hp : 0<p) (f g : ℕ → ℤ) (hf : f 0=0) (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), dilate p f n*g (n+1)) =
      ∑ a ∈ Finset.Icc 1 (N/p), f a*g (a*p+1) := by
  have he : (∑ n ∈ Finset.range (N+1), dilate p f n*g (n+1)) =
      ∑ n ∈ (Finset.range (N+1)).filter (fun n => 0<n ∧ p∣n), f (n/p)*g (n+1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn0 : n=0
    · subst n; simp [dilate,hf]
    · have hnpos : 0<n := by omega
      simp [dilate,hnpos,ite_mul]
  rw [he]
  apply Finset.sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hnN,hn0,hd⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    refine Finset.mem_Icc.mpr ⟨?_,Nat.div_le_div_right (by omega : n≤N)⟩
    have hdiv := Nat.div_pos (Nat.le_of_dvd hn0 hd) hp
    omega
  · intro n hn m hm he
    have hnfac := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2.2
    have hmfac := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2.2
    change n/p=m/p at he
    rw [he] at hnfac
    omega
  · intro a ha
    obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp ha
    have hap : 0<a*p := Nat.mul_pos (by omega) hp
    have hapN := (Nat.le_div_iff_mul_le hp).mp haN
    refine ⟨a*p,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hap,dvd_mul_left p a⟩,?_⟩
    exact Nat.mul_div_cancel _ hp
  · intro n hn
    rw [Nat.div_mul_cancel (Finset.mem_filter.mp hn).2.2]

lemma sum_signed_dilate {p : ℕ} (hp : 0<p) (f g : ℕ → ℤ) (hf : f 0=0) (N : ℕ) :
    (∑ n ∈ Finset.range N, (g n*dilate p f (n+1)-dilate p f n*g (n+1))) =
      (∑ a ∈ Finset.Icc 1 (N/p), f a*(g (a*p-1)-g (a*p+1))) +
        dilate p f N*g (N+1) := by
  have hb := sum_before_dilate hp f g N
  have ha := sum_after_dilate_full hp f g hf N
  rw [Finset.sum_range_succ] at ha
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [hb]
  omega

/-- The signed bilinear block has one fixed smoothness threshold `2^k`. -/
noncomputable def bilinear (k N : ℕ) : ℤ :=
  ∑ p ∈ block k, ∑ a ∈ Finset.Icc 1 (N/p),
    smoothRow k a * (smoothRow k (a*p-1)-smoothRow k (a*p+1))

noncomputable def endpoint (k N : ℕ) : ℤ := primeRow k N * smoothRow k (N+1)

lemma kernel_total_eq_bilinear (k N : ℕ) :
    (∑ n ∈ Finset.range N, kernel k n) = bilinear k N + endpoint k N := by
  simp_rw [kernel_eq_rows,primeRow_eq_sum,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have he : (∑ p ∈ block k, ∑ n ∈ Finset.range N,
      (smoothRow k n*dilate p (smoothRow k) (n+1)-dilate p (smoothRow k) n*smoothRow k (n+1))) =
      ∑ p ∈ block k, ((∑ a ∈ Finset.Icc 1 (N/p),
        smoothRow k a*(smoothRow k (a*p-1)-smoothRow k (a*p+1))) +
          dilate p (smoothRow k) N*smoothRow k (N+1)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_signed_dilate (mem_block.mp hp).1.pos _ _ (smoothRow_zero k) N
  rw [he,Finset.sum_add_distrib,← Finset.sum_mul,← primeRow_eq_sum]
  rfl

lemma endpoint_nonneg (k N : ℕ) : 0≤endpoint k N := by
  unfold endpoint primeRow smoothRow
  split_ifs <;> norm_num

lemma endpoint_le_single (k N : ℕ) : endpoint k N ≤ if k=Nat.log 2 (P N) then 1 else 0 := by
  by_cases h : primeSmooth k N
  · have he := log_eq_of_mem_block h.2.1
    simp only [← he,if_true,endpoint,primeRow,if_pos h,one_mul,smoothRow]
    split_ifs <;> norm_num
  · simp only [endpoint,primeRow,if_neg h,zero_mul]
    split_ifs <;> norm_num

lemma endpoint_sum_bounds (N : ℕ) :
    0 ≤ (∑ k ∈ Finset.range (N+1),endpoint k N) ∧
      (∑ k ∈ Finset.range (N+1),endpoint k N) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun k _ => endpoint_nonneg k N),?_⟩
  have hh := Finset.sum_le_sum (s := Finset.range (N+1)) (fun k _ => endpoint_le_single k N)
  simp only [Finset.sum_ite_eq',Finset.mem_range] at hh
  split_ifs at hh <;> omega

noncomputable def bilinearTotal (N : ℕ) : ℤ := ∑ k ∈ Finset.range (N+1),bilinear k N

lemma binned_total_eq (N : ℕ) :
    (∑ n ∈ Finset.range N,binnedSign n) = bilinearTotal N + ∑ k ∈ Finset.range (N+1),endpoint k N := by
  have he : (∑ n ∈ Finset.range N,binnedSign n) =
      ∑ n ∈ Finset.range N,∑ k ∈ Finset.range (N+1),kernel k n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact (sum_kernel (Finset.mem_range.mp hn)).symm
  rw [he,Finset.sum_comm]
  simp only [kernel_total_eq_bilinear,Finset.sum_add_distrib,bilinearTotal]

lemma binned_bilinear_error_bound (N : ℕ) :
    |mean (fun n => (binnedSign n:ℝ)) N - (bilinearTotal N:ℝ)/N| ≤ 1/(N:ℝ) := by
  have he : (∑ n ∈ Finset.range N,(binnedSign n:ℝ)) =
      (bilinearTotal N:ℝ)+∑ k ∈ Finset.range (N+1),(endpoint k N:ℝ) := by
    exact_mod_cast binned_total_eq N
  have h0 : (0:ℝ)≤∑ k ∈ Finset.range (N+1),(endpoint k N:ℝ) := by exact_mod_cast (endpoint_sum_bounds N).1
  have h1 : (∑ k ∈ Finset.range (N+1),(endpoint k N:ℝ))≤1 := by exact_mod_cast (endpoint_sum_bounds N).2
  unfold mean
  rw [he,add_div,add_sub_cancel_left,abs_of_nonneg (div_nonneg h0 (Nat.cast_nonneg N))]
  exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg N)

lemma binned_bilinear_error_tendsto_zero :
    Tendsto (fun N => mean (fun n => (binnedSign n:ℝ)) N - (bilinearTotal N:ℝ)/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat (fun _ => abs_nonneg _) binned_bilinear_error_bound

/-- An exact asymptotic reduction to fixed-cutoff smooth bilinear blocks.
  No estimate for the mean of `bilinearTotal` is asserted here. -/
theorem density_half_iff_bilinear_mean_zero :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      Tendsto (fun N => (bilinearTotal N:ℝ)/N) atTop (𝓝 0) := by
  rw [density_half_iff_binned_mean_zero]
  constructor
  · intro h
    have hh := h.sub binned_bilinear_error_tendsto_zero
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.add binned_bilinear_error_tendsto_zero
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring

end Erdos371PrimeBinBilinear

#print axioms Erdos371PrimeBinBilinear.kernel_total_eq_bilinear
#print axioms Erdos371PrimeBinBilinear.binned_total_eq
#print axioms Erdos371PrimeBinBilinear.density_half_iff_bilinear_mean_zero
