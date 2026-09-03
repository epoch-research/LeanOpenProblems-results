import Submission.DyadicEndpointRegularity

/-!
One-sided version of the smoothed dyadic endpoint criterion. Only a
nonvanishing downward jump needs to be excluded. The arithmetic no-drop
hypothesis below is NOT proved in this file.
-/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma dyadic_no_drop_iterate (q : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, q N ≤ q (2*N)+ε)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, q N ≤ q (2^k*N)+ε := by
  induction k generalizing ε with
  | zero =>
    simp only [pow_zero,one_mul]
    exact Eventually.of_forall (fun N => le_add_of_nonneg_right hε.le)
  | succ k ih =>
    have hp : 0 < (2 : ℕ)^k := pow_pos (by omega) _
    have ht : Tendsto (fun N : ℕ => 2^k*N) atTop atTop :=
      tendsto_atTop_mono (fun N => by dsimp; nlinarith) tendsto_id
    filter_upwards [ih (ε/2) (half_pos hε), ht.eventually (h (ε/2) (half_pos hε))]
      with N h₁ h₂
    have he : 2*(2^k*N) = 2^(k+1)*N := by rw [pow_succ]; ring
    simp only [he] at h₂
    linarith

/-- For a nonnegative sequence with syndetic near-zero Cesàro means, it
suffices to exclude asymptotically nonzero downward dyadic jumps. -/
theorem nonneg_prefixMean_zero_of_dyadic_no_drop (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hdrop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      prefixMean N f ≤ prefixMean (2*N) f+ε)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, 2 ≤ C ∧ ∃ T : ℕ, 1 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∃ M : ℕ, N ≤ M ∧ M ≤ C*N ∧ |prefixMean M f| < ε) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) := by
  have hnon (N : ℕ) : 0 ≤ prefixMean N f := by
    unfold prefixMean
    exact div_nonneg (sum_nonneg (fun n _ => hf n)) (Nat.cast_nonneg N)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C,hC,T,hT,hnear⟩ := hnear (ε/4) (by positivity)
  have hgood : ∀ᶠ N : ℕ in atTop, ∀ j ∈ range (C+1),
      prefixMean N f ≤ prefixMean (2^j*N) f+ε/2 := by
    rw [eventually_all_finset]
    intro j _hj
    exact dyadic_no_drop_iterate (fun N => prefixMean N f) hdrop j (ε/2) (half_pos hε)
  filter_upwards [hgood,eventually_ge_atTop T] with N hgood hNT
  have hN : 0 < N := hT.trans hNT
  obtain ⟨M,hNM,hMC,hM⟩ := hnear N hNT
  have hquot : 0 < M/N := Nat.div_pos hNM hN
  let j := Nat.log 2 (M/N)
  have hjC : j ≤ C := (Nat.log_le_self 2 (M/N)).trans (by
    simpa only [Nat.mul_div_cancel _ hN] using Nat.div_le_div_right (c := N) hMC)
  have hlow : 2^j*N ≤ M := (Nat.mul_le_mul_right N (Nat.pow_log_le_self 2 hquot.ne')).trans
    (Nat.div_mul_le_self M N)
  have hhigh : M < 2*(2^j*N) := by
    have hh := (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_pow_succ_log_self (by omega : 1 < 2) (M/N))
    simpa only [j,pow_succ,Nat.mul_assoc,Nat.mul_left_comm] using hh
  have hbase : (0 : ℝ) < (2^j*N : ℕ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) hN
  have hsum : ((2^j*N : ℕ) : ℝ)*prefixMean (2^j*N) f ≤ (M : ℝ)*prefixMean M f := by
    rw [mul_prefixMean_eq_sum,mul_prefixMean_eq_sum]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hlow) (fun n _ _ => hf n)
  have hhighr : (M : ℝ) ≤ 2*((2^j*N : ℕ) : ℝ) := by exact_mod_cast hhigh.le
  have hp : prefixMean (2^j*N) f ≤ 2*prefixMean M f := by
    have hh := mul_le_mul_of_nonneg_right hhighr (hnon M)
    nlinarith
  have hg := hgood j (mem_range.mpr (by omega))
  rw [abs_of_nonneg (hnon M)] at hM
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnon N)]
  linarith

/-- A one-sided sufficient condition for the original conjecture. The
hypothesis is still an unproved arithmetic assertion. -/
theorem density_of_smoothedEndpointBias_no_dyadic_drop
    (hdrop : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      smoothedEndpointBias N ≤ smoothedEndpointBias (2*N)+ε) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  have hq := nonneg_prefixMean_zero_of_dyadic_no_drop
    (fun k => |prefixMean k factorSign|) (fun k => abs_nonneg _) hdrop
    smoothedEndpointBias_syndetic_near_zero
  have hf : ∀ n, |factorSign n| ≤ 1 := by
    intro n
    simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  rw [density_iff_signed_count]
  simpa only [prefixMean,factorSign_sum_eq_signed_count] using
    prefixMean_zero_of_absolute_prefixMean_zero factorSign hf hq

#print axioms dyadic_no_drop_iterate
#print axioms nonneg_prefixMean_zero_of_dyadic_no_drop
#print axioms density_of_smoothedEndpointBias_no_dyadic_drop
end Erdos371
