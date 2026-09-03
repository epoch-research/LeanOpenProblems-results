import Submission.SignedComplementUnit

/-! The actual unit term can now be removed from the complementary-divisor
criterion. The remaining growing e>=2 sum is explicitly retained. -/
namespace Erdos371
open Finset Filter
open scoped Topology

noncomputable def nonunitComplementedRoughTail (B H N n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ Icc 2 ((N+1)/H),
      if e∣roughRadical B (n*(n+1)) ∧ (H*N)*e<roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e)
      else 0

lemma complementedRoughTail_unit_add_nonunit (B H N n : ℕ) (hH : 0<H) (hHN : H≤N+1) :
    complementedRoughTail B H N n = roughComplementUnit B (H*N) n+nonunitComplementedRoughTail B H N n := by
  have hQ : 1≤(N+1)/H := (Nat.le_div_iff_mul_le hH).mpr (by simpa only [one_mul] using hHN)
  have he : Icc 1 ((N+1)/H)=insert 1 (Icc 2 ((N+1)/H)) := by
    ext e
    simp only [mem_Icc,mem_insert]
    omega
  have hn : 1∉Icc 2 ((N+1)/H) := by simp
  unfold complementedRoughTail nonunitComplementedRoughTail
  rw [he,sum_insert hn,mul_add,roughComplementUnit_eq]

lemma subpower_multiplier_le_endpoint (B H : ℕ → ℕ)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1) : ∀ᶠ N in atTop, H N≤N+1 := by
  filter_upwards [hHB,subpower_cutoff_add_one_sq_eventually_le B hlog] with N hh hb
  nlinarith

/-- This equivalence uses the newly proved signed unit cancellation. It
does NOT assert cancellation of the remaining complementary terms. -/
theorem density_iff_nonunit_complement (B H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop)
    (hlog : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N≤B N+1)
    (hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0))
    (hunit : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughComplementUnit (B N) (H N*N) (n+1))/N) atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, nonunitComplementedRoughTail (B N) (H N) N (n+1))/N)
        atTop (𝓝 0) := by
  rw [density_iff_sublinear_complement B H hH hlog hsmall]
  have hd : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, complementedRoughTail (B N) (H N) N (n+1))/N-
      (∑ n ∈ range N, nonunitComplementedRoughTail (B N) (H N) N (n+1))/N) atTop (𝓝 0) := by
    apply hunit.congr'
    filter_upwards [hH.eventually_gt_atTop 0,subpower_multiplier_le_endpoint B H hlog hHB] with N hh hHN
    simp only [complementedRoughTail_unit_add_nonunit (B N) (H N) N _ hh hHN,
      sum_add_distrib,add_div,add_sub_cancel_right]
  constructor
  · intro h
    have ht := h.sub hd
    simp only [sub_zero] at ht
    convert ht using 1
    funext N
    ring
  · intro h
    have ht := hd.add h
    simpa only [sub_add_cancel,add_zero] using ht

/-- An unconditional reduction of the unchanged conjecture to the explicit
nonunit range. The existence of the cutoffs is proved, not postulated. -/
theorem exists_nonunit_complement_criterion :
    ∃ B H : ℕ → ℕ, Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0) ∧
      ({n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
        Tendsto (fun N : ℕ => (∑ n ∈ range N, nonunitComplementedRoughTail (B N) (H N) N (n+1))/N)
          atTop (𝓝 0)) := by
  obtain ⟨B,H,C,hB,hH,hlog,hHB,hC,hprefix,hClim,hunit⟩ := exists_signed_complement_unit_cutoffs
  have hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, roughSmallDivisorSum (B N) (H N*N) (n+1))/N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hClim
    filter_upwards [hprefix] with N hp
    rw [norm_div,Real.norm_natCast,Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right (hp N) (Nat.cast_nonneg N)
  exact ⟨B,H,hB,hH,hlog,density_iff_nonunit_complement B H hH hlog hHB hsmall hunit⟩

#print axioms exists_nonunit_complement_criterion
end Erdos371
