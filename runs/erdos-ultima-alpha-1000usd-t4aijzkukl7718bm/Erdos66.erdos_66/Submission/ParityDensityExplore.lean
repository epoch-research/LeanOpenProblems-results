import Submission.SquarePrefixDensityExplore

/-! Separate parity self-counts converge in natural density. This is a
necessary condition, and not the pointwise coefficient-reduction statement. -/
namespace Erdos66ParityDensity
open Erdos66SquarePrefixDensity Erdos66AbelSquarePrefix Erdos66ParityRepresentation
  Erdos66Counting Erdos66ResidueSeries
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2200000

noncomputable def ratioBad (a : ℕ → ℝ) (c ε : ℝ) : Set ℕ :=
  {n | ε ≤ |a n/Real.log ((n : ℝ)+2)-c|}

lemma paired_bad_eventual_subset (a b : ℕ → ℝ) {c ε : ℝ} (hε : 0<ε)
    (h : Tendsto (fun n ↦ (a n+b n)/Real.log ((n : ℝ)+2)) atTop (𝓝 c)) :
    ∀ᶠ n : ℕ in atTop,
      n∈ratioBad a (c/2) ε ∪ ratioBad b (c/2) ε → n∈logBad (fun n ↦ a n-b n) ε := by
  filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with n hn
  have hsum : |(a n+b n)/Real.log ((n : ℝ)+2)-c|<ε := by
    simpa only [Real.dist_eq] using hn
  intro hbad
  by_contra hnot
  have hnot' : |a n-b n|<ε*Real.log ((n : ℝ)+2) := lt_of_not_ge hnot
  have hL : 0<Real.log ((n : ℝ)+2) :=
    Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hd : |(a n-b n)/Real.log ((n : ℝ)+2)|<ε := by
    rw [abs_div,abs_of_pos hL]
    exact (div_lt_iff₀ hL).mpr hnot'
  rcases hbad with ha | hb
  · change ε ≤ |a n/Real.log ((n : ℝ)+2)-c/2| at ha
    have he : ((a n+b n)/Real.log ((n : ℝ)+2)-c)+
        (a n-b n)/Real.log ((n : ℝ)+2)=2*(a n/Real.log ((n : ℝ)+2)-c/2) := by ring
    have hh := abs_add_le ((a n+b n)/Real.log ((n : ℝ)+2)-c)
      ((a n-b n)/Real.log ((n : ℝ)+2))
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    linarith
  · change ε ≤ |b n/Real.log ((n : ℝ)+2)-c/2| at hb
    have he : ((a n+b n)/Real.log ((n : ℝ)+2)-c)-
        (a n-b n)/Real.log ((n : ℝ)+2)=2*(b n/Real.log ((n : ℝ)+2)-c/2) := by ring
    have hh := abs_sub ((a n+b n)/Real.log ((n : ℝ)+2)-c)
      ((a n-b n)/Real.log ((n : ℝ)+2))
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    linarith

/-- A pointwise sum limit and a vanishing mean-square contrast imply that
both component limits hold in density. Sparse outliers remain possible. -/
theorem paired_ratios_in_density (a b : ℕ → ℝ) {c : ℝ}
    (hs : Tendsto (fun n ↦ (a n+b n)/Real.log ((n : ℝ)+2)) atTop (𝓝 c))
    (hd : Tendsto (fun N : ℕ ↦ (∑ n∈Finset.range N, (a n-b n)^2)/
      ((N : ℝ)*(Real.log N)^2)) atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun N : ℕ ↦
      (count (ratioBad a (c/2) ε ∪ ratioBad b (c/2) ε) N : ℝ)/N) atTop (𝓝 0) := by
  exact density_zero_of_eventual_subset _ _ (logBad_density_zero _ hd hε)
    (paired_bad_eventual_subset a b hε hs)

lemma witness_parity_self_sum_shiftlog {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ ((sumRep (evenSet A) (n+1) : ℝ)+(sumRep (oddSet A) n : ℝ))/
      Real.log ((n : ℝ)+2)) atTop (𝓝 c) := by
  have hh := (witness_parity_self_sum_limit h).div (log_affine_ratio 1 2)
    (by norm_num : (1 : ℝ)≠0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ)≠0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  simp only [Pi.div_apply,Nat.mul_one,Nat.cast_add,Nat.cast_ofNat]
  field_simp

/-- A hypothetical witness splits into parity self-counts with coefficient
c/2 in density. The even component is indexed by n+1 to retain the exact
odd/odd carry in the comparison. -/
theorem witness_parity_self_counts_in_density {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun N : ℕ ↦
      (count (ratioBad (fun n ↦ (sumRep (evenSet A) (n+1) : ℝ)) (c/2) ε ∪
        ratioBad (fun n ↦ (sumRep (oddSet A) n : ℝ)) (c/2) ε) N : ℝ)/N) atTop (𝓝 0) := by
  exact paired_ratios_in_density _ _ (witness_parity_self_sum_shiftlog h)
    (witness_parity_prefix_zero h) hε

end Erdos66ParityDensity
