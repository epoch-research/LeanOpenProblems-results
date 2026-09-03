import Submission.MaximalComplementPrefixRow

/-! One diagonal controls an increasing family of complementary-index
prefixes. The exponent-weighted logarithmic cutoff also tends to zero. -/
namespace Erdos371
open Finset Filter
open scoped Topology

/-- A single B,H works for every fixed degree, with a uniform bound even
through B^(K(N)) for some K(N) tending to infinity. This endpoint is still
subpower, not the full complementary endpoint N/H. -/
theorem exists_maximal_complement_diagonal :
    ∃ B H K : ℕ → ℕ, ∃ C : ℕ → ℝ,
      Tendsto B atTop atTop ∧ Tendsto H atTop atTop ∧ Tendsto K atTop atTop ∧
      Tendsto (fun N => (K N+1 : ℝ)*(Real.log (B N+1 : ℝ)/Real.log N)) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, H N ≤ B N+1) ∧ (∀ N, 0 ≤ C N) ∧
      (∀ᶠ N in atTop, ∀ M : ℕ,
        |∑ n ∈ range M, roughSmallDivisorSum (B N) (H N*N) (n+1)| ≤ C N) ∧
      Tendsto (fun N : ℕ => C N/N) atTop (𝓝 0) ∧
      (∀ᶠ N in atTop, ∀ X ≤ (B N)^(K N),
        |(∑ n ∈ range N, untruncatedComplementPrefix (B N) X n)/N| ≤ 1/(K N+1 : ℝ)) := by
  classical
  choose R L hrow using fun k => exists_maximal_complement_prefix_row k ((k+1)^2)
  let P (N k : ℕ) : Prop := (k+1)^2 ≤ R k N ∧ 1 ≤ R k N ∧
    ((k+1)^2+1)*N ≤ (R k N+1)^(L k) ∧
    Real.log (R k N+1 : ℝ)/Real.log N ≤ 2/((k+1)^2+1 : ℝ) ∧
    (∀ X ≤ (R k N)^k, |(∑ n ∈ range N, untruncatedComplementPrefix (R k N) X n)/N| ≤
      1/((k+1)^2+1 : ℝ)) ∧
    roughPrefixBudget (R k N) (L k) (((k+1)^2+1)*N)/N ≤ 1/((k+1)^2+1 : ℝ)
  let K (N : ℕ) := Nat.findGreatest (P N) N
  let B (N : ℕ) := R (K N) N
  let H (N : ℕ) := (K N+1)^2+1
  let C (N : ℕ) := roughPrefixBudget (B N) (L (K N)) (H N*N)
  have hP (k : ℕ) : ∀ᶠ N in atTop, P N k := by
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hrow k
  have hK : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k,hP k] with N hNk hp
    exact Nat.le_findGreatest hNk hp
  have hPK : ∀ᶠ N in atTop, P N (K N) := by
    filter_upwards [hP 0] with N hp
    exact Nat.findGreatest_spec (Nat.zero_le N) hp
  have hB : Tendsto B atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hPK,hK.eventually_ge_atTop M] with N hp hk
    have hh : K N ≤ (K N+1)^2 := by nlinarith
    exact hk.trans (hh.trans hp.1)
  have hH : Tendsto H atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hK.eventually_ge_atTop M] with N hk
    dsimp only [H]
    nlinarith
  have hi : Tendsto (fun N => 1/(K N+1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hK
  have hfrac (N : ℕ) : 1/((K N+1)^2+1 : ℝ) ≤ 1/(K N+1 : ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    have := Nat.cast_nonneg (α := ℝ) (K N)
    nlinarith
  refine ⟨B,H,K,C,hB,hH,hK,?_,?_,?_,?_,?_,?_⟩
  · have hi2 := hi.const_mul 2
    simp only [mul_zero] at hi2
    apply squeeze_zero' (Eventually.of_forall fun N => mul_nonneg (by positivity)
      (div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (B N); linarith))
        (Real.log_natCast_nonneg N))) _ hi2
    filter_upwards [hPK] with N hp
    have hpos : (0 : ℝ) < K N+1 := by positivity
    have hden : (0 : ℝ) < (K N+1)^2+1 := by positivity
    calc
      _ ≤ (K N+1 : ℝ)*(2/((K N+1)^2+1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hp.2.2.2.1 hpos.le
      _ ≤ 2/(K N+1 : ℝ) := by
        rw [show (K N+1 : ℝ)*(2/((K N+1)^2+1 : ℝ)) =
          (2*(K N+1))/((K N+1)^2+1) by ring]
        apply (div_le_div_iff₀ hden hpos).mpr
        nlinarith
      _ = _ := by ring
  · exact hPK.mono fun N hp => Nat.add_le_add_right hp.1 1
  · intro N
    exact roughPrefixBudget_nonneg _ _ _
  · filter_upwards [hPK] with N hp
    intro M
    exact roughSmallDivisorSum_prefix_budget (B N) (L (K N)) (H N*N) M hp.2.1 hp.2.2.1
  · apply squeeze_zero' (Eventually.of_forall fun N =>
      div_nonneg (roughPrefixBudget_nonneg _ _ _) (Nat.cast_nonneg N)) _ hi
    exact hPK.mono fun N hp => hp.2.2.2.2.2.trans (hfrac N)
  · filter_upwards [hPK] with N hp
    intro X hX
    exact (hp.2.2.2.2.1 X hX).trans (hfrac N)

#print axioms exists_maximal_complement_diagonal
end Erdos371
