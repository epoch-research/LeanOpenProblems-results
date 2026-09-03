import Submission.CriticalNonlinearPrimeProxy

/-! Uniform tails and continuity of the critical detector's composite error.
These regularity results do not establish divergence of the full detector. -/
namespace Erdos972CompositeErrorRegularity

open Filter Finset
open scoped Topology
open Erdos972CriticalNonlinearPrimeProxy Erdos972PrimePowerError
open Erdos972NonlinearPrimeProxy

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def compositeTail (B : ℕ) : ℝ :=
  ∑' q : {q : ℕ // q ∉ range B}, compositeProxyTwo q

noncomputable def totalError (α : ℝ) : ℝ := ∑' n : ℕ, primeInputErrorTwo α n

noncomputable def partialError (B : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ range B, primeInputErrorTwo α n

lemma compositeTail_nonneg (B : ℕ) : 0 ≤ compositeTail B :=
  tsum_nonneg fun q => compositeProxyTwo_nonneg q

lemma compositeTail_tendsto : Tendsto compositeTail atTop (𝓝 0) := by
  exact (tendsto_tsum_compl_atTop_zero compositeProxyTwo).comp tendsto_finset_range

/-- Output injectivity bounds all input tails by one common summable output tail. -/
theorem uniform_tail_bound {α : ℝ} (hα : 1 ≤ α) (B : ℕ) :
    0 ≤ totalError α - partialError B α ∧
      totalError α - partialError B α ≤ compositeTail B := by
  classical
  have heq := (summable_primeInputErrorTwo hα).sum_add_tsum_subtype_compl (range B)
  have htail : totalError α - partialError B α =
      ∑' n : {n : ℕ // n ∉ range B}, primeInputErrorTwo α n := by
    change partialError B α + _ = totalError α at heq
    linarith
  rw [htail]
  constructor
  · exact tsum_nonneg fun n => (primeInputErrorTwo_bounds α n).1
  · let e : {n : ℕ // n ∉ range B} → {q : ℕ // q ∉ range B} := fun n =>
      ⟨floorMul α n, by
        have hnB : B ≤ (n : ℕ) := by
          simpa only [mem_range, not_lt] using n.property
        simpa only [mem_range, not_lt] using hnB.trans (self_le_floorMul hα n)⟩
    have hi : Function.Injective e := by
      intro n m h
      apply Subtype.ext
      exact (floorMul_strictMono hα).injective (congrArg Subtype.val h)
    exact Summable.tsum_le_tsum_of_inj e hi
      (fun q _ => compositeProxyTwo_nonneg q)
      (fun n => (primeInputErrorTwo_bounds α n).2)
      ((summable_primeInputErrorTwo hα).subtype _)
      (summable_compositeProxyTwo.subtype _)

lemma uniform_abs_tail_bound {α : ℝ} (hα : 1 ≤ α) (B : ℕ) :
    |totalError α - partialError B α| ≤ compositeTail B := by
  rw [abs_of_nonneg (uniform_tail_bound hα B).1]
  exact (uniform_tail_bound hα B).2

/-- Uniform convergence holds on the entire half-line, not merely pointwise in alpha. -/
theorem partialError_tendstoUniformlyOn :
    TendstoUniformlyOn partialError totalError atTop (Set.Ici 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.mp compositeTail_tendsto).2 ε hε] with B hB α hα
  rw [Real.dist_eq]
  exact (uniform_abs_tail_bound hα B).trans_lt hB

lemma floorMul_eventually_eq {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (n : ℕ) :
    ∀ᶠ β in 𝓝 α, floorMul β n = floorMul α n := by
  by_cases hn : n = 0
  · subst n
    simp [floorMul]
  · have hpos : 0 < floorMul α n :=
      (Nat.pos_of_ne_zero hn).trans_le (self_le_floorMul hα n)
    have hlow : (floorMul α n : ℝ) < α * n := by
      apply lt_of_le_of_ne (Nat.floor_le (by positivity : 0 ≤ α * (n : ℝ)))
      exact ((hI.mul_natCast hn).ne_nat _).symm
    have hhigh : α * n < (floorMul α n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcont : ContinuousAt (fun β : ℝ => β * (n : ℝ)) α :=
      continuousAt_id.mul continuousAt_const
    filter_upwards [continuousAt_const.eventually_lt hcont hlow,
      hcont.eventually_lt continuousAt_const hhigh] with β hβlow hβhigh
    exact (Nat.floor_eq_iff' (Nat.ne_of_gt hpos)).mpr ⟨hβlow.le, hβhigh⟩

lemma error_term_eventually_eq {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (n : ℕ) :
    ∀ᶠ β in 𝓝 α, primeInputErrorTwo β n = primeInputErrorTwo α n := by
  filter_upwards [floorMul_eventually_eq hα hI n] with β hβ
  simp only [primeInputErrorTwo, primeProxyWeightTwo, primePairIndicator, hβ]

lemma partialError_eventually_eq {α : ℝ} (hα : 1 ≤ α) (hI : Irrational α) (B : ℕ) :
    ∀ᶠ β in 𝓝 α, partialError B β = partialError B α := by
  have hh : ∀ᶠ β in 𝓝 α, ∀ n ∈ range B,
      primeInputErrorTwo β n = primeInputErrorTwo α n :=
    (Finset.eventually_all _).mpr (fun n _ => error_term_eventually_eq hα hI n)
  filter_upwards [hh] with β hβ
  exact sum_congr rfl hβ

/-- The complete composite error is continuous at every irrational slope greater than one.
This is a statement about the error, not the full prime detector. -/
theorem continuousAt_totalError {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    ContinuousAt totalError α := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_order.mp compositeTail_tendsto).2 (ε/2) (by positivity))
  have hsmall := hB B le_rfl
  filter_upwards [partialError_eventually_eq hα.le hI B,
    continuousAt_const.eventually_lt continuousAt_id hα] with β hβ hβone
  rw [Real.dist_eq]
  calc
    |totalError β - totalError α| =
        |(totalError β - partialError B β) - (totalError α - partialError B α)| := by
          rw [hβ]
          congr 1
          ring
    _ ≤ |totalError β - partialError B β| + |totalError α - partialError B α| :=
      abs_sub _ _
    _ ≤ compositeTail B + compositeTail B :=
      add_le_add (uniform_abs_tail_bound hβone.le B) (uniform_abs_tail_bound hα.le B)
    _ < ε := by linarith

#print axioms uniform_tail_bound
#print axioms partialError_tendstoUniformlyOn
#print axioms continuousAt_totalError

end Erdos972CompositeErrorRegularity
