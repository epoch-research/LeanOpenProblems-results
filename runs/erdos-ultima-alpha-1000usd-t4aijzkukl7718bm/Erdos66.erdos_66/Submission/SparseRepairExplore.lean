import Submission.RepairChainExplore

/-! A conditional reduction to a base set whose exceptional targets are
sufficiently sparse. This file does not assert existence of such a base set. -/
namespace Erdos66SparseRepair
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66RepairChain Erdos66Explore
open scoped Topology Classical
set_option maxHeartbeats 1000000

/-- The positive regularized logarithm is asymptotic to the ordinary logarithm. -/
lemma logScale_div_log_limit :
    Tendsto (fun n : ℕ ↦ logScale n / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd := (Real.tendsto_log_comp_add_sub_log (2 : ℝ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (hd.div_atTop hlog).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  dsimp [Function.comp_def, logScale]
  field_simp
  <;> ring

lemma tendsto_of_logScale_tails (B : Set ℕ) (c : ℝ)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep B z : ℝ) ≤ (c + ε) * logScale z)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (c - ε) * logScale z ≤ (sumRep B z : ℝ)) :
    Tendsto (fun n ↦ (sumRep B n : ℝ) / Real.log n) atTop (𝓝 c) := by
  have hh : Tendsto (fun n ↦ (sumRep B n : ℝ) / logScale n) atTop (𝓝 c) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [hl ((c-a)/2) (by linarith)] with z hz
      have hz' := (le_div_iff₀ (logScale_pos z)).mpr hz
      linarith
    · intro a ha
      filter_upwards [hu ((a-c)/2) (by linarith)] with z hz
      have hz' := (div_le_iff₀ (logScale_pos z)).mpr hz
      linarith
  have hprod := hh.mul logScale_div_log_limit
  simp only [mul_one] at hprod
  convert hprod using 1
  funext n
  field_simp [(logScale_pos n).ne']

/-- A uniform threshold sequence for clipped repairs of one base envelope. -/
theorem exists_repair_thresholds (c K C : ℝ) (hc : 0 < c)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ T : ℕ → ℕ, ∀ k n : ℕ, T k ≤ n → ∀ A : Set ℕ,
      (∀ z, (sumRep A z : ℝ) ≤ K + (max C c + 1) * logScale z) →
      ∃ F : Finset ℕ,
        c * logScale n - 2 < (sumRep (A ∪ (F : Set ℕ)) n : ℝ) ∧
        ∀ z, (sumRep (A ∪ (F : Set ℕ)) z : ℝ) ≤
          max (sumRep A z : ℝ) (c * logScale z) + allowance k * logScale z := by
  have ht (k : ℕ) := eventually_clipped_repair c (allowance k) K (max C c + 1)
    hc (residual_pos (k + 1)) hK (by linarith [le_max_left C c])
  choose T hT using fun k ↦ eventually_atTop.mp (ht k)
  refine ⟨T, fun k n hn A hA ↦ ?_⟩
  obtain ⟨F, hsupport, hlow, htarget, hother⟩ := hT k n hn A hA
  refine ⟨F, hlow, fun z ↦ ?_⟩
  by_cases hzn : z = n
  · subst z
    exact htarget.trans (le_add_of_nonneg_right (mul_nonneg (residual_pos (k+1)).le (logScale_pos n).le))
  · have hh := hother z hzn
    have hm := le_max_left (sumRep A z : ℝ) (c * logScale z)
    linarith

/-- Construct a chain of finite repairs, keeping a common logarithmic envelope. -/
theorem exists_clipped_chain (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (T : ℕ → ℕ)
    (hT : ∀ k n : ℕ, T k ≤ n → ∀ A : Set ℕ,
      (∀ z, (sumRep A z : ℝ) ≤ K + (max C c + 1) * logScale z) →
      ∃ F : Finset ℕ,
        c * logScale n - 2 < (sumRep (A ∪ (F : Set ℕ)) n : ℝ) ∧
        ∀ z, (sumRep (A ∪ (F : Set ℕ)) z : ℝ) ≤
          max (sumRep A z : ℝ) (c * logScale z) + allowance k * logScale z)
    (n : ℕ → ℕ) (hn : ∀ k, T k ≤ n k) (A : Set ℕ)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K + C * logScale z) :
    ∃ (S : ℕ → Set ℕ) (F : ℕ → Finset ℕ), S 0 = A ∧
      (∀ k, S (k+1) = S k ∪ (F k : Set ℕ)) ∧
      (∀ k, c * logScale (n k) - 2 < (sumRep (S (k+1)) (n k) : ℝ)) ∧
      (∀ k z, (sumRep (S (k+1)) z : ℝ) ≤
        max (sumRep (S k) z : ℝ) (c * logScale z) + allowance k * logScale z) := by
  let Good (k : ℕ) (B : Set ℕ) : Prop :=
    ∀ z, (sumRep B z : ℝ) ≤ K + (max C c + budget k) * logScale z
  have hstart : Good 0 A := by
    intro z
    simp only [budget_zero, add_zero]
    exact (hA z).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left C c) (logScale_pos z).le))
  have hnext (k : ℕ) (B : Set ℕ) (hB : Good k B) :
      ∃ F : Finset ℕ, Good (k+1) (B ∪ (F : Set ℕ)) ∧
        c * logScale (n k) - 2 < (sumRep (B ∪ (F : Set ℕ)) (n k) : ℝ) ∧
        ∀ z, (sumRep (B ∪ (F : Set ℕ)) z : ℝ) ≤
          max (sumRep B z : ℝ) (c * logScale z) + allowance k * logScale z := by
    have hbound : ∀ z, (sumRep B z : ℝ) ≤ K + (max C c + 1) * logScale z := by
      intro z
      exact (hB z).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (budget_le_one k)) (logScale_pos z).le))
    obtain ⟨F, hlow, hu⟩ := hT k (n k) (hn k) B hbound
    refine ⟨F, ?_, hlow, hu⟩
    intro z
    have htarget : c * logScale z ≤ K + (max C c + budget k) * logScale z := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right C c) (logScale_pos z).le
      have hb := mul_nonneg (budget_nonneg k) (logScale_pos z).le
      nlinarith
    have hm := max_le (hB z) htarget
    have hh := hu z
    rw [budget_succ]
    nlinarith
  choose packet hp using hnext
  let State (k : ℕ) := {B : Set ℕ // Good k B}
  let next (k : ℕ) (s : State k) : State (k+1) :=
    ⟨s.val ∪ (packet k s.val s.property : Set ℕ), (hp k s.val s.property).1⟩
  let s : (k : ℕ) → State k := fun k ↦ Nat.rec ⟨A, hstart⟩ next k
  let S (k : ℕ) : Set ℕ := (s k).val
  let F (k : ℕ) : Finset ℕ := packet k (s k).val (s k).property
  refine ⟨S, F, rfl, fun k ↦ rfl, ?_, ?_⟩
  · intro k
    exact (hp k (s k).val (s k).property).2.1
  · intro k z
    exact (hp k (s k).val (s k).property).2.2 z

/-- Any base set with the right upper bound and with all lower-bound failures
confined to a sufficiently late target sequence can be completed to a witness.
The threshold function is fixed before both the base set and the sequence. -/
theorem sparse_exception_completion (c K C : ℝ) (hc : 0 < c)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ T : ℕ → ℕ, ∀ (n : ℕ → ℕ), (∀ k, T k ≤ n k) →
      ∀ A : Set ℕ,
      (∀ z, (sumRep A z : ℝ) ≤ K + C * logScale z) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        (sumRep A z : ℝ) ≤ (c + ε) * logScale z) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        z ∉ Set.range n → (c - ε) * logScale z ≤ (sumRep A z : ℝ)) →
      ∃ B : Set ℕ, A ⊆ B ∧
        Tendsto (fun z ↦ (sumRep B z : ℝ) / Real.log z) atTop (𝓝 c) := by
  obtain ⟨T, hT⟩ := exists_repair_thresholds c K C hc hK hC
  refine ⟨T, fun n hn A hA hu hl ↦ ?_⟩
  obtain ⟨S, F, hzero, hstep, hlow, hupper⟩ := exists_clipped_chain c K C hc hK hC T hT n hn A hA
  let B : Set ℕ := ⋃ k, S k
  have hAB : A ⊆ B := by
    rw [← hzero]
    exact Set.subset_iUnion S 0
  have hBupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep B z : ℝ) ≤ (c + ε) * logScale z := by
    apply clipped_union_upper_tail S F c hstep hupper
    simpa only [hzero] using hu
  refine ⟨B, hAB, tendsto_of_logScale_tails B c hBupper ?_⟩
  intro ε hε
  have hlarge := (logScale_atTop.const_div_atTop (2 : ℝ)).eventually_lt_const hε
  filter_upwards [hl ε hε, hlarge] with z hz hlargez
  by_cases he : z ∈ Set.range n
  · obtain ⟨k, rfl⟩ := he
    have hm : (sumRep (S (k+1)) (n k) : ℝ) ≤ sumRep B (n k) := by
      exact_mod_cast sumRep_mono (Set.subset_iUnion S (k+1)) (n k)
    have hh := hlow k
    have heps := (div_lt_iff₀ (logScale_pos (n k))).mp hlargez
    nlinarith
  · have hm : (sumRep A z : ℝ) ≤ sumRep B z := by
      exact_mod_cast sumRep_mono hAB z
    exact (hz he).trans hm

end Erdos66SparseRepair
