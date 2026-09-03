import Submission.ClippedRepairExplore

/-! Summable-error bounds for monotone chains of finite clipped repairs. -/
namespace Erdos66RepairChain
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66Explore
  Erdos66Compactness Erdos66NaturalRepairBridge
open scoped Topology Classical
set_option maxHeartbeats 1200000

noncomputable def residual (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
noncomputable def budget (k : ℕ) : ℝ := 1 - residual k
noncomputable def allowance (k : ℕ) : ℝ := residual (k + 1)

lemma residual_pos (k : ℕ) : 0 < residual k := by dsimp [residual]; positivity
lemma residual_le_one (k : ℕ) : residual k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
lemma budget_nonneg (k : ℕ) : 0 ≤ budget k := sub_nonneg.mpr (residual_le_one k)
lemma budget_le_one (k : ℕ) : budget k ≤ 1 := by dsimp [budget]; linarith [residual_pos k]
@[simp] lemma budget_zero : budget 0 = 0 := by simp [budget, residual]
lemma budget_succ (k : ℕ) : budget (k + 1) = budget k + allowance k := by
  dsimp [budget, allowance, residual]
  rw [pow_succ]
  ring
lemma budget_mono : Monotone budget := by
  apply monotone_nat_of_le_succ
  intro k
  rw [budget_succ]
  exact le_add_of_nonneg_right (residual_pos (k + 1)).le
lemma residual_limit : Tendsto residual atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma union_mono (S : ℕ → Set ℕ) (F : ℕ → Finset ℕ)
    (hstep : ∀ k, S (k + 1) = S k ∪ (F k : Set ℕ)) : Monotone S := by
  apply monotone_nat_of_le_succ
  intro k
  rw [hstep]
  exact Set.subset_union_left

/-- Every fixed representation count of an increasing union is already
attained at a finite stage. -/
lemma sumRep_iUnion_attained (S : ℕ → Set ℕ) (hmono : Monotone S) (z J : ℕ) :
    ∃ k ≥ J, sumRep (⋃ i, S i) z = sumRep (S k) z := by
  have hw (a : ℕ) : ∃ k : ℕ, a ∈ ⋃ i, S i → a ∈ S k := by
    by_cases ha : a ∈ ⋃ i, S i
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
      exact ⟨k, fun _ ↦ hk⟩
    · exact ⟨0, fun h ↦ (ha h).elim⟩
  choose f hf using hw
  let k := max J ((Finset.range (z + 1)).sup f)
  refine ⟨k, le_max_left _ _, sumRep_congr_below (fun a ha ↦ ?_)⟩
  constructor
  · intro hmem
    have hfa : f a ≤ (Finset.range (z + 1)).sup f :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    exact hmono (hfa.trans (le_max_right _ _)) (hf a hmem)
  · intro hmem
    exact Set.mem_iUnion.mpr ⟨k, hmem⟩

lemma finite_stage_cost (S : ℕ → Set ℕ) (F : ℕ → Finset ℕ)
    (hstep : ∀ k, S (k + 1) = S k ∪ (F k : Set ℕ)) (J z : ℕ) :
    sumRep (S J) z ≤ sumRep (S 0) z + 2 * ∑ k ∈ Finset.range J, (F k).card := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [hstep, Finset.sum_range_succ]
    have hh := sumRep_union_finset_le (S J) (F J) z
    omega

lemma clipped_chain_bound (S : ℕ → Set ℕ) (c : ℝ)
    (hstep : ∀ k z, (sumRep (S (k + 1)) z : ℝ) ≤
      max (sumRep (S k) z : ℝ) (c * logScale z) + allowance k * logScale z)
    (J k z : ℕ) (hJk : J ≤ k) :
    (sumRep (S k) z : ℝ) ≤ max (sumRep (S J) z : ℝ) (c * logScale z) +
      (budget k - budget J) * logScale z := by
  induction k, hJk using Nat.le_induction with
  | base => simp
  | succ k hJk ih =>
    have hb : 0 ≤ budget k - budget J := sub_nonneg.mpr (budget_mono hJk)
    have htarget : c * logScale z ≤ max (sumRep (S J) z : ℝ) (c * logScale z) +
        (budget k - budget J) * logScale z := by
      have hh := le_max_right (sumRep (S J) z : ℝ) (c * logScale z)
      have hh' := mul_nonneg hb (logScale_pos z).le
      linarith
    have hm := max_le ih htarget
    have hh := hstep k z
    rw [budget_succ]
    nlinarith

lemma clipped_union_bound (S : ℕ → Set ℕ) (hmono : Monotone S) (c : ℝ)
    (hstep : ∀ k z, (sumRep (S (k + 1)) z : ℝ) ≤
      max (sumRep (S k) z : ℝ) (c * logScale z) + allowance k * logScale z)
    (J z : ℕ) :
    (sumRep (⋃ i, S i) z : ℝ) ≤ max (sumRep (S J) z : ℝ) (c * logScale z) + residual J * logScale z := by
  obtain ⟨k, hJk, he⟩ := sumRep_iUnion_attained S hmono z J
  rw [he]
  have hh := clipped_chain_bound S c hstep J k z hJk
  have hb : budget k - budget J ≤ residual J := by dsimp [budget]; linarith [residual_pos k]
  have hm := mul_le_mul_of_nonneg_right hb (logScale_pos z).le
  linarith

/-- Finite early modifications vanish after normalization, while the tail
of the chosen error budget can be made arbitrarily small. -/
theorem clipped_union_upper_tail (S : ℕ → Set ℕ) (F : ℕ → Finset ℕ) (c : ℝ)
    (hset : ∀ k, S (k + 1) = S k ∪ (F k : Set ℕ))
    (hstep : ∀ k z, (sumRep (S (k + 1)) z : ℝ) ≤
      max (sumRep (S k) z : ℝ) (c * logScale z) + allowance k * logScale z)
    (hbase : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep (S 0) z : ℝ) ≤ (c + ε) * logScale z) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      (sumRep (⋃ i, S i) z : ℝ) ≤ (c + ε) * logScale z := by
  intro ε hε
  obtain ⟨J, hJ⟩ := (residual_limit.eventually_lt_const (show (0 : ℝ) < ε / 3 by positivity)).exists
  let M : ℝ := 2 * ∑ k ∈ Finset.range J, ((F k).card : ℝ)
  have hMlim := logScale_atTop.const_div_atTop M
  filter_upwards [hbase (ε / 3) (by positivity),
    hMlim.eventually_lt_const (show (0 : ℝ) < ε / 3 by positivity)] with z hz hMz
  have hcost : (sumRep (S J) z : ℝ) ≤ sumRep (S 0) z + M := by
    dsimp only [M]
    exact_mod_cast finite_stage_cost S F hset J z
  have hMbound : M ≤ (ε / 3) * logScale z :=
    ((div_lt_iff₀ (logScale_pos z)).mp hMz).le
  have hstage : (sumRep (S J) z : ℝ) ≤ (c + 2 * ε / 3) * logScale z := by nlinarith
  have htarget : c * logScale z ≤ (c + 2 * ε / 3) * logScale z := by
    have hh := mul_nonneg hε.le (logScale_pos z).le
    nlinarith
  have hb := clipped_union_bound S (union_mono S F hset) c hstep J z
  have hm := max_le hstage htarget
  have hr := mul_le_mul_of_nonneg_right hJ.le (logScale_pos z).le
  nlinarith

end Erdos66RepairChain
