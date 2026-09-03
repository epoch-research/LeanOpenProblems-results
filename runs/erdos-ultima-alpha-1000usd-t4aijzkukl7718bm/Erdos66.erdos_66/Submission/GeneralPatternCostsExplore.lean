import Submission.PositivePatternCompactnessExplore
import Submission.BernoulliCostSelectionExplore

/-! Countably many positive polynomial pattern constraints retained jointly
with the full two-sided harmonic representation-cost family. -/
namespace Erdos66GeneralPatternCosts
open Filter AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66NaturalPositivePattern Erdos66PositivePatternCompactness
  Erdos66Fractional
  Erdos66PrefixBalancedUpperLimit Erdos66SummableTailBudget Erdos66BernoulliCostSelection
  Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 2200000

variable {β : Type*} [Fintype β]

 theorem exists_general_pattern_rep_costs
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (patterns : ℕ → Pattern)
    (hpatterns : ∀ S : Finset ℕ, (∑ j∈S, (patterns j).eval p) ≤ 1/4)
    (cost : ℕ → ℕ → ℝ → ℝ) (g : ℕ → ℕ → ℝ)
    (w t : ℕ → ℕ → β → ℝ)
    (hw : ∀ j n b, 0≤w j n b) (ht : ∀ j n b, |t j n b|≤1/2)
    (hrep : ∀ j n x, cost j n x=∑ b, w j n b*Real.exp (t j n b*x))
    (hg : ∀ j, Summable (g j))
    (hbound : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ L, n≤L →
      expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ cost j n (sumRep (selected L ω) n))≤g j n) :
    ∃ A : Set ℕ,
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      (∀ S : Finset ℕ, (∑ j∈S, (patterns j).value (fun i ↦ decide (i∈A))) ≤ 1) ∧
      (∀ j, Summable (fun n ↦ cost j n (sumRep A n))) := by
  have hcont (j n : ℕ) : Continuous (cost j n) := by
    have he : cost j n=(fun x ↦ ∑ b, w j n b*Real.exp (t j n b*x)) := funext (hrep j n)
    rw [he]
    fun_prop
  have hpos (j n : ℕ) (x : ℝ) : 0≤cost j n x := by
    rw [hrep]
    exact Finset.sum_nonneg (fun b _ ↦ mul_nonneg (hw j n b) (Real.exp_pos _).le)
  have hN (j : ℕ) : ∃ N : ℕ,
      (∀ n≥N, ∀ L, n≤L → expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ cost j n (sumRep (selected L ω) n))≤g j n) ∧
      (∀ S : Finset ℕ, (∀ n∈S, N≤n) → (∑ n∈S, Real.exp 1*g j n)<(1/2:ℝ)^j/4) := by
    obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (hbound j)
    obtain ⟨N₂,h₂⟩ := exists_tail_budget _ ((hg j).mul_left (Real.exp 1)) ((1/2:ℝ)^j/4) (by positivity)
    exact ⟨max N₁ N₂,fun n hn L hL ↦ h₁ n ((le_max_left _ _).trans hn) L hL,
      fun S hS ↦ h₂ S (fun n hn ↦ (le_max_right _ _).trans (hS n hn))⟩
  choose N hNb hNs using hN
  let trim : ℕ → ℕ → ℝ → ℝ := fun j n x ↦ if N j≤n then cost j n x else 0
  have htpos (j n : ℕ) (x : ℝ) : 0≤trim j n x := by
    dsimp [trim]
    split_ifs; exact hpos j n x; exact le_rfl
  have htcont (j n : ℕ) : Continuous (trim j n) := by
    by_cases hn : N j≤n
    · simpa only [trim,if_pos hn] using hcont j n
    · simp only [trim,if_neg hn]; exact continuous_const
  have hfinite (L : ℕ) : ∃ A : Set ℕ,
      (∀ k≤L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, p i)|≤1) ∧
      (∑ j∈Finset.range L, (patterns j).value (fun i ↦ decide (i∈A))) ≤ 1 ∧
      (∀ j≤L, ∀ K≤L, (∑ n∈Finset.range K, trim j n (sumRep A n))≤1) := by
    let C₀ := max L ((Finset.range L).sup (fun j ↦ (patterns j).bound))
    have hLC : L ≤ C₀ := le_max_left _ _
    let pL : Fin (C₀+1) → ℝ := fun i ↦ p i.val
    let P : (Fin (C₀+1) → Bool) → ℝ := fun ω ↦
      ∑ j∈Finset.range (L+1), ∑ n∈Finset.range (L+1), trim j n (sumRep (selected C₀ ω) n)
    let T : Finset (ℕ × ℕ × β) := (Finset.range (L+1)) ×ˢ ((Finset.range (L+1)) ×ˢ Finset.univ)
    let W : ℕ × ℕ × β → ℝ := fun z ↦ if N z.1≤z.2.1 then w z.1 z.2.1 z.2.2 else 0
    let τ : ℕ × ℕ × β → ℝ := fun z ↦ t z.1 z.2.1 z.2.2
    let target : ℕ × ℕ × β → ℕ := fun z ↦ z.2.1
    have hW (z : ℕ × ℕ × β) : 0≤W z := by
      dsimp [W]
      split_ifs; exact hw _ _ _; exact le_rfl
    have hsum (ω : Fin (C₀+1) → Bool) :
        (∑ z∈T, W z*Real.exp (τ z*(sumRep (selected C₀ ω) (target z) : ℝ)))=P ω := by
      dsimp only [T,W,τ,target,P]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnj : N j≤n
      · simp only [if_pos hnj,trim,hrep]
      · simp only [if_neg hnj,trim,zero_mul,Finset.sum_const_zero]
    have hexpect : (∑ z∈T, W z*expect pL
        (fun ω ↦ Real.exp (τ z*(sumRep (selected C₀ ω) (target z) : ℝ))))=expect pL P := by
      simp_rw [←expect_const_mul]
      rw [←expect_sum]
      simp_rw [hsum]
    have hcomp : (∑ z∈T, W z*(Real.exp (2*|τ z|)*expect pL
        (fun σ ↦ Real.exp (τ z*(sumRep (selected C₀ σ) (target z) : ℝ))))) ≤
        Real.exp 1*expect pL P := by
      rw [←hexpect,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hm : 0≤expect pL (fun σ ↦ Real.exp (τ z*(sumRep (selected C₀ σ) (target z) : ℝ))) := by
        have hh := expect_mono pL (fun i ↦ hp i.val) (fun _ ↦ 0)
          (fun σ ↦ Real.exp (τ z*(sumRep (selected C₀ σ) (target z) : ℝ))) (fun σ ↦ (Real.exp_pos _).le)
        simpa only [expect_const] using hh
      have he : Real.exp (2*|τ z|)≤Real.exp 1 := Real.exp_le_exp.mpr (by have := ht z.1 z.2.1 z.2.2; dsimp [τ]; linarith)
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hm) (hW z)
      simpa only [mul_left_comm] using hh
    have hrow (j : ℕ) : Real.exp 1*expect pL (fun ω ↦ ∑ n∈Finset.range (L+1),
        trim j n (sumRep (selected C₀ ω) n))≤(1/2:ℝ)^j/4 := by
      rw [expect_sum,Finset.mul_sum]
      calc
        _ ≤ ∑ n∈Finset.range (L+1), if N j≤n then Real.exp 1*g j n else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hnj : N j≤n
          · simp only [trim,if_pos hnj]
            exact mul_le_mul_of_nonneg_left (hNb j n hnj C₀ (by have := Finset.mem_range.mp hn; omega)) (Real.exp_pos 1).le
          · simp only [trim,if_neg hnj,expect_const,mul_zero,le_refl]
        _ = ∑ n∈(Finset.range (L+1)).filter (fun n ↦ N j≤n), Real.exp 1*g j n :=
          (Finset.sum_filter _ _).symm
        _ ≤ (1/2:ℝ)^j/4 := (hNs j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
    have hP : Real.exp 1*expect pL P ≤ 1/2 := by
      change Real.exp 1*expect pL (fun ω ↦ ∑ j∈Finset.range (L+1), _) ≤ 1/2
      rw [expect_sum,Finset.mul_sum]
      exact (Finset.sum_le_sum (fun j _ ↦ hrow j)).trans (row_budget L)
    obtain ⟨ω,hbr,hcost⟩ := exists_pattern_selection C₀ (Finset.range L) patterns
      (fun j hj ↦ (Finset.le_sup (f := fun j ↦ (patterns j).bound) hj).trans (le_max_right _ _)) T target τ W (fun z _ ↦ hW z)
      p hp
    have hpatpos : 0 ≤ ∑ j∈Finset.range L, (patterns j).value (fun i ↦ decide (i∈selected C₀ ω)) :=
      Finset.sum_nonneg (fun j _ ↦ (patterns j).value_nonneg _)
    have hreprpos : 0 ≤ P ω := Finset.sum_nonneg (fun j _ ↦ Finset.sum_nonneg (fun n _ ↦ htpos j n _))
    have htotal : (∑ j∈Finset.range L, (patterns j).value (fun i ↦ decide (i∈selected C₀ ω)))+P ω ≤ 3/4 := by
      rw [hsum] at hcost
      have hh := hpatterns (Finset.range L)
      have hb := hcomp.trans hP
      linarith only [hcost,hh,hb]
    have hchoice : P ω ≤ 1 := by linarith only [htotal,hpatpos]
    refine ⟨selected C₀ ω,fun k hk ↦ finite_prefix_bound C₀ p ω hbr k (by omega),
      by linarith only [htotal,hreprpos],?_⟩
    intro j hj K hK
    have h₁ : (∑ n∈Finset.range K, trim j n (sumRep (selected C₀ ω) n))≤
        ∑ n∈Finset.range (L+1), trim j n (sumRep (selected C₀ ω) n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ ↦ htpos j n _)
    have h₂ : (∑ n∈Finset.range (L+1), trim j n (sumRep (selected C₀ ω) n))≤P ω :=
      Finset.single_le_sum (s := Finset.range (L+1)) (a := j)
        (f := fun k ↦ ∑ n∈Finset.range (L+1), trim k n (sumRep (selected C₀ ω) n))
        (fun k _ ↦ Finset.sum_nonneg (fun n _ ↦ htpos k n _)) (Finset.mem_range.mpr (by omega))
    exact (h₁.trans h₂).trans hchoice
  obtain ⟨A,hbr,hpatterns,hA⟩ := exists_summable_costs_with_patterns p patterns trim htcont htpos hfinite
  refine ⟨A,hbr,hpatterns,fun j ↦ (hA j).congr_cofinite ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (N j)] with n hn
  simp only [trim,if_pos hn]

end Erdos66GeneralPatternCosts
