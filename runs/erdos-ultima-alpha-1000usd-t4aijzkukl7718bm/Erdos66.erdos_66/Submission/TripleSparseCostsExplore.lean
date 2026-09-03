import Submission.TripleIntersectionCompactnessExplore
import Submission.BernoulliCostSelectionExplore

/-! One infinite harmonic rounding with two-sided summable costs, prefix
discrepancy, and polynomial-horizon central triple bounds. -/
namespace Erdos66TripleSparseCosts
open Filter AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66FiniteTripleIntersectionSelection Erdos66TripleIntersectionCompactness
  Erdos66CentralTripleCounts Erdos66Fractional
  Erdos66PrefixBalancedUpperLimit Erdos66SummableTailBudget Erdos66BernoulliCostSelection
  Erdos66Generating
open scoped Classical Topology
set_option maxHeartbeats 2200000

variable {β : Type*} [Fintype β]

 theorem exists_triple_sparse_summable_rep_costs
    (cost : ℕ → ℕ → ℝ → ℝ) (g : ℕ → ℕ → ℝ)
    (w t : ℕ → ℕ → β → ℝ)
    (hw : ∀ j n b, 0≤w j n b) (ht : ∀ j n b, |t j n b|≤1/2)
    (hrep : ∀ j n x, cost j n x=∑ b, w j n b*Real.exp (t j n b*x))
    (hg : ∀ j, Summable (g j))
    (hbound : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ L, n≤L →
      expect (fun i : Fin (L+1) ↦ profile i.val)
        (fun ω ↦ cost j n (sumRep (selected L ω) n))≤g j n) :
    ∃ (A : Set ℕ) (N₀ : ℕ → ℕ),
      (∀ k, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, profile i)|≤1) ∧
      (∀ h N n z, N₀ h ≤ N → n ≤ 4*N → z ≤ N^h → n≠z →
        (fiber A N n z).card ≤ 36*(h+4)+2) ∧
      (∀ j, Summable (fun n ↦ cost j n (sumRep A n))) := by
  have hp (i : ℕ) : 0 ≤ profile i ∧ profile i ≤ 1 := ⟨profile_nonneg i,profile_le_one i⟩
  have hcont (j n : ℕ) : Continuous (cost j n) := by
    have he : cost j n=(fun x ↦ ∑ b, w j n b*Real.exp (t j n b*x)) := funext (hrep j n)
    rw [he]
    fun_prop
  have hpos (j n : ℕ) (x : ℝ) : 0≤cost j n x := by
    rw [hrep]
    exact Finset.sum_nonneg (fun b _ ↦ mul_nonneg (hw j n b) (Real.exp_pos _).le)
  have hN (j : ℕ) : ∃ N : ℕ,
      (∀ n≥N, ∀ L, n≤L → expect (fun i : Fin (L+1) ↦ profile i.val)
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
  obtain ⟨N₀,hN₀,hselect⟩ := exists_uniform_triple_selection
  have hfinite (L : ℕ) : ∃ A : Set ℕ,
      (∀ k≤L, |(∑ i∈Finset.range k, indicator A i)-(∑ i∈Finset.range k, profile i)|≤1) ∧
      (∀ h ≤ L, ∀ N ≤ L, ∀ n z, N₀ h ≤ N → n ≤ 4*N → z ≤ N^h → n≠z →
        (fiber A N n z).card ≤ 36*(h+4)+2) ∧
      (∀ j≤L, ∀ K≤L, (∑ n∈Finset.range K, trim j n (sumRep A n))≤1) := by
    let pL : Fin (2*L+1) → ℝ := fun i ↦ profile i.val
    let P : (Fin (2*L+1) → Bool) → ℝ := fun ω ↦
      ∑ j∈Finset.range (L+1), ∑ n∈Finset.range (L+1), trim j n (sumRep (selected (2*L) ω) n)
    let T : Finset (ℕ × ℕ × β) := (Finset.range (L+1)) ×ˢ ((Finset.range (L+1)) ×ˢ Finset.univ)
    let W : ℕ × ℕ × β → ℝ := fun z ↦ if N z.1≤z.2.1 then w z.1 z.2.1 z.2.2 else 0
    let τ : ℕ × ℕ × β → ℝ := fun z ↦ t z.1 z.2.1 z.2.2
    let target : ℕ × ℕ × β → ℕ := fun z ↦ z.2.1
    have hW (z : ℕ × ℕ × β) : 0≤W z := by
      dsimp [W]
      split_ifs; exact hw _ _ _; exact le_rfl
    have hsum (ω : Fin (2*L+1) → Bool) :
        (∑ z∈T, W z*Real.exp (τ z*(sumRep (selected (2*L) ω) (target z) : ℝ)))=P ω := by
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
        (fun ω ↦ Real.exp (τ z*(sumRep (selected (2*L) ω) (target z) : ℝ))))=expect pL P := by
      simp_rw [←expect_const_mul]
      rw [←expect_sum]
      simp_rw [hsum]
    have hcomp : (∑ z∈T, W z*(Real.exp (2*|τ z|)*expect pL
        (fun σ ↦ Real.exp (τ z*(sumRep (selected (2*L) σ) (target z) : ℝ))))) ≤
        Real.exp 1*expect pL P := by
      rw [←hexpect,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have hm : 0≤expect pL (fun σ ↦ Real.exp (τ z*(sumRep (selected (2*L) σ) (target z) : ℝ))) := by
        have hh := expect_mono pL (fun i ↦ hp i.val) (fun _ ↦ 0)
          (fun σ ↦ Real.exp (τ z*(sumRep (selected (2*L) σ) (target z) : ℝ))) (fun σ ↦ (Real.exp_pos _).le)
        simpa only [expect_const] using hh
      have he : Real.exp (2*|τ z|)≤Real.exp 1 := Real.exp_le_exp.mpr (by have := ht z.1 z.2.1 z.2.2; dsimp [τ]; linarith)
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hm) (hW z)
      simpa only [mul_left_comm] using hh
    have hrow (j : ℕ) : Real.exp 1*expect pL (fun ω ↦ ∑ n∈Finset.range (L+1),
        trim j n (sumRep (selected (2*L) ω) n))≤(1/2:ℝ)^j/4 := by
      rw [expect_sum,Finset.mul_sum]
      calc
        _ ≤ ∑ n∈Finset.range (L+1), if N j≤n then Real.exp 1*g j n else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hnj : N j≤n
          · simp only [trim,if_pos hnj]
            exact mul_le_mul_of_nonneg_left (hNb j n hnj (2*L) (by have := Finset.mem_range.mp hn; omega)) (Real.exp_pos 1).le
          · simp only [trim,if_neg hnj,expect_const,mul_zero,le_refl]
        _ = ∑ n∈(Finset.range (L+1)).filter (fun n ↦ N j≤n), Real.exp 1*g j n :=
          (Finset.sum_filter _ _).symm
        _ ≤ (1/2:ℝ)^j/4 := (hNs j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
    have hP : Real.exp 1*expect pL P ≤ 1/2 := by
      change Real.exp 1*expect pL (fun ω ↦ ∑ j∈Finset.range (L+1), _) ≤ 1/2
      rw [expect_sum,Finset.mul_sum]
      exact (Finset.sum_le_sum (fun j _ ↦ hrow j)).trans (row_budget L)
    obtain ⟨ω,hbr,hcost,hdiff⟩ := hselect (2*L) L (ℕ × ℕ × β) T target τ W (fun z _ ↦ hW z) (hcomp.trans hP)
    have hchoice : P ω ≤ 1 := by simpa only [hsum] using hcost
    refine ⟨selected (2*L) ω,fun k hk ↦ finite_prefix_bound (2*L) profile ω hbr k (by omega),
      fun h hh N hN n z hN₀ hn hz hnz ↦
        selected_fiber_bound (2*L) N n z (36*(h+4)) ω hnz (hdiff h hh N hN n z hN₀ hn hz),?_⟩
    intro j hj K hK
    have h₁ : (∑ n∈Finset.range K, trim j n (sumRep (selected (2*L) ω) n))≤
        ∑ n∈Finset.range (L+1), trim j n (sumRep (selected (2*L) ω) n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ ↦ htpos j n _)
    have h₂ : (∑ n∈Finset.range (L+1), trim j n (sumRep (selected (2*L) ω) n))≤P ω :=
      Finset.single_le_sum (s := Finset.range (L+1)) (a := j)
        (f := fun k ↦ ∑ n∈Finset.range (L+1), trim k n (sumRep (selected (2*L) ω) n))
        (fun k _ ↦ Finset.sum_nonneg (fun n _ ↦ htpos k n _)) (Finset.mem_range.mpr (by omega))
    exact (h₁.trans h₂).trans hchoice
  obtain ⟨A,hbr,hdiff,hA⟩ := exists_summable_costs_with_triples profile N₀ trim htcont htpos hfinite
  refine ⟨A,N₀,hbr,hdiff,fun j ↦ (hA j).congr_cofinite ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (N j)] with n hn
  simp only [trim,if_pos hn]

end Erdos66TripleSparseCosts
