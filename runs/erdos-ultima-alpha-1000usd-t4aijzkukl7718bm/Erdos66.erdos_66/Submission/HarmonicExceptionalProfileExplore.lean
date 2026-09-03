import Submission.ScaledFractionalTailExplore
import Submission.BiasedTailPotentialExplore
import Submission.SummableTailBudgetExplore
import Submission.SummableCostCompactnessExplore

/-! A fixed logarithmic coefficient with harmonically summable exceptional
targets at each fixed tolerance. This does not eliminate the exceptional targets. -/
namespace Erdos66HarmonicExceptionalProfile
open Filter AdditiveCombinatorics Erdos66ScaledFractionalTail
  Erdos66BiasedTailPotential Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli
  Erdos66SummableTailBudget Erdos66SummableCostCompactness
  Erdos66VariableBernoulliBounds
open scoped Topology Classical
set_option maxHeartbeats 2000000

noncomputable def tailBound (c δ : ℝ) (n : ℕ) : ℝ :=
  2 / ((n:ℝ)+2)^(1+δ^2*c/128 : ℝ)

lemma tailBound_summable (c δ : ℝ) (hc : 0<c) (hδ : 0<δ) :
    Summable (tailBound c δ) := by
  have hs := (Real.summable_one_div_nat_add_rpow 2 (1+δ^2*c/128)).mpr
    (by
      have : 0<δ^2*c/128 := by positivity
      linarith)
  have hh := hs.mul_left 2
  simpa only [tailBound,abs_of_nonneg (by positivity : (0:ℝ)≤(↑(_:ℕ):ℝ)+2),mul_one_div]
    using hh

lemma weighted_exp_le_tailBound (c δ : ℝ) (hc : 0≤c) (n : ℕ) (hn : 2≤n) :
    2*Real.exp (-δ^2*(c*Real.log n)/64)/((n:ℝ)+2) ≤ tailBound c δ n := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hshift : Real.log ((n:ℝ)+2) ≤ 2*Real.log n := by
    have hh := Real.log_le_log (by positivity : 0<(n:ℝ)+2)
      (show (n:ℝ)+2≤(n:ℝ)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hcomp : -δ^2*(c*Real.log n)/64 ≤ -Real.log ((n:ℝ)+2)*(δ^2*c/128) := by
    have hh := mul_le_mul_of_nonneg_left hshift (show 0≤δ^2*c/128 by positivity)
    nlinarith
  have he : 2*Real.exp (-Real.log ((n:ℝ)+2)*(δ^2*c/128))/((n:ℝ)+2) =
      tailBound c δ n := by
    unfold tailBound
    rw [Real.rpow_add (by positivity),Real.rpow_one,Real.rpow_def_of_pos (by positivity)]
    rw [neg_mul,Real.exp_neg]
    field_simp
  rw [←he]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcomp) (by norm_num)) (by positivity)

lemma uniform_weighted_potential_bound (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (c : ℝ) (hc : 0<c)
    (ht : Tendsto (fun n ↦ sumConv p p n/Real.log n) atTop (𝓝 c))
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ N : ℕ, 2≤N ∧ ∀ n≥N, ∀ L, n≤L →
      expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ potential δ (c*Real.log n) (sumRep (selected L ω) n)/((n:ℝ)+2)) ≤
      tailBound c δ n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (uniform_mean_approximation p hp c ht (δ*c/2) (by positivity))
  refine ⟨max 2 N,le_max_left _ _,fun n hn L hL ↦ ?_⟩
  have hn2 : 2≤n := (le_max_left _ _).trans hn
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hh := hN n ((le_max_right _ _).trans hn) L hL
  have hbias : |repMean L n (fun i ↦ p i.val)-c*Real.log n| ≤
      δ*(c*Real.log n)/2 := by
    have he : repMean L n (fun i ↦ p i.val)/Real.log n-c =
        (repMean L n (fun i ↦ p i.val)-c*Real.log n)/Real.log n := by field_simp
    rw [he,abs_div,abs_of_pos hln] at hh
    have hh' := (div_lt_iff₀ hln).mp hh
    nlinarith
  have hm : repMean L n (fun i ↦ p i.val) ≤ 2*(c*Real.log n) := by
    have hb := (abs_le.mp hbias).2
    have hh' := mul_le_mul_of_nonneg_right hδ1 (show 0≤c*Real.log n by positivity)
    nlinarith
  have he := expect_potential_bound (fun i : Fin (L+1) ↦ p i.val)
    (fun ω ↦ (sumRep (selected L ω) n : ℝ)) (repMean L n (fun i ↦ p i.val))
    (c*Real.log n) δ hδ hδ1 hm hbias
    (fun t ht ↦ rep_mgf L n (fun i ↦ p i.val) (fun i ↦ hp i.val) t ht)
  have heq : expect (fun i : Fin (L+1) ↦ p i.val)
      (fun ω ↦ potential δ (c*Real.log n) (sumRep (selected L ω) n)/((n:ℝ)+2)) =
      expect (fun i : Fin (L+1) ↦ p i.val)
      (fun ω ↦ potential δ (c*Real.log n) (sumRep (selected L ω) n))/((n:ℝ)+2) := by
    simp_rw [div_eq_mul_inv,mul_comm _ (((n:ℝ)+2)⁻¹)]
    rw [expect_const_mul]
  rw [heq]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (weighted_exp_le_tailBound c δ hc.le n hn2)

lemma geometric_budget (L : ℕ) :
    (∑ j ∈ Finset.range (L+1), (1/2:ℝ)^j/4) ≤ 1/2 := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).div_const 4
  have hb := Summable.sum_le_tsum (Finset.range (L+1)) (fun j _ ↦ by positivity) hs
  rw [tsum_div_const,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)] at hb
  norm_num at hb ⊢
  exact hb

/-- The common potential witness before extracting exceptional sets.
All thresholds are fixed in advance of the finite cutoffs. -/
theorem exists_summable_potentials (c : ℝ) (hc : 0<c) :
    ∃ (A : Set ℕ) (N : ℕ → ℕ), (∀ j, 2≤N j) ∧ ∀ j, Summable (fun n : ℕ ↦
      if N j≤n then potential (1/((j:ℝ)+1)) (c*Real.log n) (sumRep A n)/((n:ℝ)+2)
      else 0) := by
  obtain ⟨p,hp,hconv⟩ := exists_scaled_probability_profile c hc
  let δ : ℕ → ℝ := fun j ↦ 1/((j:ℝ)+1)
  have hδ (j : ℕ) : 0<δ j := by dsimp [δ]; positivity
  have hδ1 (j : ℕ) : δ j≤1 := by dsimp [δ]; apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hN (j : ℕ) : ∃ N : ℕ, 2≤N ∧
      (∀ n≥N, ∀ L, n≤L →
        expect (fun i : Fin (L+1) ↦ p i.val)
          (fun ω ↦ potential (δ j) (c*Real.log n) (sumRep (selected L ω) n)/((n:ℝ)+2)) ≤
        tailBound c (δ j) n) ∧
      (∀ S : Finset ℕ, (∀ n∈S, N≤n) →
        (∑ n∈S, tailBound c (δ j) n) < (1/2:ℝ)^j/4) := by
    obtain ⟨N₁,hN₁,h₁⟩ := uniform_weighted_potential_bound p hp c hc hconv (δ j) (hδ j) (hδ1 j)
    obtain ⟨N₂,h₂⟩ := exists_tail_budget _ (tailBound_summable c (δ j) hc (hδ j))
      ((1/2:ℝ)^j/4) (by positivity)
    refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_,?_⟩
    · intro n hn L hL
      exact h₁ n ((le_max_left _ _).trans hn) L hL
    · intro S hS
      exact h₂ S (fun n hn ↦ (le_max_right _ _).trans (hS n hn))
  choose N hN2 hNmean hNbudget using hN
  let cost : ℕ → ℕ → ℝ → ℝ := fun j n x ↦
    if N j≤n then potential (δ j) (c*Real.log n) x/((n:ℝ)+2) else 0
  have hcostpos (j n : ℕ) (x : ℝ) : 0≤cost j n x := by
    dsimp [cost]
    split_ifs
    · exact div_nonneg (potential_nonneg _ _ _) (by positivity)
    · exact le_rfl
  have hcostcont (j n : ℕ) : Continuous (cost j n) := by
    by_cases hn : N j≤n
    · simp only [cost,if_pos hn]
      exact (potential_continuous _ _).div_const _
    · simp only [cost,if_neg hn]
      exact continuous_const
  have hfinite (L : ℕ) : ∃ A : Set ℕ, ∀ j≤L, ∀ K≤L,
      (∑ n∈Finset.range K, cost j n (sumRep A n)) ≤ 1 := by
    let pL : Fin (L+1) → ℝ := fun i ↦ p i.val
    let P : (Fin (L+1) → Bool) → ℝ := fun ω ↦
      ∑ j∈Finset.range (L+1), ∑ n∈Finset.range (L+1), cost j n (sumRep (selected L ω) n)
    have hrow (j : ℕ) :
        expect pL (fun ω ↦ ∑ n∈Finset.range (L+1), cost j n (sumRep (selected L ω) n)) ≤
        (1/2:ℝ)^j/4 := by
      rw [expect_sum]
      calc
        _ ≤ ∑ n∈Finset.range (L+1), if N j≤n then tailBound c (δ j) n else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hnj : N j≤n
          · simp only [cost,if_pos hnj]
            exact hNmean j n hnj L (by have := Finset.mem_range.mp hn; omega)
          · simp only [cost,if_neg hnj,expect_const]
            exact le_rfl
        _ = ∑ n∈(Finset.range (L+1)).filter (fun n ↦ N j≤n), tailBound c (δ j) n :=
          (Finset.sum_filter _ _).symm
        _ ≤ (1/2:ℝ)^j/4 := (hNbudget j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
    have hP : expect pL P < 1 := by
      change expect pL (fun ω ↦ ∑ j∈Finset.range (L+1), _) < 1
      rw [expect_sum]
      exact ((Finset.sum_le_sum (fun j _ ↦ hrow j)).trans (geometric_budget L)).trans_lt (by norm_num)
    obtain ⟨ω,hw,hω⟩ := exists_positive_weight_lt pL (fun i ↦ hp i.val) P 1 hP
    refine ⟨selected L ω,fun j hj K hK ↦ ?_⟩
    have h₁ : (∑ n∈Finset.range K, cost j n (sumRep (selected L ω) n)) ≤
        ∑ n∈Finset.range (L+1), cost j n (sumRep (selected L ω) n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun n _ _ ↦ hcostpos j n _)
    have h₂ : (∑ n∈Finset.range (L+1), cost j n (sumRep (selected L ω) n)) ≤ P ω :=
      Finset.single_le_sum (s := Finset.range (L+1)) (a := j)
        (f := fun k ↦ ∑ n∈Finset.range (L+1), cost k n (sumRep (selected L ω) n))
        (fun k _ ↦ Finset.sum_nonneg (fun n _ ↦ hcostpos k n _))
        (Finset.mem_range.mpr (by omega))
    exact (h₁.trans h₂).trans hω.le
  obtain ⟨A,hA⟩ := exists_summable_costs cost hcostcont hcostpos hfinite
  exact ⟨A,N,hN2,hA⟩

/-- Potentials at every positive reciprocal-integer tolerance control
harmonic sums of bad targets for any positive error tolerance. -/
lemma exceptions_of_summable_potentials (A : Set ℕ) (c : ℝ) (N : ℕ → ℕ)
    (hN2 : ∀ j, 2≤N j)
    (hA : ∀ j, Summable (fun n : ℕ ↦
      if N j≤n then potential (1/((j:ℝ)+1)) (c*Real.log n) (sumRep A n)/((n:ℝ)+2)
      else 0)) :
    ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0) := by
  let δ : ℕ → ℝ := fun j ↦ 1/((j:ℝ)+1)
  let cost : ℕ → ℕ → ℝ → ℝ := fun j n x ↦
    if N j≤n then potential (δ j) (c*Real.log n) x/((n:ℝ)+2) else 0
  have hδ (j : ℕ) : 0<δ j := by dsimp [δ]; positivity
  have hcostpos (j n : ℕ) (x : ℝ) : 0≤cost j n x := by
    dsimp [cost]
    split_ifs
    · exact div_nonneg (potential_nonneg _ _ _) (by positivity)
    · exact le_rfl
  intro ε hε
  have hδlim : Tendsto (fun j ↦ δ j*c) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const c
  obtain ⟨j,hj⟩ := (hδlim.eventually_lt_const hε).exists
  apply (hA j).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (N j)] with n hn
  by_cases hb : ε ≤ |(sumRep A n : ℝ)/Real.log n-c|
  · simp only [if_pos hb,Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/((n:ℝ)+2))]
    change 1/((n:ℝ)+2) ≤ cost j n (sumRep A n)
    dsimp only [cost]
    rw [if_pos hn]
    have hln : 0<Real.log (n:ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1<n by have := hN2 j; omega))
    have hbad : δ j*(c*Real.log n) ≤ |(sumRep A n : ℝ)-c*Real.log n| := by
      have hh := mul_le_mul_of_nonneg_right (hj.le.trans hb) hln.le
      have he : (sumRep A n : ℝ)-c*Real.log n =
          ((sumRep A n : ℝ)/Real.log n-c)*Real.log n := by field_simp
      rw [he,abs_mul,abs_of_pos hln]
      nlinarith
    exact div_le_div_of_nonneg_right (one_le_potential _ _ _ (hδ j).le hbad) (by positivity)
  · simp only [if_neg hb,norm_zero]
    exact hcostpos j n _

/-- One fixed coefficient and all tolerances simultaneously. The exceptional
set for each tolerance has a finite harmonic sum, not necessarily finite size. -/
theorem exists_harmonically_summable_exceptions (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ, ∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0) := by
  obtain ⟨A,N,hN,hA⟩ := exists_summable_potentials c hc
  exact ⟨A,exceptions_of_summable_potentials A c N hN hA⟩

end Erdos66HarmonicExceptionalProfile
