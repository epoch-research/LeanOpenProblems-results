import Submission.LocalDifferencePotentialExplore
import Submission.SummableTailBudgetExplore

/-! A uniform finite local-difference envelope can be imposed alongside any
budgeted finite family of two-sided representation potentials. -/
namespace Erdos66FiniteLocalDifferenceSelection
open AdditiveCombinatorics Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66MixedExponentialSelection Erdos66DifferenceMatching Erdos66LocalDifferencePotential
  Erdos66OrderedPipagePrefix Erdos66Fractional Erdos66SummableTailBudget
open scoped Classical
set_option maxHeartbeats 2400000

 theorem exists_uniform_local_difference_selection : ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ (L : ℕ) (κ : Type*) (T : Finset κ) (n : κ → ℕ) (t w : κ → ℝ),
      (∀ k∈T, 0 ≤ w k) →
      (∑ k∈T, w k*(Real.exp (2*|t k|)*expect (fun i : Fin (L+1) ↦ profile i.val)
        (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ))))) ≤ 1/2 →
      ∃ ω : Fin (L+1) → Bool,
        Brackets (fun i ↦ profile i.val) (fun i ↦ bit (ω i)) ∧
        (∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))) ≤ 1 ∧
        (∀ N d : ℕ, N₀ ≤ N → 2*N ≤ L+1 → 0<d →
          (localDiff (selected L ω) N d : ℝ) ≤ 24*Real.log ((N:ℝ)+2)) := by
  obtain ⟨N₁,hN₁⟩ := exists_tail_budget _ matching_tail_summable (1/2) (by norm_num)
  let N₀ := max 1 N₁
  refine ⟨N₀,le_max_left _ _,?_⟩
  intro L κ T n t w hw hbudget
  let U : Finset (Σ _N : ℕ, ℕ × ℕ) :=
    (Finset.Icc N₀ L).sigma (fun N ↦ (Finset.Ico 1 N) ×ˢ (Finset.range 2))
  let p : Fin (L+1) → ℝ := fun i ↦ profile i.val
  let P : (Fin (L+1) → Bool) → ℝ := fun ω ↦
    ∑ z∈U, Erdos66LocalDifferencePotential.weight z.1*Real.exp ((1/2:ℝ)*matchingCount L z.1 z.2.1 z.2.2 ω)
  let R : (Fin (L+1) → Bool) → ℝ := fun ω ↦
    ∑ k∈T, w k*Real.exp (t k*(sumRep (selected L ω) (n k) : ℝ))
  have hR (ω : Fin (L+1) → Bool) : 0 ≤ R ω :=
    Finset.sum_nonneg (fun k hk ↦ mul_nonneg (hw k hk) (Real.exp_pos _).le)
  have hP (ω : Fin (L+1) → Bool) : 0 ≤ P ω :=
    Finset.sum_nonneg (fun z hz ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hmean : expect p P < 1/2 := by
    change expect p (fun ω ↦ ∑ z∈U, _) < 1/2
    rw [expect_sum]
    simp only [expect_const_mul,U,Finset.sum_sigma,Finset.sum_product]
    calc
      _ ≤ ∑ N∈Finset.Icc N₀ L, 2*(N:ℝ)*(Real.exp 1/((N:ℝ)+2)^5) := by
        apply Finset.sum_le_sum
        intro N hN
        have hterm : (∑ d∈Finset.Ico 1 N, ∑ b∈Finset.range 2,
            Erdos66LocalDifferencePotential.weight N*expect p
              (fun ω ↦ Real.exp ((1/2:ℝ)*matchingCount L N d b ω))) ≤
            ∑ d∈Finset.Ico 1 N, ∑ b∈Finset.range 2, Real.exp 1/((N:ℝ)+2)^5 := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro b hb
          exact harmonic_weighted_mean L N d b (by have := (Finset.mem_Ico.mp hd).1; omega)
        apply hterm.trans
        simp only [Finset.sum_const,Finset.card_range,Nat.card_Ico,nsmul_eq_mul,Nat.cast_ofNat]
        have hh : ((N-1:ℕ):ℝ) ≤ N := by exact_mod_cast (Nat.sub_le N 1)
        have hpos : 0 ≤ 2*(Real.exp 1/((N:ℝ)+2)^5) := by positivity
        have hh' := mul_le_mul_of_nonneg_right hh hpos
        nlinarith only [hh']
      _ < 1/2 := hN₁ _ (fun N hN ↦ (le_max_right 1 N₁).trans (Finset.mem_Icc.mp hN).1)
  obtain ⟨ω,hbr,hcost⟩ := exists_mixed_exponential_selection L U
    (fun z ↦ edgeClass L z.1 z.2.1 z.2.2) (fun _ ↦ pairCoords)
    (fun _ _ ↦ 1) (fun _ ↦ 1/2) (fun z ↦ Erdos66LocalDifferencePotential.weight z.1)
    (fun _ _ _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num) (fun _ _ ↦ (Real.exp_pos _).le)
    T n t w hw p (fun i ↦ ⟨profile_nonneg i.val,profile_le_one i.val⟩)
  simp only [one_mul] at hcost
  have htotal : P ω+R ω < 1 := by
    have hb : expect p P+(∑ k∈T, w k*(Real.exp (2*|t k|)*expect p
        (fun σ ↦ Real.exp (t k*(sumRep (selected L σ) (n k) : ℝ))))) < 1 := by
      linarith only [hmean,hbudget]
    exact hcost.trans_lt hb
  refine ⟨ω,hbr,by have := hP ω; dsimp only [R] at *; linarith only [htotal,this],?_⟩
  intro N d hN₀ hNL hd
  by_cases hdN : N ≤ d
  · rw [localDiff_zero_large _ _ _ hdN,Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  have hNL' : N ≤ L := by have := (le_max_left 1 N₁).trans hN₀; omega
  have hclass (b : ℕ) (hb : b<2) : matchingCount L N d b ω ≤ 12*Real.log ((N:ℝ)+2) := by
    let z : Σ _N : ℕ, ℕ × ℕ := ⟨N,d,b⟩
    have hz : z∈U := by
      dsimp only [z,U]
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hN₀,hNL'⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt hd,lt_of_not_ge hdN⟩,Finset.mem_range.mpr hb⟩⟩
    have hsingle := Finset.single_le_sum (s := U) (a := z)
      (f := fun z ↦ Erdos66LocalDifferencePotential.weight z.1*Real.exp ((1/2:ℝ)*matchingCount L z.1 z.2.1 z.2.2 ω))
      (fun z _ ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hz
    have hpone : P ω < 1 := by have := hR ω; linarith only [htotal,this]
    have hh := hsingle.trans_lt hpone
    change Real.exp (-6*Real.log ((N:ℝ)+2))*Real.exp ((1/2:ℝ)*matchingCount L N d b ω)<1 at hh
    rw [←Real.exp_add,Real.exp_lt_one_iff] at hh
    linarith
  rw [selected_localDiff L N d hNL]
  have h0 := hclass 0 (by norm_num)
  have h1 := hclass 1 (by norm_num)
  linarith

end Erdos66FiniteLocalDifferenceSelection
