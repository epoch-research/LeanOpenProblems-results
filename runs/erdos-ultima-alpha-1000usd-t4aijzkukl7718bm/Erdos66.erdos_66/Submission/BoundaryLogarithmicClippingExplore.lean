import Submission.BoundaryCorrectionEligibilityExplore

/-! Every positive logarithmic cap is eventually attainable by a central
finite deletion from every subset of one boundary-controlled rounding.
No control of the accumulated loss at other targets is claimed. -/
namespace Erdos66BoundaryLogarithmicClipping
open Filter AdditiveCombinatorics Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66BoundaryCorrectionEligibility Erdos66BoundarySparsePowerProfile
  Erdos66TripleIntersectionMean Erdos66CentralTripleDeletion
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma ell_le_three_log {n : ℕ} (hn : 1 ≤ n) (hlog : 1 ≤ Real.log (n:ℝ)) :
    ell n ≤ 3*Real.log (n:ℝ) := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0:ℝ) < n := by linarith
  have hh := Real.log_le_log (by positivity : (0:ℝ) < (n:ℝ)+1)
    (show (n:ℝ)+1 ≤ 2*(n:ℝ) by linarith)
  rw [Real.log_mul (by norm_num) hp.ne'] at hh
  have h2 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
  dsimp only [ell]
  linarith

lemma eventually_boundary_below_cap (A : Set ℕ) (N₀ : ℕ → ℕ)
    (hA : ∀ j n, N₀ j ≤ n → ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤ 3*ell n)
    (c : ℝ) (hc : 0<c) : ∃ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      2*(boundary B (cutoff j) n).card+2 ≤ ⌊c*Real.log (n:ℝ)⌋₊ := by
  let j := ⌈36/c⌉₊
  have hj : 36 ≤ c*((j:ℝ)+1) := by
    have hh : 36/c ≤ (j:ℝ) := Nat.le_ceil _
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh',hc]
  have ht : (0:ℝ) < (j:ℝ)+1 := by positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨j,?_⟩
  filter_upwards [eventually_ge_atTop (N₀ j),eventually_ge_atTop 1,
    hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (4/c)] with n hN hn hlog1 hlogc
  intro B hBA
  have hmono : ((boundary B (cutoff j) n).card:ℝ) ≤ (boundary A (cutoff j) n).card :=
    by exact_mod_cast Finset.card_le_card (boundary_mono hBA (cutoff j) n)
  have hB := (mul_le_mul_of_nonneg_left hmono ht.le).trans (hA j n hN)
  have hell := ell_le_three_log hn hlog1
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hscale := mul_le_mul_of_nonneg_right hj hlog0
  have hsmall : 2*((boundary B (cutoff j) n).card:ℝ) ≤ c/2*Real.log (n:ℝ) := by
    apply le_of_mul_le_mul_left (a := (j:ℝ)+1) _ ht
    nlinarith only [hB,hell,hscale]
  have hlarge : 4 ≤ c*Real.log (n:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlogc
  apply Nat.le_floor
  push_cast
  nlinarith only [hsmall,hlarge]

 theorem exists_rounding_with_logarithmic_clipping : ∃ A : Set ℕ,
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ c : ℝ, 0<c → ∃ d N : ℕ, 2 ≤ d ∧ ∀ n≥N, ∀ B : Set ℕ, B ⊆ A →
      ∃ D : Finset ℕ, D ⊆ upperEndpoints B (n/d^2) n ∧
        sumRep (B\(D : Set ℕ)) n ≤ ⌊c*Real.log (n:ℝ)⌋₊ ∧
        min (sumRep B n) (⌊c*Real.log (n:ℝ)⌋₊-1) ≤ sumRep (B\(D : Set ℕ)) n) := by
  obtain ⟨A,N₀,hbr,hboundary,hcost⟩ := exists_boundary_sparse_power_potentials
  refine ⟨A,hbr,hcost,?_⟩
  intro c hc
  obtain ⟨j,hj⟩ := eventually_boundary_below_cap A N₀ hboundary c hc
  obtain ⟨N,hN⟩ := eventually_atTop.mp hj
  refine ⟨cutoff j,N,cutoff_ge_two j,?_⟩
  intro n hn B hBA
  exact exists_central_clipping B (cutoff j) n ⌊c*Real.log (n:ℝ)⌋₊ (cutoff_ge_two j) (hN n hn B hBA)

end Erdos66BoundaryLogarithmicClipping
