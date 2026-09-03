import Submission.JointBoundaryTripleCountsExplore
import Submission.BoundaryLogarithmicClippingExplore

/-! One harmonic rounding admits logarithmic downward clipping from EVERY
subset, with constant collateral over any fixed polynomial target horizon.
This local theorem does not control the accumulation of infinitely many
corrections and does not prove an all-target lower asymptotic. -/
namespace Erdos66JointLogarithmicClipping
open Filter AdditiveCombinatorics Erdos66JointBoundaryTripleCounts
  Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential Erdos66TripleIntersectionMean
  Erdos66BoundaryCorrectionEligibility Erdos66BoundaryLogarithmicClipping
  Erdos66CentralTripleCounts Erdos66CentralTripleDeletion
  Erdos66Generating Erdos66Rounding Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 2200000

lemma eventually_joint_boundary_cap (A : Set ℕ) (NB : ℕ → ℕ)
    (hA : ∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤
      20*Real.log ((n:ℝ)+1)) (c : ℝ) (hc : 0<c) :
    ∃ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      2*(boundary B (cutoff j) n).card+2 ≤ ⌊c*Real.log (n:ℝ)⌋₊ := by
  let j := ⌈240/c⌉₊
  have hj : 240 ≤ c*((j:ℝ)+1) := by
    have hh : 240/c ≤ (j:ℝ) := Nat.le_ceil _
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith only [hh',hc]
  have ht : (0:ℝ) < (j:ℝ)+1 := by positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨j,?_⟩
  filter_upwards [eventually_ge_atTop (NB j),eventually_ge_atTop 1,
    hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (4/c)] with n hN hn hlog1 hlogc
  intro B hBA
  have hmono : ((boundary B (cutoff j) n).card:ℝ) ≤ (boundary A (cutoff j) n).card :=
    by exact_mod_cast Finset.card_le_card (boundary_mono hBA (cutoff j) n)
  have hB0 := (mul_le_mul_of_nonneg_left hmono ht.le).trans (hA j n hN)
  have hB : ((j:ℝ)+1)*((boundary B (cutoff j) n).card:ℝ) ≤ 20*ell n := by
    dsimp only [ell]
    linarith only [hB0]
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

lemma central_quotient_comparable (d n : ℕ) (hd : 0<d) (hn : d^2 ≤ n) :
    n ≤ (2*d^2)*(n/d^2) := by
  have hd2 : 0<d^2 := pow_pos hd _
  have hdiv : 1 ≤ n/d^2 := (Nat.le_div_iff_mul_le hd2).mpr (by simpa using hn)
  have hmod := Nat.mod_lt n hd2
  have he := Nat.div_add_mod n (d^2)
  nlinarith only [hdiv,hmod,he]

lemma polynomial_horizon (C N n g : ℕ) (hn : n ≤ C*N) (hC : C^g ≤ N) : n^g ≤ N^(g+1) := by
  calc
    _ ≤ (C*N)^g := Nat.pow_le_pow_left hn g
    _ = C^g*N^g := mul_pow _ _ _
    _ ≤ N*N^g := Nat.mul_le_mul_right _ hC
    _ = _ := by rw [pow_succ,mul_comm]

lemma fiber_mono {A B : Set ℕ} (hAB : A ⊆ B) (N n z : ℕ) : fiber A N n z ⊆ fiber B N n z := by
  intro a ha
  obtain ⟨han,hNa,hNb,haz,ha,hb,hc⟩ := mem_fiber.mp ha
  exact mem_fiber.mpr ⟨han,hNa,hNb,haz,hAB ha,hAB hb,hAB hc⟩

 theorem exists_uniform_central_log_clipping : ∃ A : Set ℕ,
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ c : ℝ, 0<c → ∀ g : ℕ, ∃ d N₀ : ℕ, 2 ≤ d ∧
      ∀ n≥N₀, ∀ B : Set ℕ, B ⊆ A → ∃ D : Finset ℕ,
        D ⊆ upperEndpoints B (n/d^2) n ∧
        sumRep (B\(D : Set ℕ)) n ≤ ⌊c*Real.log (n:ℝ)⌋₊ ∧
        min (sumRep B n) (⌊c*Real.log (n:ℝ)⌋₊-1) ≤ sumRep (B\(D : Set ℕ)) n ∧
        ∀ z, z ≤ n^g → n≠z → sumRep B z-sumRep (B\(D : Set ℕ)) z ≤ 2*tripleCap (g+1)) := by
  obtain ⟨A,NB,NT,hbr,hcost,hboundary,htriple⟩ := exists_joint_boundary_triple_rounding
  refine ⟨A,hbr,hcost,?_⟩
  intro c hc g
  obtain ⟨j,hj⟩ := eventually_joint_boundary_cap A NB hboundary c hc
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hj
  let d := cutoff j
  let C := 2*d^2
  let K := max (NT C (g+1)) (max (C^g) 1)
  let N₀ := max N₁ (d^2*K)
  have hd : 2 ≤ d := cutoff_ge_two j
  have hdpos : 0<d^2 := pow_pos (by omega) _
  refine ⟨d,N₀,hd,?_⟩
  intro n hn B hBA
  have hn' : max N₁ (d^2*K) ≤ n := hn
  have hscale : K ≤ n/d^2 := (Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith only [le_max_right N₁ (d^2*K),hn'])
  have hNT : NT C (g+1) ≤ n/d^2 := (le_max_left _ _).trans hscale
  have hCG : C^g ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
  have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdpos).mp h1
  have hcomp : n ≤ C*(n/d^2) := central_quotient_comparable d n (by omega) hdn
  obtain ⟨D,hD,hupper,hlower⟩ := exists_central_clipping B d n ⌊c*Real.log (n:ℝ)⌋₊ hd
    (hN₁ n (by omega) B hBA)
  refine ⟨D,hD,hupper,hlower,?_⟩
  intro z hz hnz
  have hzh : z ≤ (n/d^2)^(g+1) := hz.trans (polynomial_horizon C (n/d^2) n g hcomp hCG)
  have hcap := htriple C (g+1) (n/d^2) n z hNT hcomp hzh hnz
  have hmono := Finset.card_le_card (fiber_mono hBA (n/d^2) n z)
  have hloss := one_target_loss B D (n/d^2) n z (hD.trans (Finset.filter_subset _ _))
  omega

end Erdos66JointLogarithmicClipping
