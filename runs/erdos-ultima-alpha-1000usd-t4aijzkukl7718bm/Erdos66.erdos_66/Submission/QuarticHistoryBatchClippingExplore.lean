import Submission.FiniteHistoryIncidenceExplore
import Submission.BoundaryMarginAllowanceExplore
import Submission.CenterCapBatchClippingExplore
import Submission.FiniteHistoryRepresentationExplore
import Submission.AnnulusExtensionExplore

/-! Finite-history batches with a fourth-power support waiting bound.
There is no history-dependent global representation-envelope constant. -/
namespace Erdos66QuarticHistoryBatchClipping
open Filter AdditiveCombinatorics Erdos66FiniteHistoryIncidence
  Erdos66BoundaryMarginAllowance Erdos66CenterCapBatchClipping Erdos66FiniteHistoryRepresentation
  Erdos66PredecessorScaleBudget Erdos66PredecessorCutoffTransfer
  Erdos66ExactBracketHostEnvelope Erdos66JointLogarithmicClipping
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66BoundaryPairMean Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66CentralTripleCounts Erdos66OrderedPartialReplacement Erdos66PowerExceptionalProfile
  Erdos66AnnulusExtension
open scoped Classical Topology
set_option maxHeartbeats 5000000

theorem exists_host_with_quartic_history_batches : ∃ A : Set ℕ,
    (∀ L, PrefixBrackets profile A L) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
    ∀ c ε : ℝ, 0 < c → 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∃ J : ℕ, 2 ≤ J ∧ ∀ U N : ℕ, (max U J)^4 ≤ N → U < N ∧
        ∀ B : Set ℕ, (∀ L, PrefixBrackets profile B L) →
          (∀ a, U ≤ a → (a∈B ↔ a∈A)) →
          ∀ T : Finset ℕ, (∀ n∈T, 4*N ≤ n ∧ n ≤ 5*N) → (T.card : ℝ) ≤ ρ*Real.log N →
          ∃ D F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) B ∧
            (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
            (∀ L, PrefixBrackets profile (swap B D F) L) ∧
            (∀ n∈T, ((min (sumRep B n) (⌊c*Real.log (n : ℝ)⌋₊-1) : ℕ) : ℝ) ≤
                sumRep (swap B D F) n+ε*Real.log ((n : ℝ)+2) ∧
              (sumRep (swap B D F) n : ℝ) ≤ ⌊c*Real.log (n : ℝ)⌋₊+ε*Real.log ((n : ℝ)+2)) ∧
            ∀ z, z∉T → |(sumRep (swap B D F) z : ℝ)-sumRep B z| ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨A,K,NB,NT,hK,hbr,henv,hcost,hboundary,htriple⟩ := exists_exact_bracket_host
  refine ⟨A,hbr,hcost,?_⟩
  intro c ε hc hε
  let R := tripleCap 34+2
  let ρ := min 1 (ε/(4*((R : ℝ)+1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρR : 2*(R : ℝ)*ρ ≤ ε/2 := by
    have hh := min_le_right (1 : ℝ) (ε/(4*((R : ℝ)+1)))
    have hh' := (le_div_iff₀ (by positivity : (0 : ℝ)<4*((R : ℝ)+1))).mp hh
    change ρ*(4*((R : ℝ)+1)) ≤ ε at hh'
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  obtain ⟨j,hj⟩ := eventually_boundary_allowance A NB hboundary c hc 10
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hj
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp eventually_cubic_history_mass
  let d := cutoff j
  let Q := 2*d^2
  have hd : 2 ≤ d := cutoff_ge_two j
  have hdp : 0 < d^2 := pow_pos (by omega) _
  let M : ℝ := K+34*((33 : ℕ)+6)+5
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have htlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((uniformly_eventually_batch_downward_clipping M ε R hM hε).and
      ((htlog.eventually_ge_atTop 1).and (eventually_ge_atTop 32)))
  let J := max 2 (max N₀ (max W₀ (max N₁ (max (NT Q 34) (max (Q^33) (d^2))))))
  have hJ : 2 ≤ J ∧ N₀ ≤ J ∧ W₀ ≤ J ∧ N₁ ≤ J ∧ NT Q 34 ≤ J ∧ Q^33 ≤ J ∧ d^2 ≤ J := by
    dsimp only [J]
    omega
  refine ⟨ρ,hρ,J,hJ.1,?_⟩
  intro U N hWN
  let W := max U J
  have hW2 : 2 ≤ W := hJ.1.trans (le_max_right _ _)
  have hW4 : W < W^4 := by
    have hh := Nat.pow_le_pow_right (by omega : 0 < W) (show 2 ≤ 4 by norm_num)
    have hsq : W < W^2 := by nlinarith
    omega
  have hW3 : W ≤ W^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < W) (show 1 ≤ 3 by norm_num)
  have hW4N : W^4 ≤ N := hWN
  have hUW : U ≤ W := le_max_left _ _
  have hJW : J ≤ W := le_max_right _ _
  obtain ⟨hb,hl,hN⟩ := hN₀ N (by omega)
  refine ⟨by omega,?_⟩
  intro B hbrB hagree T hT hcount
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsize : (T.card : ℝ) ≤ Real.log N := hcount.trans (by nlinarith)
  have hbudget : 2*(R : ℝ)*T.card ≤ (ε/2)*Real.log N := by
    have h1 := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2*(R : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hρR hlog
    nlinarith only [h1,h2]
  have hwait (n : ℕ) (hn : n∈T) : W^3 ≤ n/d^2 := by
    have hnlo := (hT n hn).1
    have hdW : d^2 ≤ W := hJ.2.2.2.2.2.2.trans hJW
    have hprod : d^2*W^3 ≤ N := calc
      _ ≤ W*W^3 := Nat.mul_le_mul_right _ hdW
      _ = W^4 := by ring
      _ ≤ N := hW4N
    apply (Nat.le_div_iff_mul_le hdp).mpr
    nlinarith
  have hmass (n : ℕ) (hn : n∈T) := hW₀ W (hJ.2.2.1.trans hJW) U (n/d^2) hUW (hwait n hn)
  have hrep (n : ℕ) (hn : n∈T) : (sumRep B n : ℝ) ≤ M*Real.log N := by
    have hnhi := (hT n hn).2
    have hp := Nat.pow_le_pow_right (by omega : 0 < N) (show 2 ≤ 33 by norm_num)
    have hlow : 5*N ≤ N^2 := by nlinarith
    have hbase := finite_profile_envelope A K 34 hK (by norm_num) henv N 33 (by omega) hl n
    rw [cutoff_rep A (by omega)] at hbase
    have hh := (abs_le.mp (representation_after_history A B hbr U (n/d^2) n
      (hmass n hn).1 (quotient_half d n hd) (hmass n hn).2 hagree)).2
    dsimp only [M]
    nlinarith
  have htr (n : ℕ) (hn : n∈T) (z : ℕ) (hz : z ≤ N^33) (hnz : n≠z) :
      (fiber B (n/d^2) n z).card ≤ R := by
    obtain ⟨hnlo,hnhi⟩ := hT n hn
    have hNT : NT Q 34 ≤ n/d^2 := hJ.2.2.2.2.1.trans (hJW.trans (hW3.trans (hwait n hn)))
    have hQG : Q^33 ≤ n/d^2 := hJ.2.2.2.2.2.1.trans (hJW.trans (hW3.trans (hwait n hn)))
    have h1 : 1 ≤ n/d^2 := by have := hwait n hn; omega
    have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdp).mp h1
    have hcomp : n ≤ Q*(n/d^2) := central_quotient_comparable d n (by omega) hdn
    have hzn : z ≤ n^33 := hz.trans (Nat.pow_le_pow_left (by omega) 33)
    have hbasecap := htriple Q 34 (n/d^2) n z hNT hcomp
      (hzn.trans (polynomial_horizon Q (n/d^2) n 33 hcomp hQG)) hnz
    exact (fiber_after_history A B hbr U (n/d^2) n z (hmass n hn).1 (hmass n hn).2 hagree).trans
      (Nat.add_le_add_right hbasecap 2)
  have hcap (n : ℕ) (hn : n∈T) : 2*(boundary B d n).card+6 ≤ ⌊c*Real.log (n : ℝ)⌋₊ := by
    have hnlo := (hT n hn).1
    have hN1 : N₁ ≤ n := by have := hJ.2.2.2.1; omega
    have hbasecap := hN₁ n hN1 A (Set.Subset.refl A)
    have hhist := boundary_after_history A B hbr U (n/d^2) d n (hmass n hn).1
      (quotient_half d n hd) hd (hmass n hn).2 hagree
    change 2*(boundary A d n).card+10 ≤ _ at hbasecap
    omega
  exact hb B hbrB T (fun _ ↦ d) (fun n ↦ ⌊c*Real.log (n : ℝ)⌋₊)
    hrep hsize hbudget (fun n hn ↦ ⟨hd,hT n hn⟩) htr hcap

end Erdos66QuarticHistoryBatchClipping
