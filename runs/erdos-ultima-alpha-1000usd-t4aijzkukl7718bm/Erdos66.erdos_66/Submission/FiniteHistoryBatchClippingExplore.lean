import Submission.FiniteHistoryIncidenceExplore
import Submission.BoundaryMarginAllowanceExplore
import Submission.BatchRankDownwardClippingExplore
import Submission.AnnulusExtensionExplore

/-! Logarithmic-size clipping batches remain available after arbitrary finite
history, provided the original exact brackets are retained. The batch-size
constant is independent of that history; its waiting threshold is not. -/
namespace Erdos66FiniteHistoryBatchClipping
open Filter AdditiveCombinatorics Erdos66FiniteHistoryIncidence
  Erdos66BoundaryMarginAllowance Erdos66BatchRankDownwardClipping
  Erdos66ExactBracketHostEnvelope Erdos66JointLogarithmicClipping
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66BoundaryPairMean Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66CentralTripleCounts Erdos66OrderedPartialReplacement Erdos66PowerExceptionalProfile
  Erdos66AnnulusExtension
open scoped Classical Topology
set_option maxHeartbeats 5000000

theorem exists_host_with_finite_history_batches : ∃ A : Set ℕ,
    (∀ L, PrefixBrackets profile A L) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
    ∀ c ε : ℝ, 0 < c → 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ U : ℕ, ∀ᶠ N : ℕ in atTop, U < N ∧
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
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp uniformly_eventually_history_incidence
  let d := cutoff j
  let Q := 2*d^2
  have hd : 2 ≤ d := cutoff_ge_two j
  have hdp : 0 < d^2 := pow_pos (by omega) _
  refine ⟨ρ,hρ,?_⟩
  intro U
  let W := max U W₀
  let H := max (W^32) (max (NT Q 34) (max (Q^33) 1))
  let K' : ℝ := K+2*U
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  filter_upwards [uniformly_eventually_batch_downward_clipping K' 34 ε R hK' (by norm_num) hε,
    eventually_ge_atTop N₁,eventually_ge_atTop (d^2*H),eventually_ge_atTop (U+1)]
    with N hb hN₁' hNH hNU
  refine ⟨by omega,?_⟩
  intro B hbrB hagree T hT hcount
  have henvB (z : ℕ) : (sumRep B z : ℝ) ≤ K'+34*Real.log ((z : ℝ)+2) := by
    have hh := (abs_le.mp (sumRep_eq_tail_error B A U z hagree)).2
    have he := henv z
    dsimp only [K']
    linarith
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hsize : (T.card : ℝ) ≤ Real.log N := hcount.trans (by nlinarith)
  have hbudget : 2*(R : ℝ)*T.card ≤ (ε/2)*Real.log N := by
    have h1 := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2*(R : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hρR hlog
    nlinarith only [h1,h2]
  have hscale (n : ℕ) (hn : n∈T) : H ≤ n/d^2 := by
    have hnlo := (hT n hn).1
    apply (Nat.le_div_iff_mul_le hdp).mpr
    have hh : d^2*H ≤ n := by omega
    simpa only [Nat.mul_comm] using hh
  have hwait (n : ℕ) (hn : n∈T) : W^32 ≤ n/d^2 :=
    (le_max_left _ _).trans (hscale n hn)
  have hhistory (n : ℕ) (hn : n∈T) := hW₀ W (le_max_right _ _) A B hbr U
    (le_max_left _ _) hagree (n/d^2) (hwait n hn)
  have htr (n : ℕ) (hn : n∈T) (z : ℕ) (hz : z ≤ N^33) (hnz : n≠z) :
      (fiber B (n/d^2) n z).card ≤ R := by
    obtain ⟨hnlo,hnhi⟩ := hT n hn
    have hbase : max (NT Q 34) (max (Q^33) 1) ≤ n/d^2 :=
      (le_max_right _ _).trans (hscale n hn)
    have hNT : NT Q 34 ≤ n/d^2 := (le_max_left _ _).trans hbase
    have hQG : Q^33 ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hbase)
    have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hbase)
    have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdp).mp h1
    have hcomp : n ≤ Q*(n/d^2) := central_quotient_comparable d n (by omega) hdn
    have hzn : z ≤ n^33 := hz.trans (Nat.pow_le_pow_left (by omega) 33)
    have hbasecap := htriple Q 34 (n/d^2) n z hNT hcomp
      (hzn.trans (polynomial_horizon Q (n/d^2) n 33 hcomp hQG)) hnz
    exact ((hhistory n hn).1 n z).trans (Nat.add_le_add_right hbasecap 2)
  have hcap (n : ℕ) (hn : n∈T) : 2*(boundary B d n).card+6 ≤ ⌊c*Real.log (n : ℝ)⌋₊ := by
    have hnlo := (hT n hn).1
    have hbasecap := hN₁ n (by omega) A (Set.Subset.refl A)
    have hhist := (hhistory n hn).2 d n hd (quotient_half d n hd)
    change 2*(boundary A d n).card+10 ≤ _ at hbasecap
    omega
  exact hb B hbrB henvB T (fun _ ↦ d) (fun n ↦ ⌊c*Real.log (n : ℝ)⌋₊)
    hsize hbudget (fun n hn ↦ ⟨hd,hT n hn⟩) htr hcap

end Erdos66FiniteHistoryBatchClipping
