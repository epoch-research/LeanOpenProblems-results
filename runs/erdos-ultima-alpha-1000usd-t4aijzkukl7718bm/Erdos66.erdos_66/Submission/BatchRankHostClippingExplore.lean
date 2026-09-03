import Submission.BatchRankDownwardClippingExplore
import Submission.ExactBracketHostClippingExplore

/-! One exact-bracket host admits simultaneous logarithmic-size clipping
batches. The batch-size constant depends on the requested collateral error. -/
namespace Erdos66BatchRankHostClipping
open Filter AdditiveCombinatorics Erdos66BatchRankDownwardClipping
  Erdos66ExactBracketHostEnvelope Erdos66ExactBracketHostClipping
  Erdos66JointLogarithmicClipping Erdos66JointBoundaryTripleCounts
  Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66CentralTripleCounts
  Erdos66OrderedPartialReplacement Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 4000000

theorem exists_host_with_logarithmic_batches : ∃ A : Set ℕ,
    (∀ L, PrefixBrackets profile A L) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
    ∀ c ε : ℝ, 0 < c → 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ N : ℕ in atTop, ∀ T : Finset ℕ,
        (∀ n∈T, 4*N ≤ n ∧ n ≤ 5*N) → (T.card : ℝ) ≤ ρ*Real.log N →
        ∃ D F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
          (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
          (∀ L, PrefixBrackets profile (swap A D F) L) ∧
          (∀ n∈T, ((min (sumRep A n) (⌊c*Real.log (n : ℝ)⌋₊-1) : ℕ) : ℝ) ≤
              sumRep (swap A D F) n+ε*Real.log ((n : ℝ)+2) ∧
            (sumRep (swap A D F) n : ℝ) ≤ ⌊c*Real.log (n : ℝ)⌋₊+ε*Real.log ((n : ℝ)+2)) ∧
          ∀ z, z∉T → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨A,K,NB,NT,hK,hbr,henv,hcost,hboundary,htriple⟩ := exists_exact_bracket_host
  refine ⟨A,hbr,hcost,?_⟩
  intro c ε hc hε
  let R := tripleCap 34
  let ρ := min 1 (ε/(4*((R : ℝ)+1)))
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρR : 2*(R : ℝ)*ρ ≤ ε/2 := by
    have hh := min_le_right (1 : ℝ) (ε/(4*((R : ℝ)+1)))
    have hh' := (le_div_iff₀ (by positivity : (0 : ℝ)<4*((R : ℝ)+1))).mp hh
    change ρ*(4*((R : ℝ)+1)) ≤ ε at hh'
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  obtain ⟨j,hj⟩ := eventually_boundary_margin A NB hboundary c hc
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hj
  let d := cutoff j
  let Q := 2*d^2
  let H := max (NT Q 34) (max (Q^33) 1)
  have hd : 2 ≤ d := cutoff_ge_two j
  have hdp : 0 < d^2 := pow_pos (by omega) _
  refine ⟨ρ,hρ,?_⟩
  filter_upwards [uniformly_eventually_batch_downward_clipping K 34 ε R hK (by norm_num) hε,
    eventually_ge_atTop N₁,eventually_ge_atTop (d^2*H),eventually_ge_atTop 1]
    with N hb hN₁' hNH hNpos
  intro T hT hcount
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
  have hsize : (T.card : ℝ) ≤ Real.log N := hcount.trans (by nlinarith)
  have hbudget : 2*(R : ℝ)*T.card ≤ (ε/2)*Real.log N := by
    have h1 := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 2*(R : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hρR hlog
    nlinarith only [h1,h2]
  have htr (n : ℕ) (hn : n∈T) (z : ℕ) (hz : z ≤ N^33) (hnz : n≠z) :
      (fiber A (n/d^2) n z).card ≤ R := by
    obtain ⟨hnlo,hnhi⟩ := hT n hn
    have hnH : d^2*H ≤ n := by omega
    have hscale : H ≤ n/d^2 := (Nat.le_div_iff_mul_le hdp).mpr (by simpa only [Nat.mul_comm] using hnH)
    have hNT : NT Q 34 ≤ n/d^2 := (le_max_left _ _).trans hscale
    have hQG : Q^33 ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
    have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
    have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdp).mp h1
    have hcomp : n ≤ Q*(n/d^2) := central_quotient_comparable d n (by omega) hdn
    have hzn : z ≤ n^33 := hz.trans (Nat.pow_le_pow_left (by omega) 33)
    exact htriple Q 34 (n/d^2) n z hNT hcomp
      (hzn.trans (polynomial_horizon Q (n/d^2) n 33 hcomp hQG)) hnz
  have hcap (n : ℕ) (hn : n∈T) : 2*(boundary A d n).card+6 ≤ ⌊c*Real.log (n : ℝ)⌋₊ := by
    have hnlo := (hT n hn).1
    exact hN₁ n (by omega) A (Set.Subset.refl A)
  exact hb A hbr henv T (fun _ ↦ d) (fun n ↦ ⌊c*Real.log (n : ℝ)⌋₊)
    hsize hbudget (fun n hn ↦ ⟨hd,hT n hn⟩) htr hcap

end Erdos66BatchRankHostClipping
