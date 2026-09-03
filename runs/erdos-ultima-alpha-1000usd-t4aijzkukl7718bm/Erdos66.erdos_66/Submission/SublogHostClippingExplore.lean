import Submission.SublogDownwardClippingExplore
import Submission.ExactBracketHostClippingExplore

/-! Downward clipping uniformly over all exact-bracket subsets of a common
host with qualitative boundary and sublogarithmic central-triple bounds. -/
namespace Erdos66SublogHostClipping
open Filter AdditiveCombinatorics Erdos66SublogPatternInvariants
  Erdos66SublogDownwardClipping Erdos66JointLogarithmicClipping
  Erdos66BoundaryPairCounts Erdos66CentralTripleCounts
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66OrderedPartialReplacement
open scoped Classical Topology
set_option maxHeartbeats 3200000

lemma log_add_two_le_twice (n : ℕ) (hn : 2 ≤ n) :
    Real.log ((n : ℝ)+2) ≤ 2*Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<(n : ℝ)+2)
    (show (n : ℝ)+2 ≤ (n : ℝ)^2 by nlinarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

lemma smallBoundary_eventually_margin (A : Set ℕ) (hA : SmallBoundary A)
    (c : ℝ) (hc : 0<c) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      2*(boundary B d n).card+6 ≤ ⌊c*Real.log (n : ℝ)⌋₊ := by
  obtain ⟨d,hd,hD⟩ := hA (c/8) (by positivity)
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨d,hd,?_⟩
  filter_upwards [hD,eventually_ge_atTop 2,hlog.eventually_ge_atTop (12/c)] with n hn hn2 hnlog
  intro B hBA
  have hm : ((boundary B d n).card : ℝ) ≤ (boundary A d n).card := by
    exact_mod_cast Finset.card_le_card (boundary_mono hBA d n)
  have hl := log_add_two_le_twice n hn2
  have hlarge : 12 ≤ c*Real.log (n : ℝ) := by
    have hh := (div_le_iff₀ hc).mp hnlog
    nlinarith only [hh]
  have hsmall := mul_le_mul_of_nonneg_left hl (show 0 ≤ c/8 by positivity)
  apply Nat.le_floor
  push_cast
  nlinarith only [hm,hn,hsmall,hlarge]

/-- The host is fixed before the threshold, but the bracket-preserving subset
is chosen afterwards. In particular its own invariant thresholds are not used. -/
theorem host_eventually_uniform_downward_clipping (A : Set ℕ) (K C : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (hboundary : SmallBoundary A) (htriple : SublogCentral A)
    (c ε : ℝ) (hc : 0<c) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      (∀ L, PrefixBrackets profile B L) → ∃ D F : Finset ℕ,
        F.card=D.card ∧ Disjoint (F : Set ℕ) B ∧
        (∀ u∈D∪F, n/5 ≤ u ∧ u ≤ 2*n) ∧
        (∀ L, PrefixBrackets profile (swap B D F) L) ∧
        min (sumRep B n) (⌊c*Real.log (n : ℝ)⌋₊-1) ≤ sumRep (swap B D F) n ∧
        sumRep (swap B D F) n ≤ ⌊c*Real.log (n : ℝ)⌋₊ ∧
        ∀ z, z≠n → |(sumRep (swap B D F) z : ℝ)-sumRep B z| ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨d,hd,hbd⟩ := smallBoundary_eventually_margin A hboundary c hc
  let Q := 2*d^2
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (htriple Q 34 (ε/16) (by positivity))
  let H := max T₀ (max (Q^33) 1)
  have hdp : 0<d^2 := pow_pos (by omega) _
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((uniformly_eventually_downward_clipping_budget K C ε hK hC hε).and
      (hlog.eventually_ge_atTop (12/ε)))
  filter_upwards [hbd,eventually_ge_atTop (d^2*H),eventually_ge_atTop (5*N₀),
    eventually_ge_atTop 32] with n hbdn hnH hn₀ hn32
  intro B hBA hbr
  let N := (n+4)/5
  have hNr : N₀ ≤ N := by dsimp only [N]; omega
  have hnlo : 4*N ≤ n := by dsimp only [N]; omega
  have hnhi : n ≤ 5*N := by dsimp only [N]; omega
  have hNn : N ≤ n := by dsimp only [N]; omega
  have hN6 : 6 ≤ N := by dsimp only [N]; omega
  have hscale : H ≤ n/d^2 := (Nat.le_div_iff_mul_le hdp).mpr (by simpa only [Nat.mul_comm] using hnH)
  have hNT : T₀ ≤ n/d^2 := (le_max_left _ _).trans hscale
  have hQG : Q^33 ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
  have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdp).mp h1
  have hcomp : n ≤ Q*(n/d^2) := central_quotient_comparable d n (by omega) hdn
  have hlogcomp : Real.log ((n/d^2 : ℕ)+2 : ℝ) ≤ 2*Real.log (N : ℝ) := by
    have hdiv : n/d^2 ≤ n := Nat.div_le_self _ _
    have hN6R : (6 : ℝ) ≤ N := by exact_mod_cast hN6
    have hnhiR : (n : ℝ) ≤ 5*N := by exact_mod_cast hnhi
    have hdivR : ((n/d^2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hdiv
    have hh := Real.log_le_log (by positivity : (0 : ℝ)<((n/d^2 : ℕ) : ℝ)+2)
      (show ((n/d^2 : ℕ) : ℝ)+2 ≤ (N : ℝ)^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlarge : 12 ≤ ε*Real.log (N : ℝ) := by
    have hh := (div_le_iff₀ hε).mp (hN₀ N hNr).2
    nlinarith only [hh]
  have htr (z : ℕ) (hz : z ≤ N^33) (hnz : n≠z) :
      4*((fiber B (n/d^2) n z).card : ℝ)+6 ≤ ε*Real.log (N : ℝ) := by
    have hzn : z ≤ n^33 := hz.trans (Nat.pow_le_pow_left hNn 33)
    have hold := hT₀ (n/d^2) hNT n z hcomp
      (hzn.trans (polynomial_horizon Q (n/d^2) n 33 hcomp hQG)) hnz
    have hm : ((fiber B (n/d^2) n z).card : ℝ) ≤ (fiber A (n/d^2) n z).card := by
      exact_mod_cast Finset.card_le_card (Erdos66PatternInsertionDomination.fiber_mono hBA (n/d^2) n z)
    have hh := mul_le_mul_of_nonneg_left hlogcomp (show 0 ≤ ε/16 by positivity)
    nlinarith only [hold,hm,hh,hlarge]
  have henvB (z : ℕ) : (sumRep B z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2) :=
    (show (sumRep B z : ℝ) ≤ sumRep A z by exact_mod_cast Erdos66Explore.sumRep_mono hBA z).trans (henv z)
  obtain ⟨D,F,hFc,hFA,hs,hbr',hlo,hhi,hchange⟩ := (hN₀ N hNr).1 B hbr henvB d n
    ⌊c*Real.log (n : ℝ)⌋₊ hd hnlo hnhi htr (hbdn B hBA)
  refine ⟨D,F,hFc,hFA,?_,hbr',hlo,hhi,hchange⟩
  intro u hu
  have h := hs u hu
  dsimp only [N] at h
  omega

end Erdos66SublogHostClipping
