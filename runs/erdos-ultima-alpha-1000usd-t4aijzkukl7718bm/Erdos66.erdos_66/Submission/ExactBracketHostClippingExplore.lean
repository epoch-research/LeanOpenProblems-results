import Submission.ExactBracketHostEnvelopeExplore
import Submission.ExactBracketDownwardClippingExplore
import Submission.JointLogarithmicClippingExplore

/-! A single exact-bracket host admits downward clipping at any individual
large target, with sublogarithmic collateral everywhere else. The quantifier
order does NOT assert that the clipped sets are the same for different targets. -/
namespace Erdos66ExactBracketHostClipping
open Filter AdditiveCombinatorics Erdos66ExactBracketHostEnvelope
  Erdos66ExactBracketDownwardClipping Erdos66JointLogarithmicClipping
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryPairCounts Erdos66BoundaryPairPotential
  Erdos66BoundaryLogarithmicClipping Erdos66TripleIntersectionMean
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66CentralTripleCounts
  Erdos66OrderedPartialReplacement Erdos66PowerExceptionalProfile
open scoped Classical Topology
set_option maxHeartbeats 3000000

lemma eventually_boundary_margin (A : Set ℕ) (NB : ℕ → ℕ)
    (hA : ∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (cutoff j) n).card:ℝ) ≤
      20*Real.log ((n:ℝ)+1)) (c : ℝ) (hc : 0<c) :
    ∃ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Set ℕ, B ⊆ A →
      2*(boundary B (cutoff j) n).card+6 ≤ ⌊c*Real.log (n:ℝ)⌋₊ := by
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
    hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop (12/c)] with n hN hn hlog1 hlogc
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
  have hlarge : 12 ≤ c*Real.log (n:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlogc
  apply Nat.le_floor
  push_cast
  nlinarith only [hsmall,hlarge]

theorem host_eventually_downward_clipping (A : Set ℕ) (K C : ℝ)
    (NB : ℕ → ℕ) (NT : ℕ → ℕ → ℕ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hbr : ∀ L, PrefixBrackets profile A L)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (hboundary : ∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
      20*Real.log ((n : ℝ)+1))
    (htriple : ∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h)
    (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ D F : Finset ℕ,
      F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
      (∀ u∈D∪F, n/5 ≤ u ∧ u ≤ 2*n) ∧
      (∀ L, PrefixBrackets profile (swap A D F) L) ∧
      min (sumRep A n) (⌊c*Real.log (n : ℝ)⌋₊-1) ≤ sumRep (swap A D F) n ∧
      sumRep (swap A D F) n ≤ ⌊c*Real.log (n : ℝ)⌋₊ ∧
      ∀ z, z≠n → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨j,hj⟩ := eventually_boundary_margin A NB hboundary c hc
  let d := cutoff j
  let Q := 2*d^2
  let H := max (NT Q 34) (max (Q^33) 1)
  have hd : 2 ≤ d := cutoff_ge_two j
  have hdp : 0 < d^2 := pow_pos (by omega) _
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    (uniformly_eventually_downward_clipping K C ε (tripleCap 34) hK hC hε)
  filter_upwards [hj,eventually_ge_atTop (d^2*H),eventually_ge_atTop (5*N₀),
    eventually_ge_atTop 32] with n hbd hnH hn₀ hn32
  let N := (n+4)/5
  have hNr : N₀ ≤ N := by dsimp only [N]; omega
  have hnlo : 4*N ≤ n := by dsimp only [N]; omega
  have hnhi : n ≤ 5*N := by dsimp only [N]; omega
  have hNn : N ≤ n := by dsimp only [N]; omega
  have hscale : H ≤ n/d^2 := (Nat.le_div_iff_mul_le hdp).mpr (by simpa only [Nat.mul_comm] using hnH)
  have hNT : NT Q 34 ≤ n/d^2 := (le_max_left _ _).trans hscale
  have hQG : Q^33 ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
  have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdp).mp h1
  have hcomp : n ≤ Q*(n/d^2) := central_quotient_comparable d n (by omega) hdn
  have htr (z : ℕ) (hz : z ≤ N^33) (hnz : n≠z) :
      (fiber A (n/d^2) n z).card ≤ tripleCap 34 := by
    have hzn : z ≤ n^33 := hz.trans (Nat.pow_le_pow_left hNn 33)
    exact htriple Q 34 (n/d^2) n z hNT hcomp
      (hzn.trans (polynomial_horizon Q (n/d^2) n 33 hcomp hQG)) hnz
  obtain ⟨D,F,hFc,hFA,hs,hbr',hlo,hhi,hchange⟩ := hN₀ N hNr A hbr henv d n
    ⌊c*Real.log (n : ℝ)⌋₊ hd hnlo hnhi htr (hbd A (Set.Subset.refl A))
  refine ⟨D,F,hFc,hFA,?_,hbr',hlo,hhi,hchange⟩
  intro u hu
  have h := hs u hu
  dsimp only [N] at h
  omega

/-- One host; separate finite modifications for each requested center. -/
theorem exists_exact_bracket_host_with_downward_clipping : ∃ A : Set ℕ,
    (∀ L, PrefixBrackets profile A L) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j : ℝ)+1)) n (sumRep A n))) ∧
    ∀ c ε : ℝ, 0 < c → 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ D F : Finset ℕ,
      F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
      (∀ u∈D∪F, n/5 ≤ u ∧ u ≤ 2*n) ∧
      (∀ L, PrefixBrackets profile (swap A D F) L) ∧
      min (sumRep A n) (⌊c*Real.log (n : ℝ)⌋₊-1) ≤ sumRep (swap A D F) n ∧
      sumRep (swap A D F) n ≤ ⌊c*Real.log (n : ℝ)⌋₊ ∧
      ∀ z, z≠n → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨A,K,NB,NT,hK,hbr,henv,hcost,hboundary,htriple⟩ := exists_exact_bracket_host
  exact ⟨A,hbr,hcost,fun c ε hc hε ↦ host_eventually_downward_clipping A K 34 NB NT hK
    (by norm_num) hbr henv hboundary htriple c ε hc hε⟩

end Erdos66ExactBracketHostClipping
