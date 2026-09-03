import Submission.ShortSupportSwapTailExplore
import Submission.ExactBracketHostEnvelopeExplore
import Submission.BoundaryCorrectionEligibilityExplore

/-! A central deletion packet has uniformly bounded collateral at every other
natural target. The bound is independent of its boundary cutoff parameter. -/
namespace Erdos66RemoteCentralDeletion
open Filter AdditiveCombinatorics Erdos66ShortSupportSwapTail
  Erdos66CentralTripleDeletion Erdos66CentralTripleCounts
  Erdos66JointBoundaryTripleCounts Erdos66BoundaryCorrectionEligibility
  Erdos66ClampedPrefixContinuation Erdos66Fractional
  Erdos66OrderedPartialReplacement Erdos66Compactness Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 3000000

lemma quotient_square_window (d n : ℕ) (hd : 2 ≤ d) (hN : 2*d^2 ≤ n/d^2) :
    n ≤ 2*d^2*(n/d^2) ∧ n ≤ (n/d^2)^2 := by
  have hdpos : 0<d^2 := by positivity
  have hdiv := Nat.lt_mul_div_succ n hdpos
  have hq : 1 ≤ n/d^2 := by nlinarith
  constructor <;> nlinarith

lemma central_residual (A : Set ℕ) (d n : ℕ) (hd : 2 ≤ d) :
    sumRep (A\(upperEndpoints A (n/d^2) n : Set ℕ)) n ≤
      2*(Erdos66BoundaryPairCounts.boundary A d n).card+1 := by
  have he := upper_target_exact A (upperEndpoints A (n/d^2) n) (n/d^2) n
    (Finset.Subset.refl _)
  have hc := central_capacity A d n hd
  omega

/-- The single fixed bound works for every boundary parameter d. Only the
threshold at which its packets can be used depends on d. -/
theorem eventually_bounded_central_packet
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (NT : ℕ → ℕ → ℕ)
    (hT : ∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h)
    (d : ℕ) (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℕ, z≠n →
      (hits A (upperEndpoints A (n/d^2) n) z).card ≤ max (tripleCap 66) 3 := by
  have hdiv : Tendsto (fun n : ℕ ↦ n/d^2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by positivity)
  filter_upwards [eventually_harmonic_short_support_tail,
    (tendsto_atTop.mp hdiv) (max (NT (2*d^2) 66) (2*d^2)),
    eventually_ge_atTop 3] with n htail hN hn
  have hNT : NT (2*d^2) 66 ≤ n/d^2 := (le_max_left _ _).trans hN
  have hNq : 2*d^2 ≤ n/d^2 := (le_max_right _ _).trans hN
  obtain ⟨hC,hpow⟩ := quotient_square_window d n hd hNq
  let D := upperEndpoints A (n/d^2) n
  have hDA : (D : Set ℕ) ⊆ A := fun a ha ↦
    (mem_upperEndpoints.mp ha).2.2.2.1
  have hsupport : ∀ a∈D, a ≤ n := fun a ha ↦ (mem_upperEndpoints.mp ha).1
  intro z hzn
  by_cases hz : z ≤ n^33
  · have hpow' : n^33 ≤ (n/d^2)^66 := by
      calc
        _ ≤ ((n/d^2)^2)^33 := Nat.pow_le_pow_left hpow 33
        _ = _ := by rw [←pow_mul]
    have hh := hT (2*d^2) 66 (n/d^2) n z hNT hC (hz.trans hpow') hzn.symm
    exact ((Finset.card_le_card (hits_subset_fiber A D (n/d^2) n z
      (Finset.filter_subset _ _))).trans hh).trans (le_max_left _ _)
  · have hzfar : n^33+1 ≤ z := by omega
    have hs : ∀ a∈D∪∅, a ≤ 15*n := by
      intro a ha
      have hh := hsupport a (by simpa using ha)
      omega
    have he := htail A hbr D ∅ hDA (by simp) hs z hzfar
    have hswap : swap A D ∅=A\(D : Set ℕ) := by simp [swap]
    rw [hswap] at he
    have hmon : sumRep (A\(D : Set ℕ)) z ≤ sumRep A z := sumRep_mono Set.diff_subset z
    have hmon' : (sumRep (A\(D : Set ℕ)) z : ℝ) ≤ sumRep A z := by exact_mod_cast hmon
    rw [abs_of_nonpos (sub_nonpos.mpr hmon')] at he
    have hpow2 : n^2 ≤ n^33 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hzU : 2*(n+1) ≤ z := by nlinarith
    have hzero := supported_self_zero D (n+1) z (fun a ha ↦ by have := hsupport a ha; omega) hzU
    have hid := deletion_identity A D hDA z
    rw [hzero,Nat.add_zero] at hid
    have hid' : (sumRep A z : ℝ)=(sumRep (A\(D : Set ℕ)) z : ℝ)+2*(hits A D z).card := by
      exact_mod_cast hid
    have hb : ((hits A D z).card : ℝ) ≤ 3 := by linarith
    exact (show (hits A D z).card ≤ 3 by exact_mod_cast hb).trans (le_max_right _ _)

end Erdos66RemoteCentralDeletion
