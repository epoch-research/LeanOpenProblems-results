import Submission.PowerComparableCofactors
import Submission.BothLargePrimeBound
import Submission.SmallNearTieDensity

/-! Endpoint-scale near-tie events, and finite estimates on their small- and
large-prime portions. These estimates assert no comparison symmetry. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

/-- The two largest prime factors differ by at most `δ * log N` in their
logarithms (away from the harmless zero values). -/
def logRatioEvent (N : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^δ * Nat.maxPrimeFac (n+1) ∧
    (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^δ * Nat.maxPrimeFac n

noncomputable instance (N : ℕ) (δ : ℝ) (n : ℕ) : Decidable (logRatioEvent N δ n) :=
  Classical.propDecidable _

noncomputable def logRatioSet (N : ℕ) (δ : ℝ) : Finset ℕ :=
  (range N).filter (logRatioEvent N δ)

noncomputable def lowLogRatioSet (N : ℕ) (α δ : ℝ) : Finset ℕ :=
  (range N).filter fun n => 1 < n ∧
    (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^α ∧
    (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^α ∧ logRatioEvent N δ n

noncomputable def highLogRatioSet (N : ℕ) (β δ : ℝ) : Finset ℕ :=
  (range N).filter fun n => 1 < n ∧
    (N : ℝ)^β ≤ (Nat.maxPrimeFac n : ℝ) ∧
    (N : ℝ)^β ≤ (Nat.maxPrimeFac (n+1) : ℝ) ∧ logRatioEvent N δ n

lemma logRatioEvent_to_factorRatioEvent (N n : ℕ) (δ : ℝ)
    (h : logRatioEvent N δ n) : factorRatioEvent ⌈(N : ℝ)^δ⌉₊ n := by
  constructor
  · have hm := mul_le_mul_of_nonneg_right (Nat.le_ceil ((N : ℝ)^δ))
      (Nat.cast_nonneg (α := ℝ) (Nat.maxPrimeFac (n+1)))
    exact_mod_cast h.1.trans hm
  · have hm := mul_le_mul_of_nonneg_right (Nat.le_ceil ((N : ℝ)^δ))
      (Nat.cast_nonneg (α := ℝ) (Nat.maxPrimeFac n))
    exact_mod_cast h.2.trans hm

lemma highLogRatioSet_subset (N : ℕ) (β δ η : ℝ) (hN : 1 < N) (hηβ : η < β) :
    highLogRatioSet N β δ ⊆
      comparableCofactorPrimeSet N ⌈(N : ℝ)^δ⌉₊ ⌊(N : ℝ)^(1-β)⌋₊ ⌊(N : ℝ)^η⌋₊ := by
  intro n hn
  obtain ⟨hnN,hn2,hp,hq,hcomp⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hA := primeCofactor_le_power_cutoff N n (by omega) (by omega) (1-β) (by simpa using hp)
  have hB := primeCofactor_le_power_cutoff N (n+1) (by omega) (by omega) (1-β) (by simpa using hq)
  have hz : (⌊(N : ℝ)^η⌋₊ : ℝ) < (N : ℝ)^β :=
    (Nat.floor_le (Real.rpow_nonneg hN0.le η)).trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hN1 hηβ)
  have hc := logRatioEvent_to_factorRatioEvent N n δ hcomp
  apply boundedCofactorNearTieSet_subset
  apply mem_filter.mpr
  exact ⟨mem_Icc.mpr ⟨by omega,by omega⟩,Nat.le_floor hA,Nat.le_floor hB,hc.1,hc.2,
    by exact_mod_cast hz.trans_le hp,by exact_mod_cast hz.trans_le hq⟩

lemma highLogRatioSet_eventually_le (β δ η : ℝ)
    (hβ : β ≤ 1) (hδ : 0 ≤ δ) (hη : 0 < η) (hgap : 2*(1-β)+64*η < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((highLogRatioSet N β δ).card : ℝ)/N ≤
      (8*Real.exp 19*(1-β)/η^2)*δ+ε := by
  filter_upwards [comparableCofactorPrimeSet_power_eventually_le (1-β) δ η (by linarith) hδ hη hgap ε hε,
    eventually_gt_atTop (1 : ℕ)] with N hb hN
  have hc := Nat.cast_le (α := ℝ) |>.mpr (card_le_card
    (highLogRatioSet_subset N β δ η hN (by linarith)))
  exact (div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)).trans hb

lemma lowLogRatioSet_card_bound (N A : ℕ) (α δ : ℝ) :
    ((lowLogRatioSet N α δ).card : ℝ) ≤
      (((range N).filter fun n => Nat.maxPrimeFac (n+1) ≤ (⌈(N : ℝ)^δ⌉₊+1)*2^A).card : ℝ) +
      N*comparablePrimeMass ⌈(N : ℝ)^δ⌉₊ A ⌊(N : ℝ)^α⌋₊ + (⌊(N : ℝ)^α⌋₊ : ℝ)^2 := by
  classical
  let C := ⌈(N : ℝ)^δ⌉₊
  let D := ⌊(N : ℝ)^α⌋₊
  have hs : lowLogRatioSet N α δ ⊆
      (range N).filter (fun n => Nat.maxPrimeFac (n+1) ≤ (C+1)*2^A) ∪ smallPrimeRatioSet N C A D := by
    intro n hn
    obtain ⟨hnN,hn,hp,hq,hcomp⟩ := mem_filter.mp hn
    have hc := logRatioEvent_to_factorRatioEvent N n δ hcomp
    by_cases hsmall : Nat.maxPrimeFac (n+1) ≤ (C+1)*2^A
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,hsmall⟩)
    · apply mem_union_right
      have hqA : 2^A ≤ Nat.maxPrimeFac (n+1) := by nlinarith
      have hpA : 2^A ≤ Nat.maxPrimeFac n := by
        have hc' : Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n := hc.2
        by_contra hpA
        have hh := Nat.mul_le_mul_left C (show Nat.maxPrimeFac n ≤ 2^A by omega)
        nlinarith
      exact mem_filter.mpr ⟨hnN,hn,
        mem_primesAbovePower.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,hpA,Nat.le_floor hp⟩,
        mem_primesAbovePower.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),hqA,Nat.le_floor hq⟩,hc⟩
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hs).trans (card_union_le _ _))
  push_cast at hc
  have hb := smallPrimeRatioSet_card_le N C A D
  linarith

#print axioms highLogRatioSet_eventually_le
#print axioms lowLogRatioSet_card_bound
end FiniteSieve
end Erdos371
