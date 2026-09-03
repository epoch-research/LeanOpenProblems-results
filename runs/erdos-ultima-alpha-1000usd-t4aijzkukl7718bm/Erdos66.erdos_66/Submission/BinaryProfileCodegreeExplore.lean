import Submission.BinarySignedProfileExplore
import Submission.TripleCodegreeConcentrationExplore

/-! A binary signed profile with simultaneous, uniform off-diagonal codegree
control. The original profile and the codegrees refer to the same set D. -/
namespace Erdos66BinaryProfileCodegree
open AdditiveCombinatorics Erdos66RealWeightedCharacterEnergy Erdos66WeightedProfileCharacter
  Erdos66SignedRepBernoulli Erdos66FiniteRepBernoulli Erdos66RandomConstantProfile
  Erdos66AffineRootAggregate Erdos66SharedParameterKernel Erdos66ExceptionalPairDeletion
  Erdos66TripleCodegreeConcentration
open scoped Classical
set_option maxHeartbeats 2200000

theorem exists_binary_signed_profile_codegrees (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (s q₀ L R : ℕ) (hpL : 4*(L+1)<p) (μ ε t : ℝ) (ht : 0<t)
    (hμ : 1 ≤ μ) (hε : 0<ε) (hε1 : ε ≤ 1) (hlarge : 8 ≤ ε*μ)
    (hs : μ ≤ (s : ℝ)+1)
    (hstart : 64*(s : ℝ)^2 ≤ ε^2*((q₀ : ℝ)+1))
    (hsmall : 6*(2*(L : ℝ)+1)*Real.exp (-ε^2*(μ+1)/512) +
      (2*(L : ℝ)+1)^2*Real.exp ((2-(R : ℝ))*t+
        (Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) < 1) :
    ∃ (a : ZMod p) (T D : Finset ℕ), D ⊆ Finset.range (L+1) ∧
      (∀ i<L+1, a+(i : ZMod p) ≠ 0) ∧
      (∀ q<2*(L+1), 2*a+(q : ZMod p) ≠ 0) ∧
      (T.card : ℝ) ≤ 128*(1+Real.log ((L+1 : ℕ) : ℝ))^2/ε^2 ∧
      (∀ q∈T, ε*((s : ℝ)+1)<4*((q : ℝ)+1)) ∧
      (∀ q, (sumRep (D : Set ℕ) q : ℝ) ≤ (1+ε)*μ) ∧
      (∀ q, q₀ ≤ q → q ≤ L → |(sumRep (D : Set ℕ) q : ℝ)-μ| < ε*μ) ∧
      (∀ q, q ≤ 2*L → q∉T → |signedFiber (L+1) (selectedWeight D) a q| < ε*μ) ∧
      ∀ b q, b≠q → codegree D b q ≤ R := by
  have hμp : 0<μ := by linarith
  obtain ⟨a,ha,hop,hbad⟩ := exists_profile_translation p hp s (L+1) hpL μ hμp
  let T := badTargets (L+1) (profileWeight μ s) a ((ε/4)*μ)
  have hT : (T.card : ℝ) ≤ 128*(1+Real.log ((L+1 : ℕ) : ℝ))^2/ε^2 := by
    have hh := hbad (ε/4) (by positivity)
    convert hh using 1 <;> ring
  have hloc : ∀ q∈T, ε*((s : ℝ)+1)<4*((q : ℝ)+1) := by
    intro q hq
    have hh := Erdos66LateBadTargets.badTargets_location p μ (ε/4) hμp s L a q hq
    linarith
  let σ : ℕ → ℝ := fun i ↦ (quadraticChar (ZMod p) (a+i) : ℝ)
  have hσ (i : ℕ) : |σ i| ≤ 1 := by
    dsimp [σ]
    have hh := Erdos66FiniteField.quadraticChar_abs_le_one (a+(i : ZMod p))
    exact_mod_cast hh
  have hprob := probability_bounds μ s L hμp.le hs
  have hsmall' : 6*((2*L : ℕ)+(1 : ℝ))*Real.exp (-(ε/8)^2*(μ+1)/8) +
      (((2*L : ℕ) : ℝ)+1)^2*Real.exp ((2-(R : ℝ))*t+
        (Real.exp (9*t)-1)*(μ*Real.sqrt μ*Erdos66ConstantProfile.b s)) < 1 := by
    convert hsmall using 1 <;> push_cast <;> congr 2 <;> ring
  obtain ⟨ω,hω,hcd⟩ := exists_unsigned_signed_codegree L (2*L) R s μ (ε/8) t hμp.le hs
    (by positivity) (by linarith) ht σ hσ hsmall'
  let D := selectedFinset L ω
  have hD : D ⊆ Finset.range (L+1) := selectedFinset_subset L ω
  have hDcoe : (D : Set ℕ)=selected L ω := coe_selectedFinset L ω
  have hDsupport : ∀ n∈(D : Set ℕ), n ≤ L := by
    intro n hn
    have hh := Finset.mem_range.mp (hD hn)
    omega
  have hdev : (ε/8)*(μ+1) ≤ ε*μ/4 := by nlinarith
  refine ⟨a,T,D,hD,ha,hop,hT,hloc,?_,?_,?_,codegrees_extend D L R hD hcd⟩
  · intro q
    by_cases hq : q ≤ 2*L
    · have hh := (abs_lt.mp (hω q hq).1).2
      have hm := mean_upper μ s L q hμp.le hs
      rw [hDcoe]
      nlinarith
    · rw [rep_zero_above_support (D : Set ℕ) L q hDsupport (by omega),Nat.cast_zero]
      positivity
  · intro q hq₀ hq
    have hh := (hω q (by omega)).1
    have hl := mean_lower μ s L q hμp.le hs hq
    have hu := mean_upper μ s L q hμp.le hs
    have ht := profile_tail_small s q₀ q ε hε.le hq₀ hstart
    have hb := mul_le_mul_of_nonneg_left ht hμp.le
    rw [hDcoe,abs_lt]
    rw [abs_lt] at hh
    constructor <;> nlinarith
  · intro q hq hqT
    have hbg : |signedFiber (L+1) (profileWeight μ s) a q| ≤ (ε/4)*μ := by
      by_contra hn
      apply hqT
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),lt_of_not_ge hn⟩
    have hcorr := signedMean_nat_correction_bounds_all L q σ (profileWeight μ s) hσ
      (fun i ↦ profileWeight_bounds μ s hμp.le hs i.val)
    have hsamp := (hω q (by omega)).2
    have hbase : labelFiber (L+1) (fun i ↦ profileWeight μ s i*σ i) q =
        signedFiber (L+1) (profileWeight μ s) a q := rfl
    rw [hbase] at hcorr
    have hprobEq : (fun i : Fin (L+1) ↦ profileWeight μ s i.val)=probability μ s L := rfl
    rw [hprobEq] at hcorr
    change |labelFiber (L+1) (fun i ↦ selectedWeight D i*σ i) q| < ε*μ
    rw [←signedRep_eq_labelFiber_all L q σ ω]
    rw [abs_lt] at hsamp ⊢
    rw [abs_le] at hbg
    constructor <;> nlinarith

end Erdos66BinaryProfileCodegree
