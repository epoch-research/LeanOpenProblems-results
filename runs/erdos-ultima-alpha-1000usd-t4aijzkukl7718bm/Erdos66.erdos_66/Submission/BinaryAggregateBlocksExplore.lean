import Submission.BinarySignedProfileExplore
import Submission.AffineAggregateIntegerTransferExplore

/-! An unconditional finite block construction outside a logarithmic-square
number of coarse exceptions. These exceptions are entire blocks, not sparse
individual natural targets, and are not repaired here. -/
namespace Erdos66BinaryAggregateBlocks
open AdditiveCombinatorics Erdos66BinarySignedProfile Erdos66AffineRootAggregate
  Erdos66SharedParameterKernel Erdos66RealWeightedCharacterEnergy
  Erdos66CyclicThickening Erdos66OuterCarryProfile Erdos66AffineAggregateIntegerTransfer
open scoped Classical
set_option maxHeartbeats 1700000

/-- The prime-size factor has been removed from both the signed-selection
budget and the binary concentration budget. The unresolved exceptions are
explicit coarse blocks. -/
theorem exists_aggregate_blocks (p K J : ℕ) [Fact p.Prime] [NeZero K] [NeZero J]
    (hp : p ≠ 2) (s q₀ Q : ℕ) (hpQ : 4*(Q+1)<p) (μ ε : ℝ)
    (hμ : 1 ≤ μ) (hε : 0<ε) (hε1 : ε ≤ 1) (hlarge : 8 ≤ ε*μ)
    (hs : μ ≤ (s : ℝ)+1) (hstart : 64*(s : ℝ)^2 ≤ ε^2*((q₀ : ℝ)+1))
    (hsmall : 6*(2*(Q : ℝ)+1)*Real.exp (-ε^2*(μ+1)/512)<1) :
    ∃ (a : ZMod p) (T D : Finset ℕ), D ⊆ Finset.range (Q+1) ∧
      (T.card : ℝ) ≤ 128*(1+Real.log ((Q+1 : ℕ) : ℝ))^2/ε^2 ∧
      ∀ q, q₀+1 ≤ q → q ≤ Q → q∉T → q-1∉T →
      ∀ (z : ZMod ((p*K)^2)) (r : Fin J),
      |(sumRep
        (Erdos66IntegerBlock.blockSet (((p*K)^2)*J)
          (fun i ↦ outerLift ((p*K)^2) J (thickenedSet p K (coloredCurve D a i))))
        (q*(((p*K)^2)*J)+(blockDigit ((p*K)^2) J z r).val) : ℝ)-J*(K : ℝ)^2*μ| ≤
        ((J : ℝ)+1)*((K : ℝ)^2*(2*ε*μ)+2*K*(μ+2*ε*μ))+(K : ℝ)^2*μ := by
  obtain ⟨a,T,D,hD,ha,hop,hT,hupper,hunsigned,hsigned⟩ :=
    exists_binary_signed_profile p hp s q₀ Q hpQ μ ε hμ hε hε1 hlarge hs hstart hsmall
  refine ⟨a,T,D,hD,hT,?_⟩
  intro q hq₀ hq hqT hpT z r
  have hmu (m : ℕ) (hm : m=q ∨ m=q-1) :
      |(sumRep (D : Set ℕ) m : ℝ)-μ| ≤ ε*μ := by
    rcases hm with he | he
    · subst m
      exact (hunsigned q (by omega) hq).le
    · subst m
      exact (hunsigned (q-1) (by omega) (by omega)).le
  have hsign (m : ℕ) (hm : m=q ∨ m=q-1) :
      |labelFiber (Q+1) (fun i ↦ selectedWeight D i*(quadraticChar (ZMod p) (a+i) : ℝ)) m| ≤ ε*μ := by
    rcases hm with he | he
    · subst m
      exact (hsigned q (by omega) hqT).le
    · subst m
      exact (hsigned (q-1) (by omega) hpT).le
  have hopp (m : ℕ) (hm : m=q ∨ m=q-1) : 2*a+(m : ZMod p) ≠ 0 := by
    apply hop m
    rcases hm with he | he <;> omega
  have hh := affine_integer_error p K J hp D a (Q+1) q hD (by omega) (by omega)
    ha hopp μ (ε*μ) (ε*μ) hmu hsign z r
  convert hh using 1 <;> ring_nf

end Erdos66BinaryAggregateBlocks
