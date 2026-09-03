import Submission.DenseGroupExtensionExplore
import Submission.SaturatingCyclicFamilyExplore

/-! Conditional dense supersets in an odd cyclic group, with the concentration
condition stated as an explicit logarithmic mean threshold. -/
namespace Erdos66DenseCyclicExtension
open Erdos66OuterCarryProfile Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 1500000

lemma exponential_test_of_log (T : ℝ) (hT : 0 < T) (ε v : ℝ)
    (h : 8*Real.log (2*T) < ε^2*v) :
    2*T*Real.exp (-ε^2*v/8) < 1 := by
  have hl : Real.log (2*T) < ε^2*v/8 := by linarith
  have he := (Real.log_lt_iff_lt_exp (by positivity : 0 < 2*T)).mp hl
  have hh := mul_lt_mul_of_pos_right he (Real.exp_pos (-ε^2*v/8))
  have heq : Real.exp (ε^2*v/8)*Real.exp (-ε^2*v/8)=1 := by
    rw [←Real.exp_add,show ε^2*v/8+ -ε^2*v/8=0 by ring,Real.exp_zero]
  rwa [heq] at hh

/-- Append a denser superset while retaining mixed flatness against an old
finite palette. All means used in the threshold are displayed explicitly.
This theorem does not assert the threshold at the conjectural sparse scale. -/
theorem exists_dense_cyclic_extension (M : ℕ) [NeZero M] (hodd : Odd M)
    (C : Finset (ZMod M)) (H : ℕ) (A : Fin H → Finset (ZMod M)) (b θ ε v : ℝ)
    (hb : b=θ*M+(1-θ)*C.card)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1/4)
    (hC : ∀ z, |(cyclicCount M C C z : ℝ)-actualMean M C C| ≤ ε*actualMean M C C)
    (hAC : ∀ i z, |(cyclicCount M (A i) C z : ℝ)-actualMean M (A i) C| ≤ ε*actualMean M (A i) C)
    (hlarge : 1 ≤ ε*(b^2/M))
    (hvs : v ≤ b^2/M) (hvm : ∀ i, v ≤ (A i).card*b/M) (hvc : v ≤ b)
    (hthreshold : 8*Real.log (2*((H+1)*M+1)) < ε^2*v) :
    ∃ B : Finset (ZMod M), C ⊆ B ∧
      (∀ z, |(cyclicCount M B B z : ℝ)-actualMean M B B| < 28*ε*actualMean M B B) ∧
      (∀ i z, |(cyclicCount M (A i) B z : ℝ)-actualMean M (A i) B| < 8*ε*actualMean M (A i) B) ∧
      |(B.card : ℝ)-b| < ε*b := by
  letI : LinearOrder (ZMod M) := LinearOrder.lift' ZMod.val (ZMod.val_injective M)
  have hinj : Function.Injective (fun a : ZMod M ↦ a+a) := by
    have hu : IsUnit (2 : ZMod M) := (ZMod.isUnit_iff_coprime 2 M).mpr hodd.coprime_two_left
    intro a b he
    exact hu.mul_right_injective (by simpa only [two_mul] using he)
  have hcount (D E : Finset (ZMod M)) (z : ZMod M) :
      Erdos66GroupRepBernoulli.count D E z=cyclicCount M D E z := by
    unfold Erdos66GroupRepBernoulli.count cyclicCount
    congr 1
    ext a
    simp
  have hmean (D E : Finset (ZMod M)) :
      Erdos66DenseGroupExtension.actualMean D E=actualMean M D E := by
    simp only [Erdos66DenseGroupExtension.actualMean,actualMean,ZMod.card]
  have hcard : Erdos66DenseGroupExtension.expectedCard C θ=b := by
    simpa only [Erdos66DenseGroupExtension.expectedCard,ZMod.card] using hb.symm
  have hself : Erdos66DenseGroupExtension.nominalSelf C θ=b^2/M := by
    simp only [Erdos66DenseGroupExtension.nominalSelf,hcard,ZMod.card]
  have hmixed (i : Fin H) : Erdos66DenseGroupExtension.nominalMixed (A i) C θ=(A i).card*b/M := by
    simp only [Erdos66DenseGroupExtension.nominalMixed,hcard,ZMod.card]
  have hT : (0 : ℝ) < ((H+1)*M+1) := by positivity
  have hsmall := exponential_test_of_log ((H+1)*M+1) hT ε v hthreshold
  have hsmall' : 2*((H+1)*Fintype.card (ZMod M)+1)*Real.exp (-ε^2*v/8) < 1 := by
    simpa only [ZMod.card] using hsmall
  have h := Erdos66DenseGroupExtension.exists_dense_extension_actual hinj C H A θ ε v
    hθ hθ1 hε hε1
    (by simpa only [hcount,hmean] using hC)
    (by simpa only [hcount,hmean] using hAC)
    (by simpa only [hself] using hlarge)
    (by simpa only [hself] using hvs)
    (by simpa only [hmixed] using hvm)
    (by simpa only [hcard] using hvc) hsmall'
  simpa only [hcount,hmean,hcard] using h

end Erdos66DenseCyclicExtension
