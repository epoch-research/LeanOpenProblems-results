import FormalConjecturesUtil
import Submission.SL2TranslationWords
import Submission.InvolutiveProductsOddGroup

/-! Every full SL2 section with arbitrary voltages in a near-equal-size
odd abelian group contains C8. This is a construction obstruction only. -/
open SimpleGraph
open scoped MatrixGroups
namespace Erdos713C8SL2OddGroupVoltage
open Erdos713C8SL2SectionObstruction Erdos713SL2TranslationWords
variable {K W : Type*} [Field K] [CharP K 2] [Fintype K]
    [CommGroup W] [Fintype W]
set_option maxHeartbeats 1000000

/-- The voltage function is completely arbitrary, and need not be injective.
There is no polynomial, norm, or multiplicative-homomorphism hypothesis. -/
theorem contains (f : K → W) (hodd : Odd (Fintype.card W))
    (hW : Fintype.card W ≤ Fintype.card K+1) (hq : 40 ≤ Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  classical
  obtain ⟨c,r,d,hcr,hcr',hcd,hcd',hv⟩ :=
    Erdos713InvolutiveProductsOddGroup.exists_relation
      (fun a : K => a+1) shift_involutive (ratio f) shift_ne hodd hW hq
  exact contains_at f r c d hcr hcr' hcd hcd' hv

lemma odd_successor_card : Odd (Fintype.card K+1) := by
  obtain ⟨n,_hp,hn⟩ := FiniteField.card K 2
  rw [hn]
  apply Even.add_one
  exact even_two.pow_of_ne_zero (PNat.ne_zero n)

omit [CharP K 2] [Fintype K] [Fintype W] [CommGroup W] in
lemma odd_card_rootsOfUnity {L : Type*} [Field L] (n : ℕ) [NeZero n] (hn : Odd n) :
    Odd (Fintype.card (rootsOfUnity n L)) := by
  have hpow : ∀ g : rootsOfUnity n L, g^n=1 := by
    intro g
    apply Subtype.ext
    exact g.property
  have hd := card_dvd_exponent_pow_rank' (rootsOfUnity n L) hpow
  simpa only [Nat.card_eq_fintype_card] using Odd.of_dvd_nat hn.pow hd

/-- Arbitrary norm-one-group voltages are included, not only the tested
Möbius ratio from a quadratic extension. The extension need not be finite. -/
theorem contains_normOne {L : Type*} [Field L]
    (f : K → rootsOfUnity (Fintype.card K+1) L) (hq : 40 ≤ Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  exact contains f (odd_card_rootsOfUnity _ (odd_successor_card (K := K)))
    (card_rootsOfUnity L _) hq

/-- Arbitrary multiplicative unit-group voltages are also excluded. -/
theorem contains_units (f : K → Kˣ) (hq : 40 ≤ Fintype.card K) :
    cycleGraph 8 ⊑ Erdos713C8CommutingDifferences.graph (generator f) := by
  classical
  have hcard := Fintype.card_units (α := K)
  have he : Even (Fintype.card K) := by
    obtain ⟨n,_hp,hn⟩ := FiniteField.card K 2
    rw [hn]
    exact even_two.pow_of_ne_zero (PNat.ne_zero n)
  have hodd : Odd (Fintype.card Kˣ) := by
    rw [hcard]
    obtain ⟨j,hj⟩ := he
    refine ⟨j-1,?_⟩
    omega
  exact contains f hodd (by rw [hcard]; omega) hq

#print axioms contains
#print axioms contains_normOne
#print axioms contains_units
end Erdos713C8SL2OddGroupVoltage
