import FormalConjecturesUtil
import Submission.C8AdditiveAffineCount

/-! Arbitrary abelian voltage coordinates do not remove the additive-affine
parallelogram obstruction. Auxiliary work, not a solution of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8AdditiveAffineVoltage
open Erdos713C8CommutingDifferences Erdos713C8AdditiveAffine
open Erdos713C8AdditiveAffineCount
variable {K I W : Type*} [Field K] [CharP K 2] [CommGroup W]
set_option maxHeartbeats 2000000

def generator (f : K →+ K) (t : I → Kˣ) (w : I → W) (i : I) :
    Equiv.Perm K × W := (curve f (t i),w i)

/-- No additivity, regularity, or polynomial form is required of the
auxiliary voltage function. Its codomain may be any abelian group. -/
theorem contains_at (f : K →+ K) (t : I → Kˣ) (w : I → W)
    (ht : Function.Injective t) (a b c d : I)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : (t a : K)+(t b : K)=(t c : K)+(t d : K)) :
    cycleGraph 8 ⊑ graph (generator f t w) := by
  let g := generator f t w
  have hg : Function.Injective g := by
    intro i j h
    exact ht (curve_injective f (congrArg Prod.fst h))
  have hc : Commute ((g a)⁻¹*g b) ((g c)⁻¹*g d) := by
    apply Prod.ext
    · exact right_commute f (t a) (t b) (t c) (t d) hs
    · exact mul_comm _ _
  have hn : (g a)⁻¹*g b ≠ (g c)⁻¹*g d := by
    intro h
    exact difference_ne f (t a) (t b) (t c) (t d) (ht.ne hab) (ht.ne hac) hs
      (congrArg Prod.fst h)
  have hp : ((g a)⁻¹*g b)*((g c)⁻¹*g d) ≠ 1 := by
    intro h
    exact difference_product_ne f (t a) (t b) (t c) (t d) (ht.ne hab) (ht.ne hbc) hs
      (congrArg Prod.fst h)
  have hcopy := Erdos713C8CommutingGeneratorSets.four_generator_copy
    (fun i => (g i)⁻¹) (inv_injective.comp hg) a b c d hab hac had hbc hbd hcd
    (by simpa only [inv_inv] using hc) (by simpa only [inv_inv] using hn)
    (by simpa only [inv_inv] using hp)
  exact hcopy.trans (inverseGraphIso g).symm.isContained

lemma sum_sidon (f : K →+ K) (t : I → Kˣ) (w : I → W)
    (ht : Function.Injective t) (hf : (cycleGraph 8).Free (graph (generator f t w))) :
    SidonSums t := by
  intro a b c d hab hs
  by_cases hac : a=c
  · subst c
    exact Or.inl ⟨rfl,ht (Units.ext (add_left_cancel hs))⟩
  by_cases had : a=d
  · subst d
    rw [add_comm (t c : K)] at hs
    exact Or.inr ⟨rfl,ht (Units.ext (add_left_cancel hs))⟩
  by_cases hbc : b=c
  · subst c
    rw [add_comm (t b : K)] at hs
    exact Or.inr ⟨ht (Units.ext (add_right_cancel hs)),rfl⟩
  by_cases hbd : b=d
  · subst d
    exact Or.inl ⟨ht (Units.ext (add_right_cancel hs)),rfl⟩
  have hcd : c ≠ d := by
    intro h
    rw [h,CharTwo.add_self_eq_zero] at hs
    exact hab (ht (Units.ext (CharTwo.add_eq_zero.mp hs)))
  exact (hf (contains_at f t w ht a b c d hab hac had hbc hbd hcd hs)).elim

/-- The quadratic parameter bound survives every abelian voltage assignment. -/
theorem translated_square [Fintype I] (f : K →+ K) (t : I → Kˣ) (w : I → W)
    (ht : Function.Injective t) (hf : (cycleGraph 8).Free (graph (generator f t w)))
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) :
    (Fintype.card I)^2 ≤ Fintype.card I+2*Fintype.card U :=
  translated_square_of_sidon t (sum_sidon f t w ht hf) U theta hU

theorem retained_fraction [Fintype I] (f : K →+ K) (t : I → Kˣ) (w : I → W)
    (ht : Function.Injective t) (hf : (cycleGraph 8).Free (graph (generator f t w)))
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) (s : ℕ)
    (hs : Fintype.card U ≤ s*Fintype.card I) :
    Fintype.card U ≤ 2*s^2+s :=
  retained_fraction_of_sidon t (sum_sidon f t w ht hf) U theta hU s hs

end Erdos713C8AdditiveAffineVoltage
