import FormalConjectures.Util.ProblemImports
import Submission.Found
open Nat Finset BigOperators
namespace Wolst
variable {p : ℕ} [Fact p.Prime]

theorem sum_inv_pow_Ico_eq_zero (m : ℕ) (hm1 : 1 ≤ m) (hm : m < p - 1) :
    ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)^m = 0 := by
  have hbij : Function.Bijective (fun x : ZMod p => x⁻¹) :=
    ⟨fun a b h => by simpa using congrArg (·⁻¹) h, fun y => ⟨y⁻¹, by simp⟩⟩
  have huniv : ∑ x : ZMod p, (x⁻¹)^m = ∑ x : ZMod p, x^m :=
    Fintype.sum_bijective _ hbij (fun x => (x⁻¹)^m) (fun x => x^m) (fun x => rfl)
  have hz : ∑ x : ZMod p, x^m = 0 := by
    rw [FiniteField.sum_pow_lt_card_sub_one]; rw [ZMod.card]; omega
  have h0 : ∑ i ∈ Finset.range p, ((i : ZMod p)⁻¹)^m = ∑ x : ZMod p, (x⁻¹)^m :=
    sum_range_eq_univ (fun x => (x⁻¹)^m)
  have hsplit : ∑ i ∈ Finset.range p, ((i : ZMod p)⁻¹)^m
      = ((0 : ZMod p)⁻¹)^m + ∑ i ∈ Finset.Ico 1 p, ((i : ZMod p)⁻¹)^m := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) (by have := (Fact.out (p:=p.Prime)).two_le; omega : (1:ℕ) ≤ p)]
    simp
  rw [h0, huniv, hz] at hsplit
  simp only [inv_zero] at hsplit
  rw [zero_pow (by omega), zero_add] at hsplit
  exact hsplit.symm

end Wolst
