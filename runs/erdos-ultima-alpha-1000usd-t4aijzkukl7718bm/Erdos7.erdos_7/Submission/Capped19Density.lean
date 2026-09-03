import Submission.QuantitativeRectangleAvoidance
import Submission.Capped19Schedule

/-! Uniform positive uncovered density for the certified seven-prime rectangle. -/
namespace Erdos7Capped19Schedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7Capped19Rows Erdos7DeficitFamilyBudget
set_option maxHeartbeats 2500000
set_option maxRecDepth 2000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

lemma prefixCap_exact : prefixCap cap 7 = 60 := by
  have hs (i : Fin 7) : prefixCap cap (i.val+1) = cap i*prefixCap cap i.val := by
    rw [prefixCap]
    exact dif_pos i.isLt
  rw [hs ⟨6,by omega⟩,hs ⟨5,by omega⟩,hs ⟨4,by omega⟩,hs ⟨3,by omega⟩,
    hs ⟨2,by omega⟩,hs ⟨1,by omega⟩,hs ⟨0,by omega⟩]
  change ((9/4:ℚ):ℝ) * (((2:ℚ):ℝ) * (((2:ℚ):ℝ) * (((5/3:ℚ):ℝ) *
    (((3/2:ℚ):ℝ) * (((4/3:ℚ):ℝ) * (2*1)))))) = 60
  norm_num

variable (A : Fin 7 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (E : Fin 7 → ℕ) (X : Pattern E → ∀ i,Finset (A i))

/-- The fraction of uncovered points is at least 1158871/6561000000,
uniformly over every finite exponent rectangle. -/
theorem uncovered_density_bound
    (hd : ∀ i k,exponent E k i ≠ 0 →
      ((X k i).card:ℝ)/(Fintype.card (A i):ℝ) ≤ 1/(primes i:ℝ)^(exponent E k i)) :
    (Fintype.card (∀ i,A i):ℝ)*(1158871/6561000000:ℝ) ≤ (uncovered A E X).card := by
  let ρ (i : Fin 7) (_ : A i) : ℝ := 1/Fintype.card (A i)
  have hρ (i : Fin 7) (y : A i) : 0 ≤ ρ i y := by dsimp only [ρ]; positivity
  have hρmass (i : Fin 7) : (∑ y,ρ i y) = 1 := by
    have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    simp only [ρ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  have hd' (i : Fin 7) (k : Pattern E) (hk : exponent E k i ≠ 0) :
      (∑ y,if y ∈ X k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(exponent E k i) := by
    simpa only [ρ,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one_div]
      using hd i k hk
  let S := schedule A E X ρ hρ hρmass hd'
  have ht : S.potential 7 = fun _ => 0 := by
    change potential 7 = fun _ => 0
    simpa only [potential,show ¬(7:ℕ) = 0 by omega,if_false,forms] using evalR_terminal
  have h := uncovered_card_bound S (fun _ _ => rfl) ht
  change (Fintype.card (∀ i,A i):ℝ)*(1-(rootValue:ℝ)) ≤
    (uncovered A E X).card*prefixCap cap 7 at h
  rw [prefixCap_exact,rootValue_exact] at h
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  nlinarith

#print axioms uncovered_density_bound
end Erdos7Capped19Schedule
