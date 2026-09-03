import Submission.SupportNumericLink
import Submission.SupportLossBound

/-! Interpreting the terminal moment functional of the auxiliary prefix. -/
namespace Erdos7SupportPrefixPotential
open scoped BigOperators
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks Erdos7SupportPrefixMetadata
open Erdos7SupportCompression Erdos7SupportMomentMatrix Erdos7SupportTailIteration
open Erdos7SupportPolynomialTail
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def tailNumerator (i : ℕ) : ℕ := ∑ j ∈ Finset.range 10,getNat potentialCoeffs j*momNat i j

def totalCost : ℕ := ∑ i ∈ Finset.range 167,getNat costs i

lemma statePotential_eq (x : TripleState) :
    statePotential x=∑ j : Fin 10,(getNat potentialCoeffs j:ℚ)/243*mono j x := by
  norm_num [statePotential,potential,mono,monoR,Fin.sum_univ_succ,potentialCoeffs,getNat]
  ring

lemma expected_potential_le (i : ℕ) (μ : TripleState →₀ ℚ)
    (h : ∀ j : Fin 10,pairExpect μ (mono j) ≤ mom i j) :
    pairExpect μ statePotential ≤ (tailNumerator i:ℚ)/(243*momentScale) := by
  rw [pairExpect_congr μ statePotential_eq,pairExpect_test_sum]
  simp only [pairExpect_test_mul]
  have hh : (∑ j : Fin 10,(getNat potentialCoeffs j:ℚ)/243*pairExpect μ (mono j)) ≤
      ∑ j : Fin 10,(getNat potentialCoeffs j:ℚ)/243*mom i j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (by positivity))
  apply hh.trans_eq
  unfold tailNumerator mom
  rw [← Fin.sum_univ_eq_sum_range (fun j => getNat potentialCoeffs j*momNat i j) 10]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma total_cost_eq : (∑ i : Fin 167,cost i)=(totalCost:ℚ)/costScale := by
  unfold cost totalCost
  rw [← Fin.sum_univ_eq_sum_range (fun i => getNat costs i) 167]
  push_cast
  rw [Finset.sum_div]

lemma rational_margin (A B S D : ℕ) (hS : 0 < S) (hD : 0 < D)
    (h : A*25*D+B*25*S < 24*S*D) : (A:ℚ)/S+(B:ℚ)/D < 24/25 := by
  have hSQ : (0:ℚ) < S := by exact_mod_cast hS
  have hDQ : (0:ℚ) < D := by exact_mod_cast hD
  have hh : (A:ℚ)*25*D+B*25*S < 24*S*D := by exact_mod_cast h
  apply lt_of_mul_lt_mul_right (a := (25:ℚ)*S*D) ?_ (by positivity)
  convert hh using 1 <;> field_simp <;> ring

#print axioms expected_potential_le
end Erdos7SupportPrefixPotential
