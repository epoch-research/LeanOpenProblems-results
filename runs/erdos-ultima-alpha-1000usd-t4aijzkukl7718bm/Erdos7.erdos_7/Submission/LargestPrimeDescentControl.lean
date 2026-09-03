import Submission.MinimumFiveClasses

/-! A genuine full-cover control for largest-prime descent. The removed
largest prime is odd, and both nontrivial fibres cover, but no strict cover
exists at the reduced period. The original family has EVEN moduli, so this
is not a counterexample to the odd covering conjecture. -/
namespace Erdos7LargestPrimeDescentControl
open Erdos7CompanionExchange
set_option autoImplicit false
set_option maxHeartbeats 2000000

def cofactor : Fin 5 → ℕ := ![2,1,4,2,4]
def level : Fin 5 → ℕ := ![0,1,0,1,1]
def reducedResidue (r : ℤ) (i : Fin 5) : ℤ := 3*(residues i-r)

lemma factor_data : ∀ i,moduli i=3^level i*cofactor i ∧
    Nat.Coprime 3 (cofactor i) ∧ cofactor i∣4 := by decide +kernel

lemma largest_prime : Nat.Prime 3 ∧ Odd 3 ∧ (3:ℕ)∣12 ∧
    ∀ q : ℕ,q.Prime → q∣12 → q≤3 := by
  refine ⟨by norm_num,by norm_num,by norm_num,?_⟩
  intro q hq hd
  have hq12 := Nat.le_of_dvd (by norm_num : 0<12) hd
  interval_cases q <;> norm_num at *

lemma original_cover : ∀ z : ℤ,∃ i,(moduli i:ℤ)∣z-residues i := control_cover

lemma projected_hit (r x : ℤ) (i : Fin 5)
    (hi : (moduli i:ℤ)∣3*x+r-residues i) :
    (cofactor i:ℤ)∣x-reducedResidue r i := by
  have hdN : cofactor i∣moduli i := by rw [(factor_data i).1]; exact dvd_mul_left _ _
  have hdN' : (cofactor i:ℤ)∣(moduli i:ℤ) := by exact_mod_cast hdN
  have hd := hdN'.trans hi
  have hd4 : (cofactor i:ℤ)∣4 := by exact_mod_cast (factor_data i).2.2
  have h8 : (cofactor i:ℤ)∣8*x := hd4.trans ⟨2*x,by ring⟩
  have h3 : (cofactor i:ℤ)∣3*(3*x+r-residues i) := dvd_mul_of_dvd_right hd _
  convert dvd_sub h3 h8 using 1
  unfold reducedResidue
  ring

/-- Every nonzero ternary fibre really covers using nontrivial cofactors.
It is the DISTINCTNESS requirement, not the coverage implication, that fails. -/
theorem reduced_fibre_cover (r : ℤ) (hr : ¬(3:ℤ)∣r) :
    ∀ x : ℤ,∃ i,1<cofactor i ∧ (cofactor i:ℤ)∣x-reducedResidue r i := by
  intro x
  obtain ⟨i,hi⟩ := original_cover (3*x+r)
  refine ⟨i,?_,projected_hit r x i hi⟩
  fin_cases i <;> norm_num [cofactor]
  apply False.elim
  apply hr
  have hh : (3:ℤ)∣3*x+r := by
    change (3:ℤ)∣3*x+r-0 at hi
    simpa only [sub_zero] using hi
  have hx : (3:ℤ)∣3*x := dvd_mul_right _ _
  convert dvd_sub hh hx using 1; ring

lemma projected_not_injective : ¬Function.Injective cofactor := by
  intro h
  have he := h (show cofactor 0=cofactor 3 from rfl)
  have hh := congrArg Fin.val he
  norm_num at hh

/-- Arbitrary pruning, reassignment of residues, and choice of nontrivial
moduli dividing the reduced period cannot produce a strict cover. -/
theorem no_strict_reduced_cover {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i, 1 < m i) (hd : ∀ i,m i∣4) :
    ¬(∀ x : ℤ,∃ i,(m i:ℤ)∣x-a i) :=
  Erdos7MinimumFive.no_small_period_cover m a hinj hm 4
    (by norm_num) (by norm_num) hd

/-- This full-cover control must not be mistaken for an all-odd family. -/
lemma not_all_odd : ¬(∀ i,Odd (moduli i)) := by
  intro h
  have hh := h 0
  norm_num [moduli] at hh

#print axioms reduced_fibre_cover
#print axioms no_strict_reduced_cover
end Erdos7LargestPrimeDescentControl
