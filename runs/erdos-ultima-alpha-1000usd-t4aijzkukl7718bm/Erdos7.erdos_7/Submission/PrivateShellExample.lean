import Submission.PrivateShellPressure
import Submission.StoppingTwoPrimeExample

/-! A shell deficit distinguishes the existing stopping-obstruction partial
family from an actual cover. This is not a solution of Erdős Problem 7. -/
namespace Erdos7PrivateShellExample
open scoped BigOperators
open Erdos7StoppingTwoPrimeExample Erdos7PrivateShellPressure
set_option maxHeartbeats 1500000

def e (j : Fin 24) : ℕ := exponents j 1
def d (j : Fin 24) : ℕ := 3^(exponents j 0)

lemma factorization : ∀ j, 5^(e j)*d j=modulus j := by decide +kernel
lemma bounds : (∀ j, e j ≤ 4) ∧ (∀ j, d j ∣ 81) := by decide +kernel
lemma private_point : ∀ j : Fin 24,
    ((5^(e j)*d j : ℕ) : ℤ) ∣ 1319-residue j ↔ j=3 := by decide +kernel

/-- The private point of the625-class has no other class eligible for its
last quinary shell, although the two separate stopping closures are terminal. -/
lemma no_eligible : ∀ j : Fin 24, ¬ Eligible 5 3 e d residue 1319 j := by
  unfold Eligible
  decide +kernel

lemma shell_deficit :
    (∑ j : Fin 24, if Eligible 5 3 e d residue 1319 j then ((5 : ℚ)⁻¹)^(e j) else 0) <
      ((5 : ℚ)⁻¹)^3-((5 : ℚ)⁻¹)^4 := by
  simp only [no_eligible, if_false, Finset.sum_const_zero]
  norm_num

theorem not_cover_via_private_shell :
    ¬ (∀ z : ℤ, ∃ j : Fin 24, (modulus j : ℤ) ∣ z-residue j) := by
  intro hc
  have hc' : ∀ z : ℤ, ∃ j : Fin 24, ((5^(e j)*d j : ℕ) : ℤ) ∣ z-residue j := by
    simpa only [factorization] using hc
  exact not_cover_of_shell_deficit 5 4 81 (by decide) e d residue bounds.1 bounds.2
    (3 : Fin 24) 1319 private_point 3 (by decide) shell_deficit hc'

/-- Four actual integer holes in the displayed shell. This separate finite
check does not depend on the rational pressure calculation. -/
def shellHoles : Fin 4 → ℤ := ![11444,21569,31694,41819]

lemma shell_holes_data : ∀ k : Fin 4,
    (81 : ℤ) ∣ shellHoles k-1319 ∧
    (125 : ℤ) ∣ shellHoles k-1319 ∧
    ¬ (625 : ℤ) ∣ shellHoles k-1319 ∧
    ∀ j : Fin 24, ¬ (modulus j : ℤ) ∣ shellHoles k-residue j := by
  decide +kernel

#print axioms no_eligible
#print axioms not_cover_via_private_shell
#print axioms shell_holes_data
end Erdos7PrivateShellExample
