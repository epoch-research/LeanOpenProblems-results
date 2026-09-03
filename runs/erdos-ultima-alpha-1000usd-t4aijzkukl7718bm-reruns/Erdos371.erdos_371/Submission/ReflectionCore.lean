import FormalConjecturesUtil
import Submission.CofactorReflection

/-! A finite obstruction to exact cancellation under the prime-factor reflection.
This is not a disproof of the density conjecture. -/

namespace Erdos371ReflectionCore

open Erdos371Cofactor

def core (p : ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun n =>
    1 < n ∧ max (P n) (P (n + 1)) = p ∧
      n + 1 < P n * P (n + 1)

lemma core_five : core 5 = {4, 5, 9} := by decide +kernel

lemma core_five_reflection : reflect 4 = 5 ∧ reflect 5 = 9 ∧ reflect 9 = 5 := by
  decide +kernel

lemma core_five_counts :
    ((core 5).filter (fun n => P n < P (n + 1))).card = 2 ∧
    ((core 5).filter (fun n => P (n + 1) < P n)).card = 1 := by
  decide +kernel

lemma exact_core_balance_fails :
    ¬ ∀ p : ℕ, p.Prime →
      ((core p).filter (fun n => P n < P (n + 1))).card =
      ((core p).filter (fun n => P (n + 1) < P n)).card := by
  intro h
  have he := h 5 (by decide)
  rw [core_five_counts.1, core_five_counts.2] at he
  omega

end Erdos371ReflectionCore

#print axioms Erdos371ReflectionCore.exact_core_balance_fails
