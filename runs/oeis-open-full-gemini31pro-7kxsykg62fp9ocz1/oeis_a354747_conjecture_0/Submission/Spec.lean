import FormalConjectures.Util.ProblemImports
import Submission.TestPrimality5
import Submission.TestCertFinal
import Submission.TestCertVals

set_option maxRecDepth 2000000
set_option exponentiation.threshold 1000000

namespace R

def inv2 : R my_N_val := (inv2_u, inv2_v)
def inv3 : R my_N_val := (inv3_u, inv3_v)
def invp : R my_N_val := (invp_u, invp_v)

theorem h_inv2 : mul inv2 (sub chain_M2_final one) = one := by decide
theorem h_inv3 : mul inv3 (sub chain_M3_final one) = one := by decide
theorem h_invp : mul invp (sub chain_Mp_final one) = one := by decide
theorem h_M_eq_one : chain_M_final = one := by decide

theorem N_prime : Nat.Prime my_N_val := by
  apply is_prime_of_cert (M := my_M) (m := 39101) (x := alpha) (inv2 := inv2) (inv3 := inv3) (invp := invp)
  · decide -- hN
  · rfl -- hM
  · decide -- hm_pos
  · exact Eq.trans val_M_eq_pow.symm h_M_eq_one
  · exact Eq.trans (congrArg (fun y => mul inv2 (sub y one)) val_M2_eq_pow.symm) h_inv2
  · exact Eq.trans (congrArg (fun y => mul inv3 (sub y one)) val_M3_eq_pow.symm) h_inv3
  · exact Eq.trans (congrArg (fun y => mul invp (sub y one)) val_Mp_eq_pow.symm) h_invp

end R

open Nat Set

noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

theorem oeis_a354747_conjecture_0 : a354747 100943 = 0 := sorry

theorem oeis_a354747_conjecture_0.disproof : ¬ a354747 100943 = 0 := by
  intro h
  have h_mem : 39101 ∈ { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) } := by
    simp only [mem_setOf_eq]
    refine ⟨by decide, ?_⟩
    have h_eq : 2 * 100943 * 3 ^ 39101 - 1 = my_N_val := by decide
    rw [h_eq]
    exact R.N_prime
  have h_nonempty : { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) }.Nonempty := ⟨39101, h_mem⟩
  have h_sInf_mem := Nat.sInf_mem h_nonempty
  have h_eq : sInf { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) } = a354747 100943 := rfl
  have h_sInf_zero : sInf { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) } = 0 := by
    exact Eq.trans h_eq h
  have h_mem2 : sInf { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) } > 0 := h_sInf_mem.1
  rw [h_sInf_zero] at h_mem2
  revert h_mem2
  decide
