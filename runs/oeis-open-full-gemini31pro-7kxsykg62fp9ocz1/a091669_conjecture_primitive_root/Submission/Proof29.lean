import Mathlib
import Submission.Spec
import Submission.Proof26
import Submission.Proof27
import Submission.Proof28

open Nat BigOperators

lemma a091669_conjecture_primitive_root_proof (n : ℕ) (hn : n > 2) :
  n ∣ a (n - 1) + 2 ^ (n - 2) →
  n.Prime ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
  intro h_dvd
  have hn_prime : n.Prime := by
    by_contra hcomp
    exact composite_contradiction n hn hcomp h_dvd
  have h_totient : Nat.totient n = n - 1 := Nat.totient_prime hn_prime
  rw [h_totient]
  have hP : (((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) : ℕ) : ZMod n) = 1 := P_mod_n_eq_one n hn_prime hn h_dvd
  exact ⟨hn_prime, is_primitive_root_of_P_mod_n_eq_one n hn_prime hn hP⟩
