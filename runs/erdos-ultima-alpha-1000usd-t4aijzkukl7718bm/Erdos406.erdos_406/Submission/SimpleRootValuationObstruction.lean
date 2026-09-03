import Submission.DigitSumValuationObstruction
import Submission.NewmanSimpleModTwoRoot

/-! A checked obstruction to a degree-plus-root-multiplicity valuation bound.
The integer used below has odd cofactor 4745 and is not an original candidate.
This file does not settle Erdős 406. -/
namespace Erdos406SimpleRootValuation
open Polynomial Erdos406Cyclotomic Erdos406ReciprocalCandidate
  Erdos406SimpleModTwoRoot Erdos406DigitSumValuation Erdos406FactorBridge

lemma simple_one_root_multiplicity (P : ℤ[X]) (hP : SimpleOne P) :
    (P.map (Int.castRingHom (ZMod 2))).rootMultiplicity 1 = 1 := by
  let Q := P.map (Int.castRingHom (ZMod 2))
  have hQ : Q ≠ 0 := by
    intro hz
    have hh := hP.2
    change Q.derivative.eval 1 ≠ 0 at hh
    simp [hz] at hh
  have hpos : 0 < Q.rootMultiplicity 1 :=
    (rootMultiplicity_pos hQ).mpr hP.1
  have hle : ¬ 1 < Q.rootMultiplicity 1 := by
    intro hh
    exact hP.2 ((one_lt_rootMultiplicity_iff_isRoot hQ).mp hh).2
  change Q.rootMultiplicity 1 = 1
  omega

noncomputable def exampleP : ℤ[X] := digitPoly (Nat.digits 3 exampleN)

lemma exampleP_binary : Erdos406ReciprocalFlip.Binary exampleP :=
  binary_digitPoly _ example_digits.1

lemma exampleP_simple_one : SimpleOne exampleP := by
  have hf : (4 : ℤ) ∣ exampleP.eval 3 := by
    rw [exampleP, digitPoly_eval_three]
    norm_num [exampleN]
  apply (simple_one_iff_eval_one_mod_four exampleP hf).mpr
  change (Nat.ofDigits (X : ℤ[X]) (Nat.digits 3 exampleN)).eval 1 % 4 = 2
  rw [Erdos406Newman.eval_one_digitPoly, example_digits.2.2]
  norm_num

lemma exampleP_root_multiplicity :
    (exampleP.map (Int.castRingHom (ZMod 2))).rootMultiplicity 1 = 1 :=
  simple_one_root_multiplicity exampleP exampleP_simple_one

lemma exampleP_degree : exampleP.natDegree = 37 := by
  have hn : Nat.digits 3 exampleN ≠ [] := by decide +kernel
  have hl : (Nat.digits 3 exampleN).getLast hn = 1 := by decide +kernel +revert
  have hh := (digitPoly_isMonicOfDegree _ hn hl).natDegree_eq
  simpa only [exampleP, example_digits.2.1] using hh

/-- Even an allowance of eight does not rescue this general valuation bound.
No pure-power evaluation hypothesis appears here; the example cannot refute
an estimate that retains that essential hypothesis. -/
theorem degree_plus_multiplicity_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      padicValNat 2 n ≤ (digitPoly (Nat.digits 3 n)).natDegree +
        ((digitPoly (Nat.digits 3 n)).map
          (Int.castRingHom (ZMod 2))).rootMultiplicity 1 + 8) := by
  intro h
  have hh := h exampleN (by decide) example_digits.1
  change padicValNat 2 exampleN ≤ exampleP.natDegree +
    (exampleP.map (Int.castRingHom (ZMod 2))).rootMultiplicity 1 + 8 at hh
  rw [example_valuation, exampleP_degree, exampleP_root_multiplicity] at hh
  omega

/-- The same obstruction lies in the simple-root branch itself. -/
theorem simple_root_degree_allowance_bound_false :
    ¬ (∀ n : ℕ, 0 < n → Nat.digits 3 n ⊆ [0, 1] →
      SimpleOne (digitPoly (Nat.digits 3 n)) →
      padicValNat 2 n ≤ (digitPoly (Nat.digits 3 n)).natDegree + 9) := by
  intro h
  have hh := h exampleN (by decide) example_digits.1 exampleP_simple_one
  change padicValNat 2 exampleN ≤ exampleP.natDegree + 9 at hh
  rw [example_valuation, exampleP_degree] at hh
  omega

#print axioms exampleP_root_multiplicity
#print axioms degree_plus_multiplicity_bound_false
#print axioms simple_root_degree_allowance_bound_false
end Erdos406SimpleRootValuation
