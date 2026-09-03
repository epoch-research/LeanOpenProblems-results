import Submission.NFAFiniteCertificate

/-! A kernel test of the finite certificate interface on the language whose
last nonzero ternary digit is2. Its safety and multiplication checks pass,
but its required power-of-four seed fails, so it does not settle Erdős406. -/
namespace Erdos406NFATest
open Erdos406NFAFinite

def maskSet (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun q => m.testBit q.val)

def stepTable : List (List ℕ) := [[1, 2, 4], [2, 2, 4], [4, 2, 4]]

def familyTable : List (List (List ℕ)) :=
  [[[1], [2], [4], [2]], [[2], [2, 4], [2, 4], [2, 4]],
    [[4], [2, 4], [2, 4], [2, 4]]]

def testData : Data (Fin 3) where
  step q d := maskSet 3 ((stepTable.getD q.val []).getD d 0)
  start := {0}
  accept := maskSet 3 4
  cutoff := 0
  stride := 1
  family q c := (((familyTable.getD q.val []).getD c []).toFinset).image (maskSet 3)

set_option maxRecDepth 10000 in
lemma test_init : ∀ q ∈ testData.start, ∀ c, c < 4 ^ testData.stride →
    ∃ U ∈ testData.family q c, U ⊆ testData.evalStates c := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxSize 10000 in
lemma test_step : ∀ q c, c < 4 ^ testData.stride → ∀ U ∈ testData.family q c,
    ∀ d, d < 3 → ∀ e, e < 3 → ∀ c', c' < 4 ^ testData.stride →
    4 ^ testData.stride * d + c' = 3 * c + e → ∀ r ∈ testData.step q d,
    ∃ V ∈ testData.family r c', V ⊆ testData.stepStates U e := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma test_finish : ∀ q ∈ testData.accept, ∀ U ∈ testData.family q 0,
    (U ∩ testData.accept).Nonempty := by
  decide +kernel

lemma test_safety_start : testData.start ⊆ ({0, 1} : Finset (Fin 3)) := by decide +kernel

set_option maxRecDepth 10000 in
lemma test_safety_step : ∀ q ∈ ({0, 1} : Finset (Fin 3)), ∀ d, d < 2 →
    testData.step q d ⊆ ({0, 1} : Finset (Fin 3)) := by
  decide +kernel

lemma test_safety_finish : Disjoint ({0, 1} : Finset (Fin 3)) testData.accept := by decide +kernel

/-- This is exactly the missing seed obligation; it is false for this test
language. The remaining checks must not be mistaken for a complete proof. -/
lemma test_seed_fails : ¬ ∀ r, r < testData.stride →
    (testData.evalStates (4 ^ (testData.cutoff + r)) ∩ testData.accept).Nonempty := by
  decide +kernel

#print axioms test_init
#print axioms test_step
#print axioms test_finish
#print axioms test_seed_fails
end Erdos406NFATest
