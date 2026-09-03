import Submission.ZeroSumObstruction

/-!
A fixed zero-sum-free assignment need not permit upgrading one frequency to
exact modulus order. This is a limitation of a possible proof strategy, not a
covering system and not a resolution of the odd covering problem.
-/
namespace Erdos7PrimitiveFrequencyUpgrade
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000

def smallPrefix : Fin 3 → ZMod 9 := ![1,4,7]
def smallFamily : Fin 4 → ZMod 9 := ![1,4,7,3]

/-- The sole omitted residue is6, of nonprimitive order3. -/
lemma small_reachable :
    ((Finset.univ : Finset (Fin 3)).powerset.image
      (fun s => ∑ i ∈ s, smallPrefix i)) = Finset.univ.erase (6 : ZMod 9) := by
  decide +kernel

lemma small_zero_free : ∀ s : Finset (Fin 4), s.Nonempty →
    ∑ i ∈ s, smallFamily i ≠ 0 := by decide +kernel

/-- Every element of exact additive order9 is forbidden as the next term.
In ZMod9, the condition3*k!=0 is exactly that order condition. -/
lemma small_primitive_forbidden : ∀ k : ZMod 9, (3 : ZMod 9)*k ≠ 0 →
    ∃ s : Finset (Fin 3), ∑ i ∈ s, smallPrefix i = -k := by
  decide +kernel

/-- Distinct odd moduli realize the same fixed-assignment obstruction. -/
def modulus : Fin 4 → ℕ := ![27,45,63,9]
def frequency : Fin 4 → ZMod 945 := ![105,420,735,315]
def replacement (k : ZMod 945) (i : Fin 4) : ZMod 945 :=
  if i = 3 then k else frequency i

lemma arithmetic_data : Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 945) ∧
    (∀ i, (modulus i : ZMod 945)*frequency i = 0) := by decide +kernel

lemma frequency_zero_free : ∀ s : Finset (Fin 4), s.Nonempty →
    ∑ i ∈ s, frequency i ≠ 0 := by decide +kernel

lemma last_has_lower_order : (3 : ZMod 945)*frequency 3 = 0 ∧ frequency 3 ≠ 0 := by
  decide +kernel

/-- Every allowed upgrade of the fourth term to order9 creates a nonempty
zero subset sum, with the first three terms held fixed. -/
lemma every_primitive_replacement_fails : ∀ k : ZMod 945,
    (9 : ZMod 945)*k = 0 → (3 : ZMod 945)*k ≠ 0 →
    ∃ s : Finset (Fin 4), s.Nonempty ∧ ∑ i ∈ s, replacement k i = 0 := by
  decide +kernel

/-- The original lower-order assignment is a genuine character certificate
for this small family. It is not a witness for the existential conjecture. -/
theorem no_cover (a : Fin 4 → ℤ) :
    ¬ (∀ z : ℤ, ∃ i, (modulus i : ℤ) ∣ z-a i) :=
  Erdos7ZeroSum.not_arithmetic_cover modulus a frequency arithmetic_data.2.2
    frequency_zero_free

/-- This does not claim that no OTHER simultaneous exact-order assignment
works for the same four moduli. Only the one-term upgrade is ruled out. -/
theorem no_fixed_primitive_upgrade : ¬ ∃ k : ZMod 945,
    (9 : ZMod 945)*k = 0 ∧ (3 : ZMod 945)*k ≠ 0 ∧
    (∀ s : Finset (Fin 4), s.Nonempty → ∑ i ∈ s, replacement k i ≠ 0) := by
  rintro ⟨k,h9,h3,hz⟩
  obtain ⟨s,hs,he⟩ := every_primitive_replacement_fails k h9 h3
  exact hz s hs he

/-- Coordinated changes CAN give exact orders in this example. This prevents
misreading the fixed-upgrade obstruction as a global exact-order obstruction. -/
def exactAlternative : Fin 4 → ZMod 945 := ![35,21,15,105]

lemma exact_alternative_data :
    (∀ i, (modulus i : ZMod 945)*exactAlternative i = 0) ∧
    (∀ i, ∀ t : Fin (modulus i), t.val ≠ 0 →
      (t.val : ZMod 945)*exactAlternative i ≠ 0) ∧
    (∀ s : Finset (Fin 4), s.Nonempty → ∑ i ∈ s, exactAlternative i ≠ 0) := by
  decide +kernel

/-- A separate small control for subgroup-first reasoning. All frequencies
have proper, distinct odd orders, and every proper subgroup restriction is
zero-sum-free, yet their full sum is zero. -/
def primitiveCycle : Fin 3 → ZMod 105 := ![56,85,69]
def cycleModulus : Fin 3 → ℕ := ![15,21,35]

lemma primitive_cycle_data :
    Function.Injective cycleModulus ∧
    (∀ i, 1 < cycleModulus i ∧ Odd (cycleModulus i) ∧ cycleModulus i < 105 ∧
      cycleModulus i ∣ 105 ∧ (cycleModulus i : ZMod 105)*primitiveCycle i = 0) ∧
    (∑ i : Fin 3, primitiveCycle i) = 0 := by decide +kernel

lemma primitive_cycle_exact : ∀ i, ∀ t : Fin (cycleModulus i), t.val ≠ 0 →
    (t.val : ZMod 105)*primitiveCycle i ≠ 0 := by decide +kernel

lemma proper_subgroup_restrictions_zero_free :
    ∀ d : Fin 105, 0 < d.val → d.val ∣ 105 →
      ∀ s : Finset (Fin 3), s.Nonempty →
        (∀ i ∈ s, (d.val : ZMod 105)*primitiveCycle i = 0) →
          ∑ i ∈ s, primitiveCycle i ≠ 0 := by decide +kernel

#print axioms primitive_cycle_data
#print axioms proper_subgroup_restrictions_zero_free
#print axioms exact_alternative_data
#print axioms small_reachable
#print axioms arithmetic_data
#print axioms every_primitive_replacement_fails
#print axioms no_cover
#print axioms no_fixed_primitive_upgrade
end Erdos7PrimitiveFrequencyUpgrade
