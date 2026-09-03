import Submission.StoppingPolicyArithmetic
import Submission.DivisorAssignment

/-! A genuine distinction between collision-free deletion and deletion followed
by divisor reassignment. The source is a partial odd family, not a cover. -/
namespace Erdos7DivisorAssignmentExample
open scoped BigOperators
open Erdos7Digits Erdos7AllDigits Erdos7StoppingDigitRestriction
open Erdos7StoppingPolicyArithmetic
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

def modulus : Fin 7 → ℕ := ![3,9,27,5,15,45,135]
def residue : Fin 7 → ℤ := ![0,1,4,0,8,11,2]
def privatePoint : Fin 7 → ℤ := ![3,1,4,5,8,11,2]
def primes : Fin 2 → ℕ := ![3,5]
def caps : Fin 2 → ℕ := ![3,1]
def exponents : Fin 7 → Fin 2 → ℕ :=
  ![![1,0],![2,0],![3,0],![0,1],![1,1],![2,1],![3,1]]
instance (i : Fin 2) : NeZero (primes i) := ⟨by fin_cases i <;> decide⟩

def position (x : Fin 3 → Fin 3) : Fin 3 := if x 0=1 then 1 else 2
def value (x : Fin 3 → Fin 3) : Fin 3 := if x 0=1 then 2 else 0

lemma position_pos (x : Fin 3 → Fin 3) : 0 < (position x).val := by
  unfold position
  split_ifs <;> decide

theorem position_predictable : Predictable position := by
  intro x y hxy
  have hh : x 0=y 0 := hxy 0 (position_pos x)
  simp only [position,hh]

theorem value_predictable : PredictableValue position value := by
  intro x y hxy
  have hh : x 0=y 0 := hxy 0 (position_pos x)
  simp only [value,hh]

abbrev Active (k : Fin 7) := active primes caps 0 position value (exponents k) (residue k)
instance (k : Fin 7) : Decidable (Active k) := by
  unfold Active active
  infer_instance

def projected (k : Fin 7) : ℕ :=
  ∏ i, primes i ^ eraseExponent 0
    (position (zmodDigits 3 3 (residue k))).val (exponents k) i

def assigned : Fin 7 → ℕ := ![3,0,0,5,15,45,9]

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ k, 1 < modulus k ∧ Odd (modulus k) ∧ modulus k ∣ 135) ∧
    (∀ k l, (modulus l : ℤ) ∣ privatePoint k-residue l ↔ l=k) ∧
    (∀ k, ¬ (modulus k : ℤ) ∣ 7-residue k) ∧
    (∀ k, modulus k=∏ i, primes i ^ exponents k i) := by
  decide +kernel

lemma divisor_data : ∀ k : Fin 7, ∀ d : ↥(modulus k).divisors,
    1<d.val → ∃ l, modulus l=d.val := by
  decide +kernel

theorem divisor_closed (k : Fin 7) (d : ℕ) (hd : d ∣ modulus k) (h1 : 1<d) :
    ∃ l, modulus l=d := by
  have hp : 0 < modulus k := lt_trans (by omega : 0<1) (arithmetic_data.2.1 k).1
  exact divisor_data k ⟨d,Nat.mem_divisors.mpr ⟨hd,hp.ne'⟩⟩ h1

/-- Both45-images survive. They are different original classes. -/
lemma collision_data : Active 5 ∧ Active 6 ∧ projected 5=45 ∧ projected 6=45 ∧
    eraseExponent 0 (position (zmodDigits 3 3 (residue 5))).val (exponents 5) =
      eraseExponent 0 (position (zmodDigits 3 3 (residue 6))).val (exponents 6) := by
  decide +kernel

theorem not_strict_image : ¬ StrictImage primes caps 0 exponents residue position value := by
  intro h
  have hh : (5 : Fin 7) = 6 := h.2 5 6 collision_data.1 collision_data.2.1
    collision_data.2.2.2.2
  exact (by decide : (5 : Fin 7) ≠ 6) hh

/-- Assign the extra45-image to the free divisor9. All five active classes
receive distinct nontrivial odd moduli dividing the smaller period45. -/
theorem assignment_valid :
    (∀ k, Active k → 1 < assigned k ∧ assigned k ∣ projected k ∧ assigned k ∣ 45) ∧
    (∀ k l, Active k → Active l → assigned k=assigned l → k=l) ∧
    (Finset.univ.filter (fun k => decide (Active k))).card=5 := by
  decide +kernel

theorem not_cover : ¬ ∀ x : ℤ, ∃ k, (modulus k : ℤ) ∣ x-residue k := by
  intro hc
  obtain ⟨k,hk⟩ := hc 7
  exact arithmetic_data.2.2.2.1 k hk

#print axioms position_predictable
#print axioms value_predictable
#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms not_strict_image
#print axioms assignment_valid
#print axioms not_cover
end Erdos7DivisorAssignmentExample
