import FormalConjecturesUtil

/-! A genuine arithmetic partial-family control for paired selection.
The family is distinct, odd, divisor-complete, comparable-separated and
irredundant, but does NOT cover. After one branch is lost, its pair average
cannot replace the count of the selected surviving branch. -/
namespace Erdos7PairedAverageSelectionControl
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def modulus : Fin 11 → ℕ := ![3,5,7,9,15,21,35,45,63,105,315]
def residue : Fin 11 → ℤ := ![0,0,0,1,11,1,6,2,58,2,17]
def privatePoint : Fin 11 → ℤ := ![3,5,7,19,11,22,76,47,58,107,17]

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 315) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i j, i ≠ j → modulus i ∣ modulus j →
      ¬ (modulus i : ℤ) ∣ residue j-residue i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 8-residue i) := by
  decide +kernel

lemma complete_divisor_data : ∀ d : ↥(315 : ℕ).divisors,
    1 < d.val → ∃ i, modulus i = d.val := by
  decide +kernel

theorem all_nontrivial_divisors (d : ℕ) (hd : d ∣ 315) (h1 : 1 < d) :
    ∃ i, modulus i = d := by
  exact complete_divisor_data ⟨d,Nat.mem_divisors.mpr ⟨hd,by norm_num⟩⟩ h1

def currentAvoids (x : ℤ) : Prop :=
  ∀ i, ¬ 7 ∣ modulus i → ¬ (modulus i : ℤ) ∣ x-residue i

def futureCount (x : ℤ) : ℕ :=
  ∑ i, if 7 ∣ modulus i ∧ ((modulus i/7 : ℕ) : ℤ) ∣ x-residue i then 1 else 0

lemma branch_data :
    (31 : ℤ) % 9 = 4 ∧ (11 : ℤ) % 9 = 2 ∧
    (31 : ℤ) % 5 = 1 ∧ (11 : ℤ) % 5 = 1 ∧
    currentAvoids 31 ∧ ¬ currentAvoids 11 ∧
    futureCount 31 = 4 ∧ futureCount 11 = 2 := by
  unfold currentAvoids
  decide +kernel

lemma future_patterns :
    ((Finset.univ.filter (fun i : Fin 11 => 7 ∣ modulus i)).image
      (fun i => modulus i/7)) = {1,3,5,9,15,45} := by
  decide +kernel

/-- Both points share their5-coordinate and lie in different surviving
ternary branches. Only the left point survives the current3,5 layers. Its
future count is strictly larger than the pair average. -/
theorem selected_count_exceeds_average :
    currentAvoids 31 ∧ ¬ currentAvoids 11 ∧
      ((futureCount 31 : ℚ)+(futureCount 11 : ℚ))/2 < (futureCount 31 : ℚ) := by
  rcases branch_data with ⟨_,_,_,_,hl,hr,hc₁,hc₂⟩
  refine ⟨hl,hr,?_⟩
  rw [hc₁,hc₂]
  norm_num

/-- The gap persists with the mass1/5 of one actual quinary fiber. -/
lemma selected_integral_gap :
    ((futureCount 31 : ℚ)+(futureCount 11 : ℚ))/2/5 = 3/5 ∧
      (futureCount 31 : ℚ)/5 = 4/5 := by
  rcases branch_data with ⟨_,_,_,_,_,_,hc₁,hc₂⟩
  rw [hc₁,hc₂]
  norm_num

theorem not_cover : ¬ ∀ x : ℤ, ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  intro hc
  obtain ⟨i,hi⟩ := hc 8
  exact arithmetic_data.2.2.2.2 i hi

#print axioms arithmetic_data
#print axioms all_nontrivial_divisors
#print axioms selected_count_exceeds_average
#print axioms not_cover
end Erdos7PairedAverageSelectionControl
