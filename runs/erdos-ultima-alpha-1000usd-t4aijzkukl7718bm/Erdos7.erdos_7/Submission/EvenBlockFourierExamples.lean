import Submission.EvenBlockFourier

/-! Small kernel-checked controls for the even-block Fourier criterion.
None is an odd covering system or a settlement of Erdős Problem 7. -/
namespace Erdos7EvenBlockFourierExamples
open Finset Erdos7EvenBlockFourier
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def frequencies : Fin 6 → ZMod 105 := ![35,70,21,84,15,90]
def moduli : Fin 6 → ℕ := ![3,15,5,35,7,21]
def blocks : Fin 3 → Finset (Fin 6) := ![{0,1},{2,3},{4,5}]

lemma blocks_disjoint : Pairwise (fun j l => Disjoint (blocks j) (blocks l)) := by
  change ∀ j l : Fin 3, j ≠ l → Disjoint (blocks j) (blocks l)
  decide +kernel
lemma blocks_nonempty : ∀ j, (blocks j).Nonempty := by decide +kernel
lemma blocks_even : ∀ j, Even (blocks j).card := by decide +kernel
lemma moduli_arithmetic : Function.Injective moduli ∧
    (∀ i, 1 < moduli i ∧ Odd (moduli i)) ∧
    (∀ i, (moduli i : ZMod 105) * frequencies i = 0) := by
  decide +kernel

lemma zero_subsets_exact : ∀ u : Finset (Fin 6),
    (∑ i ∈ u, frequencies i = 0) ↔ ∃ s : Finset (Fin 3), s.biUnion blocks = u := by
  decide +kernel

lemma eight_zero_subsets :
    ((Finset.univ : Finset (Fin 6)).powerset.filter
      (fun u => ∑ i ∈ u, frequencies i = 0)).card = 8 := by
  decide +kernel

/-- The criterion tolerates eight zero representations, with arbitrary phases. -/
theorem control_noncoverage (a : Fin 6 → ℤ) :
    ¬ (∀ x : ℤ, ∃ i, (moduli i : ℤ) ∣ x - a i) :=
  not_arithmetic_cover_even_blocks (by decide) moduli a frequencies
    moduli_arithmetic.2.2 blocks blocks_disjoint blocks_nonempty blocks_even
    zero_subsets_exact

/-- Merely requiring all zero subsets to have even size is NOT sufficient. -/
def overlappingFrequencies : Fin 3 → ZMod 3 := ![1,1,2]
def overlappingResidues : Fin 3 → ZMod 3 := ![0,1,2]

lemma overlapping_all_zero_subsets_even : ∀ s : Finset (Fin 3),
    ∑ i ∈ s, overlappingFrequencies i = 0 → Even s.card := by
  decide +kernel

lemma overlapping_kernels_cover : ∀ x : ZMod 3, ∃ i,
    overlappingFrequencies i * (x - overlappingResidues i) = 0 := by
  decide +kernel

lemma overlapping_two_minimal_zeros :
    (∑ i ∈ ({0,2} : Finset (Fin 3)), overlappingFrequencies i = 0) ∧
    (∑ i ∈ ({1,2} : Finset (Fin 3)), overlappingFrequencies i = 0) ∧
    ¬ Disjoint ({0,2} : Finset (Fin 3)) {1,2} := by
  decide +kernel

/-- An odd block can vanish: this repeated-modulus control covers three points.
Its vanishing phase is exactly what the general block theorem forces. -/
def oddBlock : Fin 1 → Finset (Fin 3) := fun _ => Finset.univ

def oddBlockFrequencies : Fin 3 → ZMod 3 := fun _ => 1

lemma odd_block_zero_subsets : ∀ u : Finset (Fin 3),
    (∑ i ∈ u, oddBlockFrequencies i = 0) ↔
      ∃ s : Finset (Fin 1), s.biUnion oddBlock = u := by
  decide +kernel

lemma odd_block_kernels_cover : ∀ x : ZMod 3, ∃ i,
    oddBlockFrequencies i * (x - overlappingResidues i) = 0 := by
  decide +kernel

lemma odd_block_phase_control : ∃ j, Odd (oddBlock j).card ∧
    ∑ i ∈ oddBlock j, oddBlockFrequencies i * overlappingResidues i = 0 := by
  apply cover_forces_odd_block_phase (by decide) oddBlockFrequencies
    overlappingResidues oddBlock
  · intro j l hjl
    exact False.elim (hjl (Subsingleton.elim _ _))
  · decide +kernel
  · exact odd_block_zero_subsets
  · exact odd_block_kernels_cover

#print axioms control_noncoverage
#print axioms eight_zero_subsets
#print axioms overlapping_all_zero_subsets_even
#print axioms overlapping_kernels_cover
#print axioms odd_block_phase_control
end Erdos7EvenBlockFourierExamples
