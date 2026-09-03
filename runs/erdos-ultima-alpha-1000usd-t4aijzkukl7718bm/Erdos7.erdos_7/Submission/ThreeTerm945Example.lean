import Submission.ThreeTermCharacterCancellation

/-! A small exact instantiation of the three-term criterion. Period945 was
already excluded by other arguments; this is not the original conjecture. -/
namespace Erdos7ThreeTerm945
open scoped BigOperators
open Erdos7ThreeTermCancellation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

 def weight : Fin 15 → ℕ := ![315,189,135,105,63,45,35,27,21,15,9,7,5,3,1]
 def modulus : Fin 15 → ℕ := ![3,5,7,9,15,21,27,35,45,63,105,135,189,315,945]
 def frequency (i : Fin 15) : ZMod 945 := weight i
 def tail : Finset (Fin 15) := {8,9,10,11,12,13,14}
 def reps : Fin 3 → Finset (Fin 15) :=
   ![{13,14}, ({8,12} : Finset (Fin 15))ᶜ, ({9,11,13,14} : Finset (Fin 15))ᶜ]

lemma total_weight : (∑ i : Fin 15, weight i) = 975 := by decide +kernel
lemma large_weight : ∀ i : Fin 15, i.val < 8 → 27 ≤ weight i := by decide +kernel
lemma tail_mem : ∀ i : Fin 15, 8 ≤ i.val → i ∈ tail := by decide +kernel

/-- Only128 small subsets are checked, rather than all32768 subsets of the
whole divisor family. Large frequencies cannot enter a sum of at most26. -/
lemma small_checks : ∀ s : ↥tail.powerset,
    ((∑ i ∈ s.val, weight i) = 4 ↔ s.val = {13,14}) ∧
    ((∑ i ∈ s.val, weight i) = 26 ↔
      s.val = {8,12} ∨ s.val = {9,11,13,14}) := by
  decide +kernel

lemma subset_tail {s : Finset (Fin 15)} (hs : (∑ i ∈ s, weight i) ≤ 26) : s ⊆ tail := by
  intro i hi
  have hw : weight i ≤ ∑ j ∈ s, weight j := Finset.single_le_sum (by simp) hi
  have hlow : ¬ i.val < 8 := by
    intro h
    have hh := large_weight i h
    omega
  exact tail_mem i (by omega)

lemma sum_four {s : Finset (Fin 15)} (hs : (∑ i ∈ s, weight i) = 4) : s = {13,14} := by
  have hsub := subset_tail (s := s) (by omega)
  exact (small_checks ⟨s,Finset.mem_powerset.mpr hsub⟩).1.mp hs

lemma sum_twenty_six {s : Finset (Fin 15)} (hs : (∑ i ∈ s, weight i) = 26) :
    s = {8,12} ∨ s = {9,11,13,14} := by
  have hsub := subset_tail (s := s) (by omega)
  exact (small_checks ⟨s,Finset.mem_powerset.mpr hsub⟩).2.mp hs

lemma sum_complement (s : Finset (Fin 15)) :
    (∑ i ∈ s, weight i) + (∑ i ∈ sᶜ, weight i) = 975 := by
  rw [Finset.sum_add_sum_compl, total_weight]

lemma representations : ∀ s : Finset (Fin 15),
    (∑ i ∈ s, frequency i = (4 : ZMod 945)) ↔ ∃ j, s = reps j := by
  intro s
  constructor
  · intro h
    have hcast : ((∑ i ∈ s, weight i : ℕ) : ZMod 945) = 4 := by
      simpa only [Nat.cast_sum, frequency] using h
    have hmod : (∑ i ∈ s, weight i) % 945 = 4 := by
      have hh := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast, ZMod.val_ofNat, Nat.reduceMod] using hh
    have htot := sum_complement s
    have he : (∑ i ∈ s, weight i) = 4 ∨ (∑ i ∈ s, weight i) = 949 := by omega
    rcases he with he | he
    · exact ⟨0,by simpa only [reps, Matrix.cons_val_zero] using sum_four he⟩
    · have hcomp : (∑ i ∈ sᶜ, weight i) = 26 := by omega
      rcases sum_twenty_six hcomp with h1 | h2
      · refine ⟨1, ?_⟩
        have hs := congrArg (fun z : Finset (Fin 15) => zᶜ) h1
        simpa [reps] using hs
      · refine ⟨2, ?_⟩
        have hs := congrArg (fun z : Finset (Fin 15) => zᶜ) h2
        simpa [reps] using hs
  · rintro ⟨j,rfl⟩
    have hh : ∀ j : Fin 3, ∑ i ∈ reps j, frequency i = (4 : ZMod 945) := by decide +kernel
    exact hh j

lemma reps_injective : Function.Injective reps := by decide +kernel
lemma annihilated : ∀ i : Fin 15, (modulus i : ZMod 945) * frequency i = 0 := by decide +kernel
lemma arithmetic_data : Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 945) := by decide +kernel
lemma signs_mixed : ¬ ((-1 : ℂ)^(reps 0).card = (-1 : ℂ)^(reps 1).card ∧
    (-1 : ℂ)^(reps 1).card = (-1 : ℂ)^(reps 2).card) := by
  have h0 : (reps 0).card = 2 := by decide +kernel
  have h1 : (reps 1).card = 13 := by decide +kernel
  intro h
  norm_num [h0,h1] at h

/-- No residues on this fifteen-modulus table cover the integers. This is a
finite-period consequence, not an unrestricted disproof of Erdos7.erdos_7. -/
theorem no_cover (a : Fin 15 → ℤ) : ¬ (∀ z : ℤ, ∃ i, (modulus i : ℤ) ∣ z-a i) :=
  not_arithmetic_cover_three_mixed (by decide : Odd 945) modulus a frequency
    annihilated reps reps_injective 4 representations signs_mixed

#print axioms small_checks
#print axioms representations
#print axioms no_cover
end Erdos7ThreeTerm945
