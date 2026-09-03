import Submission.SplittingTreeCover

/-! Exact certificates that may reuse a congruence class on several tree leaves.
Repeated moduli are permitted only when the induced residue classes coincide.
This module supplies a certificate interface, not an odd covering witness. -/
namespace Erdos7SharedTreeCover
open Erdos7SplittingTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A finite family can be deduplicated by modulus when equal moduli describe
identical congruence classes. -/
theorem deduplicate {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ)
    (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hcoh : ∀ i j, m i = m j → (m i : ℤ) ∣ a i - a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  let S := Finset.univ.image m
  let J := {n : ℕ // n ∈ S}
  have he (j : J) : ∃ i, m i = j.val := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
    exact ⟨i, hi⟩
  let pick (j : J) : I := Classical.choose (he j)
  have hp (j : J) : m (pick j) = j.val := Classical.choose_spec (he j)
  apply Erdos7Reduction.arithmetic_formulation.mpr
  refine ⟨J, inferInstance, Subtype.val, (fun j => a (pick j)),
    Subtype.val_injective, ?_, ?_⟩
  · intro j
    simpa only [hp j] using hm (pick j)
  · intro x
    obtain ⟨i, hi⟩ := hc x
    let j : J := ⟨m i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    refine ⟨j, ?_⟩
    have heq : m i = m (pick j) := (hp j).symm
    have hh := dvd_add hi (hcoh i (pick j) heq)
    simpa only [sub_add_sub_cancel] using hh

/-- Coherence of the residue classes assigned to repeated leaf moduli. -/
def Consistent (T : Tree) (m : ℕ) (a : ℤ) : Prop :=
  ∀ i j, T.modulus i = T.modulus j →
    (T.modulus i : ℤ) ∣ T.residue m a i - T.residue m a j

/-- Unlike the injective-leaf certificate, this permits a class to be used in
several disjoint parts of the covering tree. -/
theorem consistent_odd_strict_cover (T : Tree) (hv : T.Valid 1)
    (ho : ∀ i, Odd (T.modulus i)) (hh : Consistent T 1 0) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  exact deduplicate T.modulus (T.residue 1 0)
    (fun i => ⟨T.nontrivial 1 hv i, ho i⟩) hh
    (fun x => T.covers 1 0 hv x (by simp))

/-- The simplest finite certificate: each period residue receives an odd
nontrivial divisor of the period, and equal labels have congruent residues. -/
theorem finite_period_certificate (N : ℕ) (hN : 0 < N) (d : Fin N → ℕ)
    (hd : ∀ r, 1 < d r ∧ Odd (d r) ∧ d r ∣ N)
    (hcoh : ∀ r s, d r = d s → (d r : ℤ) ∣ (r.val : ℤ) - s.val) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  let T : Tree := .split N (fun r => .leaf (d r))
  apply consistent_odd_strict_cover T
  · exact ⟨hN, fun r => ⟨(hd r).1, by simpa using (hd r).2.2⟩⟩
  · rintro ⟨r, k⟩
    exact (hd r).2.1
  · rintro ⟨r, k⟩ ⟨s, l⟩ h
    simpa [T, Tree.residue, Tree.modulus] using hcoh r s h

/-- Completeness of the finite-period certificate for finite arithmetic covers.
The labels are not required to be injective; coherence replaces that restriction. -/
theorem arithmetic_has_period_certificate {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hinj : Function.Injective m)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x - a i) :
    ∃ (N : ℕ) (_ : 0 < N) (d : Fin N → ℕ),
      (∀ r, 1 < d r ∧ Odd (d r) ∧ d r ∣ N) ∧
      (∀ r s, d r = d s → (d r : ℤ) ∣ (r.val : ℤ) - s.val) := by
  classical
  let N := ∏ i, m i
  have hN : 0 < N := Finset.prod_pos (fun i _ => by have := (hm i).1; omega)
  let pick (r : Fin N) : I := Classical.choose (hc r.val)
  have hp (r : Fin N) : (m (pick r) : ℤ) ∣ (r.val : ℤ) - a (pick r) :=
    Classical.choose_spec (hc r.val)
  refine ⟨N, hN, (fun r => m (pick r)), ?_, ?_⟩
  · intro r
    exact ⟨(hm _).1, (hm _).2, Finset.dvd_prod_of_mem m (Finset.mem_univ (pick r))⟩
  · intro r s hrs
    have he : pick r = pick s := hinj hrs
    have hpr := hp r
    have hps := hp s
    rw [← he] at hps
    have hh := dvd_sub hpr hps
    convert hh using 1; ring

/-- Coherent splitting trees characterize the original existential, not merely
an assumed restricted class of constructions. This is not an existence proof. -/
theorem shared_tree_characterization :
    (∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤) ↔
    ∃ T : Tree, T.Valid 1 ∧ (∀ i, Odd (T.modulus i)) ∧ Consistent T 1 0 := by
  constructor
  · intro hc
    obtain ⟨I, fi, m, a, hinj, hm, hcover⟩ :=
      Erdos7Reduction.arithmetic_formulation.mp hc
    letI : Fintype I := fi
    obtain ⟨N, hN, d, hd, hcoh⟩ := arithmetic_has_period_certificate m a hm hinj hcover
    let T : Tree := .split N (fun r => .leaf (d r))
    refine ⟨T, ⟨hN, fun r => ⟨(hd r).1, by simpa using (hd r).2.2⟩⟩, ?_, ?_⟩
    · rintro ⟨r,k⟩
      exact (hd r).2.1
    · rintro ⟨r,k⟩ ⟨s,l⟩ h
      simpa [T, Tree.residue, Tree.modulus] using hcoh r s h
  · rintro ⟨T, hv, ho, hh⟩
    exact consistent_odd_strict_cover T hv ho hh

/-- An even control with genuine repeated leaf labels: two distinct leaves
are both assigned the SAME class modulo2. -/
def repeatedControl : Tree := .split 4 ![.leaf 2, .leaf 4, .leaf 2, .leaf 4]

lemma repeatedControl_valid : repeatedControl.Valid 1 := by decide +kernel

/-- The two4-leaves in repeatedControl are incompatible, showing why mere
modulus reuse without residue coherence is not an admissible certificate. -/
lemma repeatedControl_inconsistent : ¬ Consistent repeatedControl 1 0 := by
  unfold Consistent
  decide +kernel

/-- An actual coherent reuse certificate for the standard even control. -/
def sharedEvenControl : Tree := .split 12 (fun r =>
  .leaf ((![2,3,2,6,2,4,2,3,2,4,2,12] : Fin 12 → ℕ) r))

lemma sharedEvenControl_valid : sharedEvenControl.Valid 1 := by decide +kernel
lemma sharedEvenControl_consistent : Consistent sharedEvenControl 1 0 := by
  unfold Consistent
  decide +kernel
lemma sharedEvenControl_not_injective : ¬ Function.Injective sharedEvenControl.modulus := by
  decide +kernel

#print axioms arithmetic_has_period_certificate
#print axioms shared_tree_characterization
#print axioms deduplicate
#print axioms consistent_odd_strict_cover
#print axioms finite_period_certificate
#print axioms repeatedControl_valid
#print axioms repeatedControl_inconsistent
#print axioms sharedEvenControl_consistent
#print axioms sharedEvenControl_not_injective
end Erdos7SharedTreeCover
