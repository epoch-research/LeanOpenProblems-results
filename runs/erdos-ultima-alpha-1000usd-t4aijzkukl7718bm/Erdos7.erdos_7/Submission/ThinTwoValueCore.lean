import Submission.TwoValueCore

/-! Two-value cores for thin sections rather than singleton sections.
This permits restricting an entire prime-power coordinate to an antipodal pair.
It does not establish an odd-covering obstruction. -/
namespace Erdos7ThinTwoValueCore
open Erdos7TwoValueCore
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A two-value restriction of a box cover has a genuinely covering core,
provided each box section contains at most one selected value. The core has
more boxes than used coordinates and uses both symbols at each coordinate. -/
theorem exists_thin_two_value_core
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : I → Type*) (supp : J → Finset I) (B : J → (i : I) → Set (A i))
    (hc : ∀ x : (i : I) → A i, ∃ j, ∀ i ∈ supp j, x i ∈ B j i)
    (z : (i : I) → Fin 2 → A i)
    (hthin : ∀ j i, i ∈ supp j → ∀ r s : Fin 2,
      z i r ∈ B j i → z i s ∈ B j i → r = s) :
    ∃ s : Finset J,
      (∀ u : I → Fin 2, ∃ j ∈ s, ∀ i ∈ supp j, z i (u i) ∈ B j i) ∧
      (s.biUnion supp).card < s.card ∧
      (∀ j ∈ s, ∀ i ∈ supp j, ∃ v : Fin 2, z i v ∈ B j i) ∧
      (∀ i ∈ s.biUnion supp, ∀ v : Fin 2, ∃ j ∈ s,
        i ∈ supp j ∧ z i v ∈ B j i) := by
  classical
  let P (s : Finset J) := ∀ u : I → Fin 2, ∃ j ∈ s,
    ∀ i ∈ supp j, z i (u i) ∈ B j i
  have hp : P Finset.univ := by
    intro u
    obtain ⟨j, hj⟩ := hc (fun i => z i (u i))
    exact ⟨j, Finset.mem_univ _, hj⟩
  obtain ⟨s, hs⟩ := exists_minimal_of_wellFoundedLT P ⟨Finset.univ, hp⟩
  have hprivate (j : s) : ∃ u : I → Fin 2,
      (∀ i ∈ supp j.val, z i (u i) ∈ B j.val i) ∧
      ∀ k ∈ s, k ≠ j.val → ¬ ∀ i ∈ supp k, z i (u i) ∈ B k i := by
    have hn : ¬ P (s.erase j.val) := by
      intro h
      exact Finset.notMem_erase j.val s
        (hs.le_of_le h (Finset.erase_subset j.val s) j.property)
    change ¬ ∀ u : I → Fin 2, ∃ k ∈ s.erase j.val,
      ∀ i ∈ supp k, z i (u i) ∈ B k i at hn
    push_neg at hn
    obtain ⟨u, hu⟩ := hn
    have hpr : ∀ k ∈ s, k ≠ j.val → ¬ ∀ i ∈ supp k, z i (u i) ∈ B k i := by
      intro k hk hkj
      obtain ⟨i, hi, hni⟩ := hu k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
      exact fun hall => hni (hall i hi)
    obtain ⟨k, hk, hmk⟩ := hs.prop u
    have he : k = j.val := by by_contra h; exact hpr k hk h hmk
    exact ⟨u, he ▸ hmk, hpr⟩
  choose b hb hbp using hprivate
  have hcov : ∀ u : I → Fin 2, ∃ j : s, ∀ i ∈ supp j.val, u i = b j i := by
    intro u
    obtain ⟨j, hj, hu⟩ := hs.prop u
    refine ⟨⟨j, hj⟩, ?_⟩
    intro i hi
    exact hthin j i hi (u i) (b ⟨j, hj⟩ i) (hu i hi) (hb ⟨j, hj⟩ i hi)
  have hpriv : ∀ j : s, ∃ u : I → Fin 2,
      ∀ k : s, k ≠ j → ¬ ∀ i ∈ supp k.val, u i = b k i := by
    intro j
    refine ⟨b j, ?_⟩
    intro k hkj hh
    apply hbp j k.val k.property (fun he => hkj (Subtype.ext he))
    intro i hi
    rw [hh i hi]
    exact hb k i hi
  have hu : Finset.univ.biUnion (fun j : s => supp j.val) = s.biUnion supp := by
    ext i
    simp
  have hbound := irredundant_used_bound (fun _ : I => 2) (by intro; norm_num)
    (fun j : s => supp j.val) b hcov hpriv
  have hcard : (s.biUnion supp).card < s.card := by
    rw [hu] at hbound
    simpa only [Nat.reduceSub, Finset.sum_const, smul_eq_mul, mul_one,
      Fintype.card_coe] using hbound
  refine ⟨s, hs.prop, hcard, ?_, ?_⟩
  · intro j hj i hi
    exact ⟨b ⟨j, hj⟩ i, hb ⟨j, hj⟩ i hi⟩
  · intro i hi v
    have hiu : ∃ j : s, i ∈ supp j.val := by
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      exact ⟨⟨j, hj⟩, hij⟩
    obtain ⟨j, hij, hjv⟩ := irredundant_all_values (fun _ : I => Fin 2)
      (fun j : s => supp j.val) b hcov hpriv i hiu v
    exact ⟨j.val, j.property, hij, hjv ▸ hb j i hij⟩

#print axioms exists_thin_two_value_core
end Erdos7ThinTwoValueCore
