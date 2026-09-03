import Submission.ArithmeticReduction

/-! Necessary core conditions for two-value restrictions of finite box covers.
These lemmas do not establish an odd-covering obstruction. -/
namespace Erdos7TwoValueCore
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- An irredundant atomic cover uses every value at every used coordinate. -/
theorem irredundant_all_values
    {I J : Type*} [DecidableEq I] (A : I → Type*)
    (supp : J → Finset I) (a : J → (i : I) → A i)
    (hc : ∀ x : (i : I) → A i, ∃ j, ∀ i ∈ supp j, x i = a j i)
    (hpriv : ∀ j, ∃ x : (i : I) → A i,
      ∀ k, k ≠ j → ¬ ∀ i ∈ supp k, x i = a k i)
    (i : I) (hi : ∃ j, i ∈ supp j) (v : A i) :
    ∃ j, i ∈ supp j ∧ a j i = v := by
  classical
  obtain ⟨j₀, hj₀⟩ := hi
  obtain ⟨x, hx⟩ := hpriv j₀
  obtain ⟨j, hj⟩ := hc (Function.update x i v)
  have hij : i ∈ supp j := by
    by_contra h
    have hm : ∀ k ∈ supp j, x k = a j k := by
      intro k hk
      have hki : k ≠ i := by intro he; subst k; exact h hk
      simpa [Function.update_of_ne hki] using hj k hk
    have he : j = j₀ := by by_contra hn; exact hx j hn hm
    exact h (he ▸ hj₀)
  have hv : v = a j i := by simpa using hj i hij
  exact ⟨j, hij, hv.symm⟩

/-- Tarsi's bound counts only coordinates actually used by the subcover. -/
theorem irredundant_used_bound
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (q : I → ℕ) (hq : ∀ i, 0 < q i)
    (supp : J → Finset I) (a : J → (i : I) → Fin (q i))
    (hc : ∀ x : (i : I) → Fin (q i), ∃ j, ∀ i ∈ supp j, x i = a j i)
    (hpriv : ∀ j, ∃ x : (i : I) → Fin (q i),
      ∀ k, k ≠ j → ¬ ∀ i ∈ supp k, x i = a k i) :
    (∑ i ∈ Finset.univ.biUnion supp, (q i - 1)) < Fintype.card J := by
  classical
  let U := Finset.univ.biUnion supp
  have hmem (j : J) (i : I) (hi : i ∈ supp j) : i ∈ U :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
  let t (j : J) : Finset U := Finset.univ.filter (fun i => i.val ∈ supp j)
  let b (j : J) (i : U) : Fin (q i.val) := a j i.val
  have hcov : ∀ x : (i : U) → Fin (q i.val), ∃ j, ∀ i ∈ t j, x i = b j i := by
    intro x
    let y (i : I) : Fin (q i) := if hi : i ∈ U then x ⟨i, hi⟩ else ⟨0, hq i⟩
    obtain ⟨j, hj⟩ := hc y
    refine ⟨j, ?_⟩
    intro i hi
    have his : i.val ∈ supp j := (Finset.mem_filter.mp hi).2
    simpa [y, i.property, b] using hj i.val his
  have hpv : ∀ j, ∃ x : (i : U) → Fin (q i.val),
      ∀ k, k ≠ j → ∃ i ∈ t k, x i ≠ b k i := by
    intro j
    obtain ⟨x, hx⟩ := hpriv j
    refine ⟨fun i => x i.val, ?_⟩
    intro k hkj
    have hn := hx k hkj
    push_neg at hn
    obtain ⟨i, hi, hxi⟩ := hn
    exact ⟨⟨i, hmem k i hi⟩, by simp [t, hi], hxi⟩
  have hus : ∀ i : U, ∃ j, i ∈ t j := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp i.property
    exact ⟨j, by simp [t, hj]⟩
  have hb := Erdos7Tarsi.irredundant_box_cover_tarsi_bound
    (fun i : U => q i.val) (fun i => hq i.val) t b hcov hpv hus
  change (∑ i : U, (q i.val - 1)) < Fintype.card J at hb
  rw [Finset.sum_coe_sort U (fun i => q i - 1)] at hb
  exact hb

/-- Any two-value restriction of a cover has an irredundant core. Its number
of clauses exceeds the number of used coordinates, and each used coordinate
sees exactly the two selected values. Selection is injective coordinatewise. -/
theorem exists_two_value_core
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (A : I → Type*) (supp : J → Finset I) (a : J → (i : I) → A i)
    (hc : ∀ x : (i : I) → A i, ∃ j, ∀ i ∈ supp j, x i = a j i)
    (z : (i : I) → Fin 2 → A i) (hz : ∀ i, Function.Injective (z i)) :
    ∃ s : Finset J,
      (s.biUnion supp).card < s.card ∧
      (∀ j ∈ s, ∀ i ∈ supp j, a j i ∈ Set.range (z i)) ∧
      (∀ i ∈ s.biUnion supp, ∀ v : Fin 2, ∃ j ∈ s,
        i ∈ supp j ∧ a j i = z i v) := by
  classical
  let P (s : Finset J) := ∀ x : I → Fin 2, ∃ j ∈ s,
    ∀ i ∈ supp j, z i (x i) = a j i
  have hp : P Finset.univ := by
    intro x
    obtain ⟨j, hj⟩ := hc (fun i => z i (x i))
    exact ⟨j, Finset.mem_univ _, hj⟩
  obtain ⟨s, hs⟩ := exists_minimal_of_wellFoundedLT P ⟨Finset.univ, hp⟩
  have hprivate (j : s) : ∃ x : I → Fin 2,
      (∀ i ∈ supp j.val, z i (x i) = a j.val i) ∧
      ∀ k ∈ s, k ≠ j.val → ¬ ∀ i ∈ supp k, z i (x i) = a k i := by
    have hn : ¬ P (s.erase j.val) := by
      intro h
      exact Finset.notMem_erase j.val s
        (hs.le_of_le h (Finset.erase_subset j.val s) j.property)
    change ¬ ∀ x : I → Fin 2, ∃ k ∈ s.erase j.val,
      ∀ i ∈ supp k, z i (x i) = a k i at hn
    push_neg at hn
    obtain ⟨x, hx⟩ := hn
    have hpr : ∀ k ∈ s, k ≠ j.val → ¬ ∀ i ∈ supp k, z i (x i) = a k i := by
      intro k hk hkj
      obtain ⟨i, hi, hni⟩ := hx k (Finset.mem_erase.mpr ⟨hkj, hk⟩)
      intro hall
      exact hni (hall i hi)
    obtain ⟨k, hk, hmk⟩ := hs.prop x
    have he : k = j.val := by by_contra h; exact hpr k hk h hmk
    exact ⟨x, he ▸ hmk, hpr⟩
  choose b hb hbp using hprivate
  have hcov : ∀ x : I → Fin 2, ∃ j : s, ∀ i ∈ supp j.val, x i = b j i := by
    intro x
    obtain ⟨j, hj, hx⟩ := hs.prop x
    refine ⟨⟨j, hj⟩, ?_⟩
    intro i hi
    exact hz i ((hx i hi).trans (hb ⟨j, hj⟩ i hi).symm)
  have hpriv : ∀ j : s, ∃ x : I → Fin 2,
      ∀ k : s, k ≠ j → ¬ ∀ i ∈ supp k.val, x i = b k i := by
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
  refine ⟨s, hcard, ?_, ?_⟩
  · intro j hj i hi
    exact ⟨b ⟨j, hj⟩ i, hb ⟨j, hj⟩ i hi⟩
  · intro i hi v
    have hiu : ∃ j : s, i ∈ supp j.val := by
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      exact ⟨⟨j, hj⟩, hij⟩
    obtain ⟨j, hij, hjv⟩ := irredundant_all_values (fun _ : I => Fin 2)
      (fun j : s => supp j.val) b hcov hpriv i hiu v
    exact ⟨j.val, j.property, hij, (hb j i hij).symm.trans (congrArg (z i) hjv)⟩

#print axioms irredundant_all_values
#print axioms irredundant_used_bound
#print axioms exists_two_value_core
end Erdos7TwoValueCore
