import FormalConjecturesUtil

/-!
# Arithmetic-progression length reductions for sets of natural numbers

These reductions use the imported definition
`Set.IsAPOfLengthWith S l a d :=
  ENat.card S = l ∧ S = {a + n • d | (n : ℕ) (_ : n < l)}`.
In particular, a constant parametrization cannot witness a length greater than one.
-/

namespace Erdos3Reduction

open Filter

/-- The cardinality condition forces a nonzero difference once the length exceeds one. -/
theorem isAPOfLengthWith_step_ne_zero {S : Set ℕ} {l : ℕ∞} {a d : ℕ}
    (hS : S.IsAPOfLengthWith l a d) (hl : 1 < l) : d ≠ 0 := by
  intro hd
  have hsub : S ⊆ ({a} : Set ℕ) := by
    rw [hS.eq]
    rintro x ⟨n, hn, rfl⟩
    simp [hd]
  have hcard : l ≤ 1 := by
    calc
      l = S.encard := hS.card.symm
      _ ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub
      _ = 1 := Set.encard_singleton a
  exact (not_le_of_gt hl) hcard

/-- With nonzero difference, the first `k` terms have cardinality exactly `k`. -/
theorem isAPOfLengthWith_prefix {a d : ℕ} (hd : d ≠ 0) (k : ℕ) :
    Set.IsAPOfLengthWith {a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))}
      (k : ℕ∞) a d := by
  refine ⟨?_, rfl⟩
  have hinj : Function.Injective (fun n : ℕ ↦ a + n • d) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd)
      (by simpa only [nsmul_eq_mul] using Nat.add_left_cancel hmn)
  simp only [exists_prop, ENat.coe_lt_coe]
  change ENat.card ((fun n : ℕ ↦ a + n • d) '' Set.Iio k) = k
  rw [ENat.card_image_of_injective _ _ hinj,
    ENat.card_eq_coe_fintype_card, Fintype.card_Iio, Nat.card_Iio]

/-- A finite initial segment of an AP, retaining its first term and difference.
The source length may be infinite; lengths zero and one need no nondegeneracy assumption. -/
theorem isAPOfLengthWith_truncate {S : Set ℕ} {l : ℕ∞} {k a d : ℕ}
    (hS : S.IsAPOfLengthWith l a d) (hkl : (k : ℕ∞) ≤ l) :
    ∃ T ⊆ S, T.IsAPOfLengthWith (k : ℕ∞) a d := by
  by_cases hk0 : k = 0
  · subst k
    exact ⟨∅, Set.empty_subset S, by simp⟩
  by_cases hk1 : k = 1
  · subst k
    refine ⟨{a}, ?_, by simp⟩
    intro x hx
    have hxa : x = a := hx
    subst x
    rw [hS.eq]
    exact ⟨0, lt_of_lt_of_le (by norm_num) hkl, by simp⟩
  have hk : 1 < (k : ℕ∞) := by
    exact_mod_cast (show 1 < k by omega)
  have hd : d ≠ 0 := isAPOfLengthWith_step_ne_zero hS (hk.trans_le hkl)
  refine ⟨{a + n • d | (n : ℕ) (_ : n < (k : ℕ∞))}, ?_,
    isAPOfLengthWith_prefix hd k⟩
  rw [hS.eq]
  rintro x ⟨n, hn, rfl⟩
  exact ⟨n, hn.trans_le hkl, rfl⟩

/-- Truncation to a natural length, also allowing an infinite source length. -/
theorem isAPOfLength_truncate_enat {S : Set ℕ} {l : ℕ∞} {k : ℕ}
    (hS : S.IsAPOfLength l) (hkl : (k : ℕ∞) ≤ l) :
    ∃ T ⊆ S, T.IsAPOfLength (k : ℕ∞) := by
  obtain ⟨a, d, hS⟩ := hS
  obtain ⟨T, hTS, hT⟩ := isAPOfLengthWith_truncate hS hkl
  exact ⟨T, hTS, a, d, hT⟩

/-- Every natural length at most the length of a natural-number set AP occurs in a subset. -/
theorem isAPOfLength_truncate {S : Set ℕ} {k l : ℕ}
    (hS : S.IsAPOfLength (l : ℕ∞)) (hkl : k ≤ l) :
    ∃ T ⊆ S, T.IsAPOfLength (k : ℕ∞) := by
  exact isAPOfLength_truncate_enat hS (by exact_mod_cast hkl)

/-- Containment of a progression is downward closed in its natural length. -/
theorem exists_isAPOfLength_mono {A : Set ℕ} {k l : ℕ} (hkl : k ≤ l)
    (hl : ∃ S ⊆ A, S.IsAPOfLength (l : ℕ∞)) :
    ∃ T ⊆ A, T.IsAPOfLength (k : ℕ∞) := by
  obtain ⟨S, hSA, hS⟩ := hl
  obtain ⟨T, hTS, hT⟩ := isAPOfLength_truncate hS hkl
  exact ⟨T, hTS.trans hSA, hT⟩

/-- Arbitrarily large natural AP lengths are equivalent to all natural AP lengths. -/
theorem frequently_isAPOfLength_iff_forall (A : Set ℕ) :
    (∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∀ k : ℕ, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞) := by
  rw [Filter.frequently_atTop]
  constructor
  · intro h k
    obtain ⟨l, hkl, hl⟩ := h k
    exact exists_isAPOfLength_mono hkl hl
  · intro h k
    exact ⟨k, le_rfl, h k⟩

/-- Failure of arbitrarily large AP lengths means that some fixed length is absent. -/
theorem not_frequently_isAPOfLength_iff (A : Set ℕ) :
    (¬ ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∃ k : ℕ, ¬ ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞) := by
  rw [frequently_isAPOfLength_iff_forall]
  exact not_forall

/-- The missing-length characterization, expressed as exclusion of every subset of `A`. -/
theorem not_frequently_isAPOfLength_iff_exists_missing_length (A : Set ℕ) :
    (¬ ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∃ k : ℕ, ∀ S ⊆ A, ¬ S.IsAPOfLength (k : ℕ∞) := by
  rw [not_frequently_isAPOfLength_iff]
  simp only [not_exists, not_and]

/-- A missing length can be chosen above any prescribed bound: a progression at a
larger length would truncate to one at the original missing length. -/
theorem not_frequently_isAPOfLength_iff_exists_missing_length_ge
    (A : Set ℕ) (b : ℕ) :
    (¬ ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∃ k : ℕ, b ≤ k ∧ ∀ S ⊆ A, ¬ S.IsAPOfLength (k : ℕ∞) := by
  rw [not_frequently_isAPOfLength_iff_exists_missing_length]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨max k b, le_max_right k b, ?_⟩
    intro S hSA hS
    obtain ⟨T, hTS, hT⟩ := isAPOfLength_truncate hS (le_max_left k b)
    exact hk T (hTS.trans hSA) hT
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

/-- In particular, one may choose a fixed missing length at least three.
This holds for every `A`, so it also holds when `A` is infinite. -/
theorem not_frequently_isAPOfLength_iff_exists_missing_length_ge_three (A : Set ℕ) :
    (¬ ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)) ↔
      ∃ k : ℕ, 3 ≤ k ∧ ∀ S ⊆ A, ¬ S.IsAPOfLength (k : ℕ∞) :=
  not_frequently_isAPOfLength_iff_exists_missing_length_ge A 3

end Erdos3Reduction
