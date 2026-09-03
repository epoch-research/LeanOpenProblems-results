import FormalConjecturesUtil

/-!
# Elementary reductions for the Erdős–Turán representation problem

These lemmas concern the genuine ordered representation count `sumRep`. They do
not prove or refute the Erdős–Turán conjecture and do not import `Submission.Spec`.
The equivalences below are reductions only: in particular, they do not construct
a bounded asymptotic basis.
-/

open Filter Set AdditiveCombinatorics
open scoped Pointwise

namespace Erdos28.Reduction

/-- There are at most `n + 1` ordered representations of `n`. -/
theorem sumRep_le_succ (A : Set ℕ) (n : ℕ) : sumRep A n ≤ n + 1 := by
  classical
  rw [sumRep_def, ← Finset.Nat.card_antidiagonal n]
  exact Finset.card_filter_le _ _

/-- Positive representation count is exactly membership in the sumset. -/
theorem sumRep_pos_iff (A : Set ℕ) (n : ℕ) :
    0 < sumRep A n ↔ n ∈ A + A := by
  classical
  rw [sumRep_def, Finset.card_pos]
  constructor
  · rintro ⟨⟨a, b⟩, hp⟩
    rcases Finset.mem_filter.mp hp with ⟨hab, ha, hb⟩
    exact Set.mem_add.mpr ⟨a, ha, b, hb, Finset.mem_antidiagonal.mp hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hab, ha, hb⟩⟩

/-- For a natural-valued sequence, ENat limsup is top precisely when every
natural threshold is exceeded arbitrarily far out. -/
theorem enat_limsup_eq_top_iff_tail_unbounded (u : ℕ → ℕ) :
    limsup (fun n : ℕ ↦ (u n : ℕ∞)) atTop = ⊤ ↔
      ∀ K N : ℕ, ∃ n ≥ N, K < u n := by
  rw [← top_le_iff, le_limsup_iff]
  constructor
  · intro h K N
    have hf := h (K : ℕ∞) (by simp)
    rcases Filter.frequently_atTop.mp hf N with ⟨n, hn, hK⟩
    exact ⟨n, hn, by exact_mod_cast hK⟩
  · intro h y hy
    lift y to ℕ using ne_top_of_lt hy
    apply Filter.frequently_atTop.mpr
    intro N
    rcases h y N with ⟨n, hn, hK⟩
    exact ⟨n, hn, by exact_mod_cast hK⟩

/-- Global unboundedness of `sumRep` already gives unboundedness on every tail.
The pointwise bound rules out obtaining arbitrarily large values in a prefix. -/
theorem sumRep_unbounded_iff_tail_unbounded (A : Set ℕ) :
    (∀ K : ℕ, ∃ n : ℕ, K < sumRep A n) ↔
      ∀ K N : ℕ, ∃ n ≥ N, K < sumRep A n := by
  constructor
  · intro h K N
    rcases h (K + N) with ⟨n, hn⟩
    have hb := sumRep_le_succ A n
    exact ⟨n, by omega, by omega⟩
  · intro h K
    rcases h K 0 with ⟨n, _, hn⟩
    exact ⟨n, hn⟩

/-- The tail version of the limsup criterion for representation counts. -/
theorem sumRep_limsup_eq_top_iff_tail_unbounded (A : Set ℕ) :
    limsup (fun n : ℕ ↦ (sumRep A n : ℕ∞)) atTop = ⊤ ↔
      ∀ K N : ℕ, ∃ n ≥ N, K < sumRep A n :=
  enat_limsup_eq_top_iff_tail_unbounded (sumRep A)

/-- ENat limsup is top if and only if the representation counts have no global
natural-number bound. No sumset hypothesis is needed for this equivalence. -/
theorem sumRep_limsup_eq_top_iff_unbounded (A : Set ℕ) :
    limsup (fun n : ℕ ↦ (sumRep A n : ℕ∞)) atTop = ⊤ ↔
      ∀ K : ℕ, ∃ n : ℕ, K < sumRep A n :=
  (sumRep_limsup_eq_top_iff_tail_unbounded A).trans
    (sumRep_unbounded_iff_tail_unbounded A).symm

/-- Failure of the limsup conclusion for a fixed set is a global finite bound,
not merely an eventual bound. -/
theorem sumRep_limsup_ne_top_iff_bounded (A : Set ℕ) :
    limsup (fun n : ℕ ↦ (sumRep A n : ℕ∞)) atTop ≠ ⊤ ↔
      ∃ C : ℕ, ∀ n : ℕ, sumRep A n ≤ C := by
  rw [ne_eq, sumRep_limsup_eq_top_iff_unbounded]
  push_neg
  rfl

/-- Logical reduction of the negated universal assertion to a bounded
asymptotic basis. Neither side of this equivalence is asserted on its own. -/
theorem not_forall_limsup_eq_top_iff_exists_bounded :
    (¬ ∀ A : Set ℕ, (A + A)ᶜ.Finite →
      limsup (fun n : ℕ ↦ (sumRep A n : ℕ∞)) atTop = ⊤) ↔
    ∃ A : Set ℕ, (A + A)ᶜ.Finite ∧
      ∃ C : ℕ, ∀ n : ℕ, sumRep A n ≤ C := by
  simp only [not_forall, exists_prop, sumRep_limsup_ne_top_iff_bounded]

/-- Projection to the first coordinate bounds the number of antidiagonal
pairs whose first coordinate belongs to a given finite set. -/
theorem antidiagonal_filter_fst_card_le (F : Finset ℕ) (n : ℕ) :
    ((Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.1 ∈ F)).card ≤ F.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    exact hp.2
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact (Finset.antidiagonal_congr hp.1 hq.1).mpr hpq

/-- The analogous bound using the second coordinate. -/
theorem antidiagonal_filter_snd_card_le (F : Finset ℕ) (n : ℕ) :
    ((Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.2 ∈ F)).card ≤ F.card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    exact hp.2
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact (Finset.antidiagonal_congr' hp.1 hq.1).mpr hpq

/-- Adjoining a finite set creates at most `2 * F.card` additional ordered
representations of any one integer. This does not require disjointness. -/
theorem sumRep_union_finset_le (A : Set ℕ) (F : Finset ℕ) (n : ℕ) :
    sumRep (A ∪ (F : Set ℕ)) n ≤ sumRep A n + 2 * F.card := by
  classical
  let S := (Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.1 ∈ A ∧ p.2 ∈ A)
  let L := (Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.1 ∈ F)
  let R := (Finset.antidiagonal n).filter (fun p : ℕ × ℕ ↦ p.2 ∈ F)
  have hL : L.card ≤ F.card := antidiagonal_filter_fst_card_le F n
  have hR : R.card ≤ F.card := antidiagonal_filter_snd_card_le F n
  have hS : S.card = sumRep A n := (sumRep_def A n).symm
  calc
    sumRep (A ∪ (F : Set ℕ)) n ≤ ((S ∪ L) ∪ R).card := by
      rw [sumRep_def]
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter, Set.mem_union, Finset.mem_coe] at hp
      simp only [Finset.mem_union, S, L, R, Finset.mem_filter]
      tauto
    _ ≤ (S ∪ L).card + R.card := Finset.card_union_le _ _
    _ ≤ (S.card + L.card) + R.card :=
      Nat.add_le_add_right (Finset.card_union_le S L) _
    _ ≤ sumRep A n + 2 * F.card := by omega

/-- Cofiniteness of the sumset is equivalently the existence of a threshold
past which every integer is represented. -/
theorem sumset_compl_finite_iff_tail (A : Set ℕ) :
    (A + A)ᶜ.Finite ↔ ∃ N : ℕ, ∀ n ≥ N, n ∈ A + A := by
  constructor
  · intro h
    rcases h.bddAbove with ⟨N, hN⟩
    refine ⟨N + 1, ?_⟩
    intro n hn
    by_contra hnot
    have hle : n ≤ N := hN hnot
    omega
  · rintro ⟨N, hN⟩
    apply (Finset.range N).finite_toSet.subset
    intro n hn
    change n ∈ Finset.range N
    apply Finset.mem_range.mpr
    by_contra hnot
    exact hn (hN n (by omega))

/-- Filling the finite initial interval turns a tail basis into a full basis.
The extra endpoint ensures that the adjoined set contains zero even if `N = 0`. -/
theorem finite_filling_sumset_eq_univ (A : Set ℕ) (N : ℕ)
    (hN : ∀ n ≥ N, n ∈ A + A) :
    (A ∪ (Finset.range (N + 1) : Set ℕ)) +
      (A ∪ (Finset.range (N + 1) : Set ℕ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  by_cases hn : N ≤ n
  · rcases Set.mem_add.mp (hN n hn) with ⟨a, ha, b, hb, hab⟩
    exact Set.mem_add.mpr ⟨a, Or.inl ha, b, Or.inl hb, hab⟩
  · apply Set.mem_add.mpr
    refine ⟨n, Or.inr ?_, 0, Or.inr ?_, by simp⟩
    · exact Finset.mem_range.mpr (by omega)
    · simp

/-- A bounded cofinite basis can be enlarged to a full basis by precisely the
finite filling in the statement, with explicit bound `C + 2 * (N + 1)`. -/
theorem finite_filling_normalization (A : Set ℕ) (hA : (A + A)ᶜ.Finite)
    (C : ℕ) (hC : ∀ n : ℕ, sumRep A n ≤ C) :
    ∃ N : ℕ, ∃ B : Set ℕ,
      B = A ∪ (Finset.range (N + 1) : Set ℕ) ∧
      B + B = Set.univ ∧ ∀ n : ℕ, sumRep B n ≤ C + 2 * (N + 1) := by
  rcases (sumset_compl_finite_iff_tail A).mp hA with ⟨N, hN⟩
  refine ⟨N, A ∪ (Finset.range (N + 1) : Set ℕ), rfl,
    finite_filling_sumset_eq_univ A N hN, ?_⟩
  intro n
  calc
    sumRep (A ∪ (Finset.range (N + 1) : Set ℕ)) n ≤
        sumRep A n + 2 * (Finset.range (N + 1)).card :=
      sumRep_union_finset_le A (Finset.range (N + 1)) n
    _ ≤ C + 2 * (N + 1) := by
      simpa only [Finset.card_range] using
        Nat.add_le_add_right (hC n) (2 * (N + 1))

/-- The existence of a globally bounded cofinite basis is equivalent to the
existence of a globally bounded full basis. -/
theorem exists_bounded_cofinite_iff_exists_bounded_full :
    (∃ A : Set ℕ, (A + A)ᶜ.Finite ∧
      ∃ C : ℕ, ∀ n : ℕ, sumRep A n ≤ C) ↔
    ∃ B : Set ℕ, B + B = Set.univ ∧
      ∃ D : ℕ, ∀ n : ℕ, sumRep B n ≤ D := by
  constructor
  · rintro ⟨A, hA, C, hC⟩
    rcases finite_filling_normalization A hA C hC with ⟨N, B, _, hB, hbound⟩
    exact ⟨B, hB, C + 2 * (N + 1), hbound⟩
  · rintro ⟨B, hB, D, hD⟩
    refine ⟨B, ?_, D, hD⟩
    rw [hB, Set.compl_univ]
    exact Set.finite_empty

/-- Combining the logical reduction and finite filling. This is still only an
equivalence, not a proof that a bounded full basis exists. -/
theorem not_forall_limsup_eq_top_iff_exists_bounded_full :
    (¬ ∀ A : Set ℕ, (A + A)ᶜ.Finite →
      limsup (fun n : ℕ ↦ (sumRep A n : ℕ∞)) atTop = ⊤) ↔
    ∃ B : Set ℕ, B + B = Set.univ ∧
      ∃ D : ℕ, ∀ n : ℕ, sumRep B n ≤ D :=
  not_forall_limsup_eq_top_iff_exists_bounded.trans
    exists_bounded_cofinite_iff_exists_bounded_full

end Erdos28.Reduction

/-
## Verification

From `/workspace/leanproject`, run:

```
lake env lean Submission/Reduction.lean
lake env lean -DwarningAsError=true Submission/Reduction.lean
```

The commands below audit every theorem in this file. Their axiom lists must be
contained in `{propext, Classical.choice, Quot.sound}`. No declaration from the
problem specification is used, and neither the conjecture nor its negation is
proved here.
-/

#print axioms Erdos28.Reduction.sumRep_le_succ
#print axioms Erdos28.Reduction.sumRep_pos_iff
#print axioms Erdos28.Reduction.enat_limsup_eq_top_iff_tail_unbounded
#print axioms Erdos28.Reduction.sumRep_unbounded_iff_tail_unbounded
#print axioms Erdos28.Reduction.sumRep_limsup_eq_top_iff_tail_unbounded
#print axioms Erdos28.Reduction.sumRep_limsup_eq_top_iff_unbounded
#print axioms Erdos28.Reduction.sumRep_limsup_ne_top_iff_bounded
#print axioms Erdos28.Reduction.not_forall_limsup_eq_top_iff_exists_bounded
#print axioms Erdos28.Reduction.antidiagonal_filter_fst_card_le
#print axioms Erdos28.Reduction.antidiagonal_filter_snd_card_le
#print axioms Erdos28.Reduction.sumRep_union_finset_le
#print axioms Erdos28.Reduction.sumset_compl_finite_iff_tail
#print axioms Erdos28.Reduction.finite_filling_sumset_eq_univ
#print axioms Erdos28.Reduction.finite_filling_normalization
#print axioms Erdos28.Reduction.exists_bounded_cofinite_iff_exists_bounded_full
#print axioms Erdos28.Reduction.not_forall_limsup_eq_top_iff_exists_bounded_full
