import FormalConjecturesUtil

/-!
# Counting identities for finite projective planes

For a set of points `S`, `lineSize S l` is `|(S ∩ l)|`.  The first two
incidence moments imply a quadratic necessary condition for a set meeting
all lines in between `1` and `C` points.  All subtraction in the moments
and in the quadratic takes place in `ℤ`, not in `ℕ`.

This file develops counting foundations only.  It does not prove or disprove
the existence of a uniform constant in Erdős Problem 1159, and does not
import the conjectural statements in `Submission/Spec.lean`.
-/

open scoped BigOperators
open Configuration

namespace Erdos1159.Counting

/-- An integer version of the number of ordered pairs of distinct elements. -/
private lemma card_mul_card_sub_one {α : Type*} [DecidableEq α] (T : Finset α) :
    (T.card : ℤ) * ((T.card : ℤ) - 1) =
      ∑ a ∈ T, ∑ b ∈ T, if a ≠ b then (1 : ℤ) else 0 := by
  have hrow (a : α) (ha : a ∈ T) :
      (∑ b ∈ T, if a ≠ b then (1 : ℤ) else 0) = (T.card : ℤ) - 1 := by
    calc
      _ = ∑ b ∈ T, ((1 : ℤ) - if a = b then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases h : a = b <;> simp [h]
      _ = (T.card : ℤ) - 1 := by
        rw [Finset.sum_sub_distrib]
        simp [ha]
  rw [Finset.sum_congr rfl hrow]
  simp [mul_sub]

variable {P L : Type*} [Membership P L]

/-- The number of points of `S` on `l`, in the notation of the specification. -/
noncomputable def lineSize (S : Set P) (l : L) : ℕ :=
  (S ∩ {p : P | p ∈ l}).ncard

section FinitePlane

variable [Fintype P] [Fintype L] [ProjectivePlane P L]

/-- No intersection contains more than the `q + 1` points of its line. -/
theorem lineSize_le_order_add_one (S : Set P) (l : L) :
    lineSize S l ≤ ProjectivePlane.order P L + 1 := by
  calc
    lineSize S l ≤ ({p : P | p ∈ l} : Set P).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right
    _ = ProjectivePlane.order P L + 1 := by
      simpa only [Configuration.pointCount, Nat.card_coe_set_eq] using
        ProjectivePlane.pointCount_eq P l

/-- A set of points is bounded by the total `q² + q + 1` points of the plane. -/
theorem ncard_le_plane_size (S : Set P) :
    S.ncard ≤ ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1 := by
  have h := Set.ncard_le_card S
  rwa [Nat.card_eq_fintype_card, ProjectivePlane.card_points P L] at h

/-- First incidence moment: every point of `S` lies on exactly `q + 1` lines. -/
theorem first_moment (S : Set P) :
    (∑ l : L, (lineSize S l : ℤ)) =
      (S.ncard : ℤ) * ((ProjectivePlane.order P L : ℤ) + 1) := by
  classical
  let T := S.toFinset
  have hT : T.card = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
  have hline (l : L) : lineSize S l = (T.filter (fun p => p ∈ l)).card := by
    rw [lineSize, Set.ncard_eq_toFinset_card']
    congr 1
    ext p
    simp [T]
  have hpoint (p : P) :
      (∑ l : L, if p ∈ l then (1 : ℤ) else 0) =
        (ProjectivePlane.order P L : ℤ) + 1 := by
    have hcard : (Finset.univ.filter (fun l : L => p ∈ l)).card =
        ProjectivePlane.order P L + 1 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact ProjectivePlane.lineCount_eq L p
    rw [Finset.sum_boole, hcard, Nat.cast_add, Nat.cast_one]
  calc
    _ = ∑ l : L, ∑ p ∈ T, if p ∈ l then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_boole, hline]
    _ = ∑ p ∈ T, ∑ l : L, if p ∈ l then (1 : ℤ) else 0 := Finset.sum_comm
    _ = ∑ p ∈ T, ((ProjectivePlane.order P L : ℤ) + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hpoint p
    _ = _ := by simp [hT]

/-- The first moment also holds without casts, since it involves no subtraction. -/
theorem first_moment_nat (S : Set P) :
    (∑ l : L, lineSize S l) = S.ncard * (ProjectivePlane.order P L + 1) := by
  exact_mod_cast first_moment (L := L) S

/-- Second factorial moment: every ordered pair of distinct points determines one line. -/
theorem second_factorial_moment (S : Set P) :
    (∑ l : L, (lineSize S l : ℤ) * ((lineSize S l : ℤ) - 1)) =
      (S.ncard : ℤ) * ((S.ncard : ℤ) - 1) := by
  classical
  let T := S.toFinset
  have hT : T.card = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
  have hline (l : L) : lineSize S l = (T.filter (fun p => p ∈ l)).card := by
    rw [lineSize, Set.ncard_eq_toFinset_card']
    congr 1
    ext p
    simp [T]
  have hpair (p r : P) (hpr : p ≠ r) :
      (∑ l : L, if p ∈ l ∧ r ∈ l then (1 : ℤ) else 0) = 1 := by
    obtain ⟨l, hl, huniq⟩ := HasLines.existsUnique_line P L p r hpr
    rw [Finset.sum_eq_single l]
    · simp [hl]
    · intro m hm hml
      exact if_neg (fun hm => hml (huniq m hm))
    · simp
  calc
    _ = ∑ l : L, ∑ p ∈ T, ∑ r ∈ T,
        if p ∈ l ∧ r ∈ l ∧ p ≠ r then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hline, card_mul_card_sub_one]
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpl : p ∈ l
      · simp only [hpl, if_true, true_and]
        apply Finset.sum_congr rfl
        intro r hr
        by_cases hrl : r ∈ l <;> simp [hrl]
      · simp [hpl]
    _ = ∑ p ∈ T, ∑ r ∈ T, ∑ l : L,
        if p ∈ l ∧ r ∈ l ∧ p ≠ r then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_comm
    _ = ∑ p ∈ T, ∑ r ∈ T, if p ≠ r then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hpr : p ≠ r
      · simpa [hpr] using hpair p r hpr
      · simp [hpr]
    _ = _ := by rw [← card_mul_card_sub_one, hT]

/--
A necessary quadratic inequality for line intersections in `[1, C]`.
Writing `q = order P L` and `s = |S|`, this is
`s² - (C(q + 1) + 1)s + C(q² + q + 1) ≤ 0` over the integers.
-/
theorem quadratic_inequality (S : Set P) (C : ℤ)
    (h : ∀ l : L, 1 ≤ (lineSize S l : ℤ) ∧ (lineSize S l : ℤ) ≤ C) :
    (S.ncard : ℤ) ^ 2 - (C * ((ProjectivePlane.order P L : ℤ) + 1) + 1) *
      (S.ncard : ℤ) +
      C * ((ProjectivePlane.order P L : ℤ) ^ 2 + (ProjectivePlane.order P L : ℤ) + 1)
      ≤ 0 := by
  have hsum :
      (∑ l : L, (lineSize S l : ℤ) * ((lineSize S l : ℤ) - 1)) ≤
        ∑ l : L, (C * (lineSize S l : ℤ) - C) := by
    apply Finset.sum_le_sum
    intro l hl
    have hprod := mul_nonneg (sub_nonneg.mpr (h l).1) (sub_nonneg.mpr (h l).2)
    nlinarith
  rw [second_factorial_moment, Finset.sum_sub_distrib, ← Finset.mul_sum,
    first_moment] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card L : ℤ) =
      (ProjectivePlane.order P L : ℤ) ^ 2 + (ProjectivePlane.order P L : ℤ) + 1 := by
    exact_mod_cast ProjectivePlane.card_lines P L
  rw [hcard] at hsum
  nlinarith only [hsum]

/-- The quadratic necessary condition with the natural-number bounds used in `Spec.lean`. -/
theorem quadratic_inequality_nat (S : Set P) (C : ℕ)
    (h : ∀ l : L, 1 ≤ lineSize S l ∧ lineSize S l ≤ C) :
    (S.ncard : ℤ) ^ 2 - ((C : ℤ) * ((ProjectivePlane.order P L : ℤ) + 1) + 1) *
      (S.ncard : ℤ) +
      (C : ℤ) * ((ProjectivePlane.order P L : ℤ) ^ 2 +
        (ProjectivePlane.order P L : ℤ) + 1) ≤ 0 := by
  apply quadratic_inequality S (C : ℤ)
  intro l
  exact ⟨by exact_mod_cast (h l).1, by exact_mod_cast (h l).2⟩

/--
For order at least five, an integer upper bound on all the nonzero line
intersections must be at least four.  For `C ≤ 3`, the quadratic for `C = 3`
has negative discriminant; the proof uses a completed square.
-/
theorem four_le_of_order_ge_five_int (S : Set P) (C : ℤ)
    (hq : 5 ≤ ProjectivePlane.order P L)
    (h : ∀ l : L, 1 ≤ (lineSize S l : ℤ) ∧ (lineSize S l : ℤ) ≤ C) :
    4 ≤ C := by
  by_contra hC
  have hC3 : C ≤ 3 := by omega
  have h3 := quadratic_inequality S 3 (fun l => ⟨(h l).1, (h l).2.trans hC3⟩)
  have hq' : (5 : ℤ) ≤ (ProjectivePlane.order P L : ℤ) := by exact_mod_cast hq
  nlinarith only [h3, hq',
    sq_nonneg (2 * (S.ncard : ℤ) - (3 * (ProjectivePlane.order P L : ℤ) + 4)),
    sq_nonneg ((ProjectivePlane.order P L : ℤ) - 5)]

end FinitePlane

/--
The order-five obstruction in precisely the `Set.ncard` notation of the
specification.  Only finiteness, not chosen enumerations, is needed here.
This is a necessary lower bound on `C`, not a solution of the uniform-constant
existence problem.
-/
theorem four_le_of_order_ge_five [Finite P] [Finite L] [ProjectivePlane P L]
    (S : Set P) (C : ℕ) (hq : 5 ≤ ProjectivePlane.order P L)
    (h : ∀ l : L, 1 ≤ (S ∩ {p : P | p ∈ l}).ncard ∧
      (S ∩ {p : P | p ∈ l}).ncard ≤ C) :
    4 ≤ C := by
  letI := Fintype.ofFinite P
  letI := Fintype.ofFinite L
  have hC : (4 : ℤ) ≤ (C : ℤ) := by
    apply four_le_of_order_ge_five_int S (C : ℤ) hq
    intro l
    exact ⟨by exact_mod_cast (h l).1, by exact_mod_cast (h l).2⟩
  exact_mod_cast hC

end Erdos1159.Counting

#print axioms Erdos1159.Counting.lineSize_le_order_add_one
#print axioms Erdos1159.Counting.ncard_le_plane_size
#print axioms Erdos1159.Counting.first_moment
#print axioms Erdos1159.Counting.first_moment_nat
#print axioms Erdos1159.Counting.second_factorial_moment
#print axioms Erdos1159.Counting.quadratic_inequality
#print axioms Erdos1159.Counting.quadratic_inequality_nat
#print axioms Erdos1159.Counting.four_le_of_order_ge_five_int
#print axioms Erdos1159.Counting.four_le_of_order_ge_five
