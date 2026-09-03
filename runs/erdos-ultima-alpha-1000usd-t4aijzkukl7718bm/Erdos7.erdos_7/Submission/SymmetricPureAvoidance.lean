import FormalConjecturesUtil

/-!
A symmetric complement for a finite pure-prime-power family. This is a
preparation for antipodal restrictions, not a solution of the odd-cover problem.
-/
namespace Erdos7SymmetricPureAvoidance
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def geometricMass (r : ℚ) (E : ℕ) : ℚ :=
  ∑ j ∈ Finset.range E, r^(j+1)

lemma geometricMass_le_half (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 1/3) (E : ℕ) :
    geometricMass r E ≤ (1-r^E)/2 := by
  induction E with
  | zero => simp [geometricMass]
  | succ E ih =>
    have he : geometricMass r (E+1) = geometricMass r E+r^(E+1) := by
      simp [geometricMass, Finset.sum_range_succ]
    rw [he, pow_succ]
    have h := mul_nonneg (pow_nonneg hr E) (show 0 ≤ 1-3*r by linarith)
    nlinarith

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Remove a distinguished invariant first-level class, and both reflections
of each subsequent class. No disjointness of the subsequent classes is needed. -/
def bad (σ : X → X) (Z : Finset X) (B : ℕ → Finset X) (E : ℕ) : Finset X :=
  Z ∪ (Finset.range E).biUnion (fun j => B j ∪ (B j).image σ)

def good (σ : X → X) (Z : Finset X) (B : ℕ → Finset X) (E : ℕ) : Finset X :=
  Finset.univ \ bad σ Z B E

lemma bad_card_bound (σ : X → X) (Z : Finset X) (B : ℕ → Finset X)
    (E : ℕ) (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 1/3)
    (hZ : (Z.card : ℚ) ≤ Fintype.card X*r)
    (hB : ∀ j < E, ((B j).card : ℚ) ≤ Fintype.card X*r^(j+2)) :
    ((bad σ Z B E).card : ℚ) ≤ 2*(Fintype.card X : ℚ)/3 := by
  have hcard : (bad σ Z B E).card ≤ Z.card +
      ∑ j ∈ Finset.range E, ((B j).card+(B j).card) := by
    apply (Finset.card_union_le Z _).trans
    apply Nat.add_le_add_left
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro j _
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_image_le _)
  have hq : ((bad σ Z B E).card : ℚ) ≤ (Z.card : ℚ) +
      ∑ j ∈ Finset.range E, (((B j).card : ℚ)+(B j).card) := by
    exact_mod_cast hcard
  have hb : (∑ j ∈ Finset.range E, (((B j).card : ℚ)+(B j).card)) ≤
      ∑ j ∈ Finset.range E, (2*(Fintype.card X : ℚ)*r^(j+2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hh := hB j (Finset.mem_range.mp hj)
    linarith
  have he : (∑ j ∈ Finset.range E, (2*(Fintype.card X : ℚ)*r^(j+2))) =
      2*(Fintype.card X : ℚ)*r*geometricMass r E := by
    unfold geometricMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show j+2 = (j+1)+1 by omega, pow_succ]
    ring
  rw [he] at hb
  have hhalf : geometricMass r E ≤ 1/2 := by
    have hh := geometricMass_le_half r hr hr3 E
    have hp := pow_nonneg hr E
    linarith
  have hn : (0 : ℚ) ≤ Fintype.card X := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hhalf
    (show 0 ≤ 2*(Fintype.card X : ℚ)*r by positivity)
  have hrN := mul_le_mul_of_nonneg_left hr3 hn
  nlinarith

/-- At least one third of the ambient space survives, uniformly in the number
of higher pure levels. For a base p≥3 take r=1/p. -/
theorem good_card_bound (σ : X → X) (Z : Finset X) (B : ℕ → Finset X)
    (E : ℕ) (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 1/3)
    (hZ : (Z.card : ℚ) ≤ Fintype.card X*r)
    (hB : ∀ j < E, ((B j).card : ℚ) ≤ Fintype.card X*r^(j+2)) :
    (Fintype.card X : ℚ)/3 ≤ (good σ Z B E).card := by
  have hb := bad_card_bound σ Z B E r hr hr3 hZ hB
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (bad σ Z B E))
  have hq : ((good σ Z B E).card : ℚ)+(bad σ Z B E).card = Fintype.card X := by
    exact_mod_cast hc
  linarith

lemma good_avoids (σ : X → X) (hσ : Function.Involutive σ)
    (Z : Finset X) (hZ : ∀ x, x ∈ Z → σ x ∈ Z)
    (B : ℕ → Finset X) (E : ℕ) (x : X) (hx : x ∈ good σ Z B E) :
    x ∉ Z ∧ σ x ∉ Z ∧ ∀ j < E, x ∉ B j ∧ σ x ∉ B j := by
  have hn := (Finset.mem_sdiff.mp hx).2
  have hxZ : x ∉ Z := fun h => hn (Finset.mem_union_left _ h)
  refine ⟨hxZ, ?_, ?_⟩
  · intro h
    exact hxZ (by simpa only [hσ x] using hZ (σ x) h)
  · intro j hj
    have hbad : ∀ y ∈ B j ∪ (B j).image σ, y ∈ bad σ Z B E := by
      intro y hy
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hy⟩)
    constructor
    · intro h
      exact hn (hbad x (Finset.mem_union_left _ h))
    · intro h
      apply hn
      apply hbad x
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨σ x, h, hσ x⟩

/-- Both members of an involution pair can avoid all the pure classes. -/
theorem exists_avoiding_pair [Nonempty X]
    (σ : X → X) (hσ : Function.Involutive σ)
    (Z : Finset X) (hZstable : ∀ x, x ∈ Z → σ x ∈ Z)
    (B : ℕ → Finset X) (E : ℕ) (r : ℚ) (hr : 0 ≤ r) (hr3 : r ≤ 1/3)
    (hZ : (Z.card : ℚ) ≤ Fintype.card X*r)
    (hB : ∀ j < E, ((B j).card : ℚ) ≤ Fintype.card X*r^(j+2)) :
    ∃ x : X, x ∉ Z ∧ σ x ∉ Z ∧ ∀ j < E, x ∉ B j ∧ σ x ∉ B j := by
  have hb := good_card_bound σ Z B E r hr hr3 hZ hB
  have hN : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hg : 0 < (good σ Z B E).card := by
    have hh : (0 : ℚ) < (good σ Z B E).card := by linarith
    exact_mod_cast hh
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hg
  exact ⟨x, good_avoids σ hσ Z hZstable B E x hx⟩

end Finite
#print axioms good_card_bound
#print axioms exists_avoiding_pair
end Erdos7SymmetricPureAvoidance
