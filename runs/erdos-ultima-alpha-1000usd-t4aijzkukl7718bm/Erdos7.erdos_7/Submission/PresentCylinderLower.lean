import FormalConjecturesUtil

/-! Conditioning away a complete family of disjoint pure prime-power classes
does not shrink a cylinder which avoids all pure classes at lower levels.
This is a finite uniform-measure statement. It does not apply to absent
patterns or to arbitrary nonuniform optimizing measures. -/
namespace Erdos7PresentCylinderLower
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def geometricMass (r : ℚ) (E : ℕ) : ℚ := ∑ j ∈ Finset.range E, r^(j+1)

lemma geometricMass_nonneg (r : ℚ) (hr : 0 ≤ r) (E : ℕ) :
    0 ≤ geometricMass r E := Finset.sum_nonneg (fun _ _ => pow_nonneg hr _)

lemma geometricMass_mono (r : ℚ) (hr : 0 ≤ r) : Monotone (geometricMass r) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro j _ _
  positivity

lemma tail_le_scaled_total (r : ℚ) (hr : 0 ≤ r) (a E : ℕ) :
    (∑ j ∈ Finset.Ico a E, r^(j+1)) ≤ r^a * geometricMass r E := by
  rw [Finset.sum_Ico_eq_sum_range]
  have he : (∑ j ∈ Finset.range (E-a), r^(a+j+1)) = r^a*geometricMass r (E-a) := by
    simp only [geometricMass, Finset.mul_sum, ← pow_add, Nat.add_assoc]
  rw [he]
  exact mul_le_mul_of_nonneg_left (geometricMass_mono r hr (Nat.sub_le E a)) (pow_nonneg hr _)

lemma geometricMass_lt_one (r : ℚ) (hr : 0 < r) (hhalf : r ≤ 1/2) (E : ℕ) :
    geometricMass r E < 1 := by
  have hbound : ∀ n, geometricMass r n ≤ 1-r^n := by
    intro n
    induction n with
    | zero => simp [geometricMass]
    | succ n ih =>
      have he : geometricMass r (n+1) = geometricMass r n + r^(n+1) := by
        simp [geometricMass, Finset.sum_range_succ]
      rw [he, pow_succ]
      have hn := pow_nonneg hr.le n
      nlinarith
  exact (hbound E).trans_lt (by have := pow_pos hr E; linarith)

section Finite
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The exact size of a disjoint complete pure family. -/
lemma pure_union_card (r : ℚ) (E : ℕ) (B : ℕ → Finset X)
    (hd : (↑(Finset.range E) : Set ℕ).PairwiseDisjoint B)
    (hsize : ∀ j < E, ((B j).card : ℚ) = Fintype.card X * r^(j+1)) :
    (((Finset.range E).biUnion B).card : ℚ) =
      Fintype.card X * geometricMass r E := by
  rw [Finset.card_biUnion hd, Nat.cast_sum, geometricMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact hsize j (Finset.mem_range.mp hj)

/-- Only higher pure classes can remove points of an allowable cylinder. -/
lemma cylinder_intersection_bound (r : ℚ) (hr : 0 ≤ r) (a E : ℕ)
    (B : ℕ → Finset X) (C : Finset X)
    (hsize : ∀ j < E, ((B j).card : ℚ) = Fintype.card X * r^(j+1))
    (havoid : ∀ j < E, j < a → Disjoint C (B j)) :
    ((C ∩ (Finset.range E).biUnion B).card : ℚ) ≤
      Fintype.card X * (r^a * geometricMass r E) := by
  have hs : C ∩ (Finset.range E).biUnion B ⊆ (Finset.Ico a E).biUnion B := by
    intro x hx
    obtain ⟨hc,hb⟩ := Finset.mem_inter.mp hx
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp hb
    have hjE := Finset.mem_range.mp hj
    have haj : a ≤ j := by
      by_contra hn
      have hd := havoid j hjE (by omega)
      exact Finset.disjoint_left.mp hd hc hxj
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_Ico.mpr ⟨haj,hjE⟩,hxj⟩
  have hcard := (Finset.card_le_card hs).trans Finset.card_biUnion_le
  have hq : ((C ∩ (Finset.range E).biUnion B).card : ℚ) ≤
      ∑ j ∈ Finset.Ico a E, ((B j).card : ℚ) := by exact_mod_cast hcard
  have he : (∑ j ∈ Finset.Ico a E, ((B j).card : ℚ)) =
      Fintype.card X * (∑ j ∈ Finset.Ico a E, r^(j+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hsize j (Finset.mem_Ico.mp hj).2
  rw [he] at hq
  exact hq.trans (mul_le_mul_of_nonneg_left (tail_le_scaled_total r hr a E) (Nat.cast_nonneg _))

/-- Uniform conditioning on the pure-class complement cannot lower the mass
of a cylinder whose lower pure levels are disjoint from it. The denominator
is positive by hypothesis; a separate theorem supplies this for r<=1/2. -/
theorem conditioned_cylinder_lower (r : ℚ) (hr : 0 ≤ r) (a E : ℕ)
    (B : ℕ → Finset X) (C : Finset X)
    (hd : (↑(Finset.range E) : Set ℕ).PairwiseDisjoint B)
    (hsize : ∀ j < E, ((B j).card : ℚ) = Fintype.card X * r^(j+1))
    (hC : (C.card : ℚ) = Fintype.card X * r^a)
    (havoid : ∀ j < E, j < a → Disjoint C (B j))
    (hpos : 0 < (Finset.univ \ (Finset.range E).biUnion B).card) :
    r^a ≤ (((Finset.univ \ (Finset.range E).biUnion B) ∩ C).card : ℚ) /
      (Finset.univ \ (Finset.range E).biUnion B).card := by
  let F := (Finset.range E).biUnion B
  let U : Finset X := Finset.univ \ F
  have hF : (F.card : ℚ) = Fintype.card X * geometricMass r E :=
    pure_union_card r E B hd hsize
  have hU : (U.card : ℚ) = Fintype.card X - Fintype.card X * geometricMass r E := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
    have hq : (U.card : ℚ) + F.card = Fintype.card X := by exact_mod_cast h
    linarith
  have hsplit : ((C \ F).card : ℚ) + (C ∩ F).card = C.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter C F
  have hbound := cylinder_intersection_bound r hr a E B C hsize havoid
  change ((C ∩ F).card : ℚ) ≤ _ at hbound
  have he : U ∩ C = C \ F := by
    ext x
    simp [U, and_comm]
  change r^a ≤ ((U ∩ C).card : ℚ) / U.card
  apply (le_div_iff₀ (show (0 : ℚ) < U.card by exact_mod_cast hpos)).mpr
  rw [he]
  calc
    r^a * U.card = Fintype.card X * r^a -
        Fintype.card X * (r^a * geometricMass r E) := by rw [hU]; ring
    _ ≤ C.card - (C ∩ F).card := by rw [hC]; linarith
    _ = ((C \ F).card : ℚ) := by linarith

/-- For reciprocal bases at most1/2, the pure complement is always nonempty. -/
theorem pure_complement_nonempty [Nonempty X]
    (r : ℚ) (hr : 0 < r) (hhalf : r ≤ 1/2) (E : ℕ) (B : ℕ → Finset X)
    (hd : (↑(Finset.range E) : Set ℕ).PairwiseDisjoint B)
    (hsize : ∀ j < E, ((B j).card : ℚ) = Fintype.card X * r^(j+1)) :
    0 < (Finset.univ \ (Finset.range E).biUnion B).card := by
  let F := (Finset.range E).biUnion B
  have hF := pure_union_card r E B hd hsize
  have hN : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hS := geometricMass_lt_one r hr hhalf E
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
  have hq : ((Finset.univ \ F).card : ℚ) + F.card = Fintype.card X := by exact_mod_cast hcard
  have hh : (0 : ℚ) < (Finset.univ \ F).card := by
    change (F.card : ℚ) = _ at hF
    nlinarith
  exact_mod_cast hh

end Finite
#print axioms conditioned_cylinder_lower
#print axioms pure_complement_nonempty
end Erdos7PresentCylinderLower
