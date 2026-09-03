import FormalConjecturesUtil

/-!
# Collision energy of the inverse graph over a finite field

An elementary finite-field estimate for later use with additive-character
orthogonality. No assertion about primes or totient multiplicity is made here.
-/
open Finset
open scoped Classical BigOperators
namespace Erdos821.Kloosterman

variable {F : Type*} [Field F]

lemma pair_eq_or_swap_of_sum_invSum {x y z w : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hs : x + y = z + w) (hi : x⁻¹ + y⁻¹ = z⁻¹ + w⁻¹)
    (hs0 : x + y ≠ 0) :
    (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  have hip : (x+y)*(z*w) = (z+w)*(x*y) := by
    field_simp at hi
    linear_combination hi
  have hp : z*w = x*y := by
    apply mul_left_cancel₀ hs0
    simpa only [← hs] using hip
  have hroot : (z-x)*(z-y) = 0 := by
    linear_combination -z*hs - hp
  rcases mul_eq_zero.mp hroot with h | h
  · left
    have hz' := sub_eq_zero.mp h
    exact ⟨hz', by linear_combination -hs - hz'⟩
  · right
    have hz' := sub_eq_zero.mp h
    exact ⟨hz', by linear_combination -hs - hz'⟩

abbrev UnitPair (F : Type*) [Field F] := Fˣ × Fˣ

def pairSum (u : UnitPair F) : F := (u.1 : F) + (u.2 : F)

def pairInvSum (u : UnitPair F) : F := (u.1 : F)⁻¹ + (u.2 : F)⁻¹

def Collides (u v : UnitPair F) : Prop :=
  pairSum u = pairSum v ∧ pairInvSum u = pairInvSum v

lemma collides_eq_or_swap {u v : UnitPair F} (hc : Collides u v)
    (hu : pairSum u ≠ 0) : v = u ∨ v = u.swap := by
  obtain h | h := pair_eq_or_swap_of_sum_invSum u.1.ne_zero u.2.ne_zero
    v.1.ne_zero v.2.ne_zero hc.1 hc.2 hu
  · exact Or.inl (Prod.ext (Units.ext h.1) (Units.ext h.2))
  · exact Or.inr (Prod.ext (Units.ext h.1) (Units.ext h.2))

variable [Fintype F]

noncomputable def collisionFiber (u : UnitPair F) : Finset (UnitPair F) :=
  univ.filter (Collides u)

noncomputable def collisionEnergy : ℕ :=
  ∑ u : UnitPair F, (collisionFiber u).card

lemma collisionFiber_card_le_two {u : UnitPair F} (hu : pairSum u ≠ 0) :
    (collisionFiber u).card ≤ 2 := by
  have hs : collisionFiber u ⊆ {u, u.swap} := by
    intro v hv
    simpa only [mem_insert, mem_singleton] using
      collides_eq_or_swap (mem_filter.mp hv).2 hu
  exact (card_le_card hs).trans (by simpa using card_insert_le u {u.swap})

lemma collisionFiber_card_le_units (u : UnitPair F) :
    (collisionFiber u).card ≤ Fintype.card Fˣ := by
  apply card_le_card_of_injOn (fun v : UnitPair F => v.1)
    (t := (univ : Finset Fˣ)) (by intro v hv; exact mem_univ _)
  intro v hv w hw he
  have hv' := (mem_filter.mp hv).2.1
  have hw' := (mem_filter.mp hw).2.1
  apply Prod.ext he
  apply Units.ext
  have he' : (v.1 : F) = (w.1 : F) := congrArg Units.val he
  dsimp [pairSum] at hv' hw'
  linear_combination hw' - hv' - he'

lemma zero_pairSum_card_le_units :
    (univ.filter (fun u : UnitPair F => pairSum u = 0)).card ≤
      Fintype.card Fˣ := by
  apply card_le_card_of_injOn (fun v : UnitPair F => v.1)
    (t := (univ : Finset Fˣ)) (by intro v hv; exact mem_univ _)
  intro v hv w hw he
  apply Prod.ext he
  apply Units.ext
  have hv' := (mem_filter.mp hv).2
  have hw' := (mem_filter.mp hw).2
  have he' : (v.1 : F) = (w.1 : F) := congrArg Units.val he
  dsimp [pairSum] at hv' hw'
  linear_combination hv' - hw' - he'

/-- The inverse graph has at most three times the square of its cardinality
many ordered additive collisions. This works in characteristic two as well. -/
theorem collisionEnergy_le :
    collisionEnergy (F := F) ≤ 3 * (Fintype.card Fˣ)^2 := by
  let Z := univ.filter (fun u : UnitPair F => pairSum u = 0)
  have hsplit := sum_filter_add_sum_filter_not (s := (univ : Finset (UnitPair F)))
    (p := fun u => pairSum u = 0) (f := fun u => (collisionFiber u).card)
  have hzero : (∑ u ∈ Z, (collisionFiber u).card) ≤ (Fintype.card Fˣ)^2 := by
    calc
      _ ≤ ∑ _u ∈ Z, Fintype.card Fˣ := sum_le_sum fun u _ => collisionFiber_card_le_units u
      _ = Z.card * Fintype.card Fˣ := by simp
      _ ≤ Fintype.card Fˣ * Fintype.card Fˣ := Nat.mul_le_mul_right _ zero_pairSum_card_le_units
      _ = _ := by ring
  have hnonzero :
      (∑ u ∈ univ.filter (fun u : UnitPair F => ¬ pairSum u = 0),
        (collisionFiber u).card) ≤ 2 * (Fintype.card Fˣ)^2 := by
    calc
      _ ≤ ∑ _u ∈ univ.filter (fun u : UnitPair F => ¬ pairSum u = 0), 2 :=
        sum_le_sum fun u hu => collisionFiber_card_le_two (mem_filter.mp hu).2
      _ ≤ ∑ _u : UnitPair F, 2 := sum_le_sum_of_subset_of_nonneg
        (filter_subset _ _) (by intros; omega)
      _ = _ := by simp [UnitPair, Fintype.card_prod]; ring
  dsimp [collisionEnergy]
  change (∑ u ∈ Z, (collisionFiber u).card) + _ = _ at hsplit
  omega

end Erdos821.Kloosterman
