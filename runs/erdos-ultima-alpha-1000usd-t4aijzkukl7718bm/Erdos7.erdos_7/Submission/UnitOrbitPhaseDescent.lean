import Submission.UnitOrbitDescent

/-! Merge identical induced congruence classes before testing distinctness.
Only repeated periods with different phases obstruct the conditional descent.
This does not prove that an unobstructed orbit always exists. -/
namespace Erdos7UnitOrbitPhaseDescent
open Erdos7Reduction Erdos7UnitOrbitDescent
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {G I : Type} [Group G] [Fintype G] [Fintype I]
variable (H : I → Type) [∀ i, Group (H i)]
variable (π : (i : I) → G →* H i) (a : (i : I) → H i)

/-- Both classes are met at the same parameter of the orbit. -/
def CoActive (u v : G) (i j : I) : Prop :=
  ∃ n : ℤ, π i (v*u^n) = a i ∧ π j (v*u^n) = a j

lemma coActive_symm (u v : G) (i j : I) :
    CoActive H π a u v i j ↔ CoActive H π a u v j i := by
  simp only [CoActive, and_comm]

lemma hit_difference (u v : G) (i : I) {s t : ℤ}
    (hs : π i (v*u^s) = a i) (ht : π i (v*u^t) = a i) :
    (orderOf (π i u) : ℤ) ∣ t-s := by
  have hh := hs.trans ht.symm
  simp only [map_mul, map_zpow] at hh
  exact Int.modEq_iff_dvd.mp (zpow_eq_zpow_iff_modEq.mp (mul_left_cancel hh))

/-- If each active period has a single phase, merge all copies of that phase.
The resulting smaller odd covering system is strict. -/
theorem cover_of_phase_clean_orbit (hc : ∀ x : G, ∃ i, π i x = a i)
    (u v : G) (hu : Odd (orderOf u))
    (hunit : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1)
    (hphase : ∀ i j, Active H π a u v i → Active H π a u v j →
      orderOf (π i u) = orderOf (π j u) → CoActive H π a u v i j) :
    HasOddArithmeticCover (orderOf u) (Fintype.card I) := by
  let A : Finset I := Finset.univ.filter (Active H π a u v)
  let D : Finset ℕ := A.image (fun i => orderOf (π i u))
  have hrep (d : D) : ∃ i : I, Active H π a u v i ∧ orderOf (π i u) = d.val := by
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp d.property
    exact ⟨i, (Finset.mem_filter.mp hi).2, he⟩
  let r (d : D) : I := Classical.choose (hrep d)
  have hr (d : D) : Active H π a u v (r d) ∧ orderOf (π (r d) u) = d.val :=
    Classical.choose_spec (hrep d)
  let b (d : D) : ℤ := Classical.choose (hr d).1
  have hb (d : D) : π (r d) (v*u^(b d)) = a (r d) := Classical.choose_spec (hr d).1
  have hd (d : D) : d.val ∣ orderOf u := (hr d).2 ▸ orderOf_map_dvd (π (r d)) u
  refine ⟨orderOf_pos u, D, inferInstance, Subtype.val, b,
    Subtype.val_injective, ?_, ?_, hd, ?_⟩
  · intro d
    have hp := Nat.pos_of_dvd_of_pos (hd d) (orderOf_pos u)
    have hn : d.val ≠ 1 := (hr d).2 ▸ hunit (r d) (hr d).1
    exact ⟨by omega, hu.of_dvd_nat (hd d)⟩
  · intro n
    obtain ⟨i,hi⟩ := hc (v*u^n)
    have hai : Active H π a u v i := ⟨n,hi⟩
    have hdi : orderOf (π i u) ∈ D := Finset.mem_image.mpr
      ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hai⟩,rfl⟩
    let d : D := ⟨orderOf (π i u), hdi⟩
    obtain ⟨t,hit,hjt⟩ := hphase i (r d) hai (hr d).1 (hr d).2.symm
    have hni : (d.val : ℤ) ∣ n-t := hit_difference H π a u v i hit hi
    have hbj : (d.val : ℤ) ∣ t-b d := by
      rw [← (hr d).2]
      exact hit_difference H π a u v (r d) (hb d) hjt
    refine ⟨d, ?_⟩
    convert dvd_add hni hbj using 1 <;> ring
  · calc
      Fintype.card D = D.card := Fintype.card_coe _
      _ ≤ A.card := Finset.card_image_le
      _ ≤ Fintype.card I := (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- In a minimal counterexample an orbit has a unit period, or two active
classes of the same nonunit period with genuinely different phases. -/
theorem every_orbit_phase_bad (hc : ∀ x : G, ∃ i, π i x = a i)
    (u : G) (hu : Odd (orderOf u))
    (hno : ¬ HasOddArithmeticCover (orderOf u) (Fintype.card I)) (v : G) :
    (∃ i, Active H π a u v i ∧ orderOf (π i u) = 1) ∨
    (∃ i j, i ≠ j ∧ Active H π a u v i ∧ Active H π a u v j ∧
      orderOf (π i u) = orderOf (π j u) ∧ orderOf (π i u) ≠ 1 ∧
      ¬ CoActive H π a u v i j) := by
  by_contra! hn
  apply hno
  apply cover_of_phase_clean_orbit H π a hc u v hu hn.1
  intro i j hi hj he
  by_cases hij : i = j
  · subst j
    obtain ⟨t,ht⟩ := hi
    exact ⟨t,ht,ht⟩
  · exact hn.2 i j hij hi hj he (hn.1 i hi)

section Counting
variable [LinearOrder I]

/-- The phase-sensitive union bound is no larger than the previous collision
count; same-phase duplicates and period-one pairs have been removed. -/
theorem phase_collision_count_bound (hc : ∀ x : G, ∃ i, π i x = a i)
    (u : G) (hu : Odd (orderOf u))
    (hno : ¬ HasOddArithmeticCover (orderOf u) (Fintype.card I)) :
    Fintype.card G ≤
      (∑ i : I, ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v i ∧ orderOf (π i u) = 1)).card) +
      (∑ ij : PairIndex (I := I), ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v ij.val.1 ∧ Active H π a u v ij.val.2 ∧
        orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u) ∧
        orderOf (π ij.val.1 u) ≠ 1 ∧
        ¬ CoActive H π a u v ij.val.1 ij.val.2)).card) := by
  let U (i : I) : Finset G := Finset.univ.filter (fun v =>
    Active H π a u v i ∧ orderOf (π i u) = 1)
  let P (ij : PairIndex (I := I)) : Finset G := Finset.univ.filter (fun v =>
    Active H π a u v ij.val.1 ∧ Active H π a u v ij.val.2 ∧
    orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u) ∧
    orderOf (π ij.val.1 u) ≠ 1 ∧
    ¬ CoActive H π a u v ij.val.1 ij.val.2)
  have hcover : (Finset.univ : Finset G) ⊆
      Finset.univ.biUnion U ∪ Finset.univ.biUnion P := by
    intro v _
    rcases every_orbit_phase_bad H π a hc u hu hno v with
      ⟨i, hi⟩ | ⟨i,j,hij,hi,hj,he,hne,hn⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
    · apply Finset.mem_union_right
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Finset.mem_biUnion.mpr ⟨⟨(i,j),hij⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj,he,hne,hn⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨⟨(j,i),hji⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,hi,he.symm,he ▸ hne,
            fun hh => hn ((coActive_symm H π a u v j i).mp hh)⟩⟩
  calc
    Fintype.card G = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ ≤ (Finset.univ.biUnion U ∪ Finset.univ.biUnion P).card := Finset.card_le_card hcover
    _ ≤ (Finset.univ.biUnion U).card + (Finset.univ.biUnion P).card := Finset.card_union_le _ _
    _ ≤ (∑ i, (U i).card) + ∑ ij, (P ij).card :=
      add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = _ := by
      simp only [U, P]

end Counting
#print axioms cover_of_phase_clean_orbit
#print axioms every_orbit_phase_bad
#print axioms phase_collision_count_bound
end
end Erdos7UnitOrbitPhaseDescent
