import Submission.ArithmeticReduction

/-! A conditional odd-order orbit descent, with a finite collision-count
criterion. No universally small collision budget is proved here. -/
namespace Erdos7UnitOrbitDescent
open scoped BigOperators
open Erdos7Reduction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

variable {G I : Type} [Group G] [Fintype G] [Fintype I]
variable (H : I → Type) [∀ i, Group (H i)]
variable (π : (i : I) → G →* H i) (a : (i : I) → H i)

/-- A class is active when it meets the translated cyclic orbit. -/
def Active (u v : G) (i : I) : Prop := ∃ n : ℤ, π i (v*u^n) = a i

/-- If active induced periods are distinct and nontrivial, restricting a
coset cover to this orbit really produces a strict odd arithmetic cover. -/
theorem cover_of_clean_orbit (hc : ∀ x : G, ∃ i, π i x = a i)
    (u v : G) (hu : Odd (orderOf u))
    (hunit : ∀ i, Active H π a u v i → orderOf (π i u) ≠ 1)
    (hinj : ∀ i j, Active H π a u v i → Active H π a u v j →
      orderOf (π i u) = orderOf (π j u) → i = j) :
    HasOddArithmeticCover (orderOf u) (Fintype.card I) := by
  classical
  let J := {i : I // Active H π a u v i}
  let d (i : J) := orderOf (π i.val u)
  let b (i : J) : ℤ := Classical.choose i.property
  have hb (i : J) : π i.val (v*u^(b i)) = a i.val := Classical.choose_spec i.property
  have hd (i : J) : d i ∣ orderOf u := orderOf_map_dvd (π i.val) u
  refine ⟨orderOf_pos u, J, inferInstance, d, b, ?_, ?_, ?_, hd, ?_⟩
  · intro i j hij
    apply Subtype.ext
    exact hinj i.val j.val i.property j.property hij
  · intro i
    have hp : 0 < d i := Nat.pos_of_dvd_of_pos (hd i) (orderOf_pos u)
    have hn : d i ≠ 1 := hunit i.val i.property
    exact ⟨by omega, hu.of_dvd_nat (hd i)⟩
  · intro n
    obtain ⟨i, hi⟩ := hc (v*u^n)
    let j : J := ⟨i, n, hi⟩
    refine ⟨j, ?_⟩
    have he := (hb j).trans hi.symm
    simp only [map_mul, map_zpow] at he
    have hp : (π i u) ^ b j = (π i u) ^ n := mul_left_cancel he
    exact Int.modEq_iff_dvd.mp (zpow_eq_zpow_iff_modEq.mp hp)
  · exact Fintype.card_subtype_le _

/-- Minimality forces a unit or a repeated induced period on every translate.
The assertion is conditional on a smaller-period nonexistence hypothesis. -/
theorem every_orbit_bad (hc : ∀ x : G, ∃ i, π i x = a i)
    (u : G) (hu : Odd (orderOf u))
    (hno : ¬ HasOddArithmeticCover (orderOf u) (Fintype.card I)) (v : G) :
    (∃ i, Active H π a u v i ∧ orderOf (π i u) = 1) ∨
    (∃ i j, i ≠ j ∧ Active H π a u v i ∧ Active H π a u v j ∧
      orderOf (π i u) = orderOf (π j u)) := by
  by_contra! hn
  apply hno
  apply cover_of_clean_orbit H π a hc u v hu
  · intro i hi he
    exact hn.1 i hi he
  · intro i j hi hj he
    by_contra hij
    exact hn.2 i j hij hi hj he

/-- A second-order failure count can find a sample with no exceptional event
and at most one active label. This is a finite counting statement only. -/
lemma exists_sample_of_binomial_bound {Ω J : Type} [Fintype Ω] [Fintype J]
    (U : Ω → Prop) (P : Ω → J → Prop)
    (hbound : (∑ x : Ω, ((if U x then 1 else 0) +
      (((Finset.univ : Finset J).filter (P x)).card).choose 2)) < Fintype.card Ω) :
    ∃ x, ¬ U x ∧ ∀ i j, P x i → P x j → i = j := by
  classical
  by_contra hn
  have hpoint (x : Ω) : 1 ≤ (if U x then 1 else 0) +
      (((Finset.univ : Finset J).filter (P x)).card).choose 2 := by
    by_cases hu : U x
    · simp [hu]
    · have hbad : ¬ ∀ i j, P x i → P x j → i = j :=
        fun hh => hn ⟨x,hu,hh⟩
      push_neg at hbad
      obtain ⟨i,j,hi,hj,hij⟩ := hbad
      have hcard : 1 < (((Finset.univ : Finset J).filter (P x)).card) := by
        apply Finset.one_lt_card.mpr
        exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
          j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,hij⟩
      have hp := Nat.choose_pos (k := 2) (by omega : 2 ≤
        (((Finset.univ : Finset J).filter (P x)).card))
      simpa only [if_neg hu, zero_add] using hp
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => hpoint x)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  omega

/-- Necessary binomial collision budget. Counting all pairs of nonunit
active classes is a valid relaxation of counting only equal-period pairs. -/
theorem binomial_collision_count_bound (hc : ∀ x : G, ∃ i, π i x = a i)
    (u : G) (hu : Odd (orderOf u))
    (hno : ¬ HasOddArithmeticCover (orderOf u) (Fintype.card I)) :
    Fintype.card G ≤ ∑ v : G,
      ((if ∃ i, Active H π a u v i ∧ orderOf (π i u) = 1 then 1 else 0) +
      (((Finset.univ : Finset I).filter (fun i =>
        Active H π a u v i ∧ orderOf (π i u) ≠ 1)).card).choose 2) := by
  classical
  by_contra h
  have hb := lt_of_not_ge h
  obtain ⟨v,hv,hi⟩ := exists_sample_of_binomial_bound
    (fun v => ∃ i, Active H π a u v i ∧ orderOf (π i u) = 1)
    (fun v i => Active H π a u v i ∧ orderOf (π i u) ≠ 1) (by
      convert hb using 1
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      · by_cases hh : ∃ i, Active H π a u v i ∧ orderOf (π i u) = 1 <;> simp [hh]
      · congr 1
        congr 1
        ext i
        simp)
  have hunit (i : I) (hactive : Active H π a u v i) : orderOf (π i u) ≠ 1 :=
    fun he => hv ⟨i,hactive,he⟩
  apply hno
  apply cover_of_clean_orbit H π a hc u v hu hunit
  intro i j hai haj _
  exact hi i j ⟨hai,hunit i hai⟩ ⟨haj,hunit j haj⟩


section Counting
variable [LinearOrder I]

abbrev PairIndex := {ij : I × I // ij.1 < ij.2}

/-- Integer union-bound form. Unlike the first moment of the number of active
classes, it counts the actual failure conditions for a clean orbit. -/
theorem collision_count_bound (hc : ∀ x : G, ∃ i, π i x = a i)
    (u : G) (hu : Odd (orderOf u))
    (hno : ¬ HasOddArithmeticCover (orderOf u) (Fintype.card I)) :
    Fintype.card G ≤
      (∑ i : I, ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v i ∧ orderOf (π i u) = 1)).card) +
      (∑ ij : PairIndex (I := I), ((Finset.univ : Finset G).filter (fun v =>
        Active H π a u v ij.val.1 ∧ Active H π a u v ij.val.2 ∧
        orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u))).card) := by
  classical
  let U (i : I) : Finset G := Finset.univ.filter (fun v =>
    Active H π a u v i ∧ orderOf (π i u) = 1)
  let P (ij : PairIndex (I := I)) : Finset G := Finset.univ.filter (fun v =>
    Active H π a u v ij.val.1 ∧ Active H π a u v ij.val.2 ∧
    orderOf (π ij.val.1 u) = orderOf (π ij.val.2 u))
  have hcover : (Finset.univ : Finset G) ⊆
      Finset.univ.biUnion U ∪ Finset.univ.biUnion P := by
    intro v _
    rcases every_orbit_bad H π a hc u hu hno v with ⟨i, hi⟩ | ⟨i,j,hij,hi,hj,he⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
    · apply Finset.mem_union_right
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Finset.mem_biUnion.mpr ⟨⟨(i,j),hij⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj,he⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨⟨(j,i),hji⟩, Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,hi,he.symm⟩⟩
  calc
    Fintype.card G = (Finset.univ : Finset G).card := Finset.card_univ.symm
    _ ≤ (Finset.univ.biUnion U ∪ Finset.univ.biUnion P).card := Finset.card_le_card hcover
    _ ≤ (Finset.univ.biUnion U).card + (Finset.univ.biUnion P).card := Finset.card_union_le _ _
    _ ≤ (∑ i, (U i).card) + ∑ ij, (P ij).card :=
      add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = _ := by
      simp only [U, P]
      congr 1 <;> congr 1
      all_goals ext v <;> simp

end Counting
#print axioms cover_of_clean_orbit
#print axioms every_orbit_bad
#print axioms collision_count_bound
#print axioms exists_sample_of_binomial_bound
#print axioms binomial_collision_count_bound
end
end Erdos7UnitOrbitDescent
