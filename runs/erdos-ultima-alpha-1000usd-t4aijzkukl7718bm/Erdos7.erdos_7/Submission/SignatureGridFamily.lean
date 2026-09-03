import Submission.SignatureGridPatterns

/-! A divisor-closed partial prime-power family with separated grid boxes.
This construction is for testing signature charges, not for covering integers. -/
namespace Erdos7SignatureGridFamily
open scoped BigOperators
open Finset Erdos7SignatureGridPatterns
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

abbrev value : Coord → Fin 14 → ℤ :=
  ![![1,4,7,10,13,16,19,5,14,17,23,32,41,44],
    ![2,7,12,17,22,27,32,3,8,13,18,23,28,33],
    ![3,10,17,24,31,38,45,4,11,18,25,32,39,46]]

def gridPoint (g : Grid) : Coord → ℤ := fun i => value i (g i)

lemma value_properties : ∀ i : Coord,
    Function.Injective (value i) ∧
    (∀ j, 0 ≤ value i j ∧ value i j < (prime i : ℤ) ^ depth i) ∧
    (∀ j, ¬ (prime i : ℤ) ^ depth i ∣ value i j + 1) := by
  decide +kernel

lemma prime_positive (i : Coord) : 0 < prime i := (prime_properties.2 i).1.pos
lemma prime_three_le (i : Coord) : 3 ≤ prime i := (prime_properties.2 i).2.2

lemma value_congruent_injective (i : Coord) (j k : Fin 14)
    (h : (prime i : ℤ) ^ depth i ∣ value i j - value i k) : j = k := by
  apply (value_properties i).1
  exact Erdos7PrimePowerCombFamily.bounded_congruent_eq ((value_properties i).2.1 j).1
    ((value_properties i).2.1 k).1 ((value_properties i).2.1 j).2
    ((value_properties i).2.1 k).2 h

lemma pure_small_check : ∀ i : Coord, ∀ j : Fin 14, ∀ e ∈ range (depth i + 1),
    0 < e → ¬ (prime i : ℤ) ^ e ∣ value i j - Erdos7PrimePowerCombFamily.exitValue (prime i) e 1 := by
  decide +kernel

lemma value_avoids_pure (i : Coord) (j : Fin 14) (e : ℕ) (he : 0 < e) :
    ¬ (prime i : ℤ) ^ e ∣ value i j - Erdos7PrimePowerCombFamily.exitValue (prime i) e 1 := by
  by_cases hb : e ≤ depth i
  · exact pure_small_check i j e (mem_range.mpr (by omega)) he
  · intro h
    have hd := (pow_dvd_pow (prime i : ℤ) (by omega : depth i ≤ e)).trans h
    have hs := Erdos7PrimePowerCombFamily.higher_exit_stem (p := prime i) (c := 1) (by omega : depth i < e)
    have hbad : (prime i : ℤ) ^ depth i ∣ value i j + 1 := by
      convert dvd_add hd hs using 1 <;> ring
    exact (value_properties i).2.2 j hbad

lemma first_digit_checks :
    (∀ j : Fin 14, ¬ (5 : ℤ) ∣ value 1 j + 1) ∧
    (∀ j : Fin 14, ¬ (7 : ℤ) ∣ value 2 j + 1) ∧
    (∀ j : Fin 14, ∀ c : Fin 4, 0 < c.val →
      ¬ (7 : ℤ) ∣ value 2 j - (c.val - 1 : ℤ)) ∧
    (∀ j : Fin 14, ∀ c : Fin 3, 0 < c.val →
      ¬ (5 : ℤ) ∣ value 1 j - (c.val - 1 : ℤ)) := by
  decide +kernel

lemma value_seven_avoids_color (j : Fin 14) (e c : ℕ) (he : 0 < e)
    (hc : 0 < c) (hc3 : c ≤ 3) :
    ¬ (7 : ℤ) ∣ value 2 j - Erdos7PrimePowerCombFamily.exitValue 7 e c := by
  by_cases he1 : e = 1
  · subst e
    simpa [Erdos7PrimePowerCombFamily.exitValue] using first_digit_checks.2.2.1 j ⟨c, by omega⟩ hc
  · intro h
    have hs := Erdos7PrimePowerCombFamily.higher_exit_stem (p := 7) (c := c) (by omega : 1 < e)
    simp only [pow_one] at hs
    have hh : (7 : ℤ) ∣ value 2 j + 1 := by
      convert dvd_add h hs using 1 <;> ring
    exact first_digit_checks.2.1 j hh

lemma value_five_avoids_color (j : Fin 14) (e c : ℕ) (he : 0 < e)
    (hc : 0 < c) (hc2 : c ≤ 2) :
    ¬ (5 : ℤ) ∣ value 1 j - Erdos7PrimePowerCombFamily.exitValue 5 e c := by
  by_cases he1 : e = 1
  · subst e
    simpa [Erdos7PrimePowerCombFamily.exitValue] using first_digit_checks.2.2.2 j ⟨c, by omega⟩ hc
  · intro h
    have hs := Erdos7PrimePowerCombFamily.higher_exit_stem (p := 5) (c := c) (by omega : 1 < e)
    simp only [pow_one] at hs
    have hh : (5 : ℤ) ∣ value 1 j + 1 := by
      convert dvd_add h hs using 1 <;> ring
    exact first_digit_checks.1 j hh

lemma support_nonempty (d : Pattern) : (Erdos7PrimePowerCombFamily.support (exponent d)).Nonempty := by
  obtain ⟨i, hi⟩ := exponent_nonzero d
  exact ⟨i, (Erdos7PrimePowerCombFamily.mem_support _ _).mpr hi⟩

lemma support_card_le_three (e : Coord → ℕ) : (Erdos7PrimePowerCombFamily.support e).card ≤ 3 := by
  exact (card_le_univ _).trans (by decide : Fintype.card Coord ≤ 3)

/-- Grid boxes are disjoint from all the comb completion boxes. -/
theorem grid_misses_comb (g : Grid) (d : Pattern) :
    ¬ ∀ i ∈ Erdos7PrimePowerCombFamily.support (exponent d), (prime i : ℤ) ^ exponent d i ∣
      gridPoint g i - Erdos7PrimePowerCombFamily.exitValue (prime i) (exponent d i) (Erdos7PrimePowerCombFamily.color prime (exponent d) i) := by
  intro h
  by_cases h7 : exponent d 2 ≠ 0
  · have hi := (Erdos7PrimePowerCombFamily.mem_support _ _).mpr h7
    have hc := Erdos7PrimePowerCombFamily.color_bounds prime (exponent d) prime_three_le 2 hi
    have hcard := support_card_le_three (exponent d)
    have hcol : Erdos7PrimePowerCombFamily.color prime (exponent d) 2 ≤ 3 := (min_le_left _ _).trans hcard
    have hd := (pow_dvd_pow (prime 2 : ℤ) (Nat.pos_of_ne_zero h7)).trans (h 2 hi)
    exact value_seven_avoids_color (g 2) _ _ (Nat.pos_of_ne_zero h7) hc.1 hcol
      (by simpa only [pow_one, prime, Matrix.cons_val_two, gridPoint] using hd)
  · have h7z : exponent d 2 = 0 := by omega
    by_cases h5 : exponent d 1 ≠ 0
    · have hi := (Erdos7PrimePowerCombFamily.mem_support _ _).mpr h5
      have hc := Erdos7PrimePowerCombFamily.color_bounds prime (exponent d) prime_three_le 1 hi
      have hsub : Erdos7PrimePowerCombFamily.support (exponent d) ⊆ ({0, 1} : Finset Coord) := by
        intro i hi
        fin_cases i <;> simp_all [Erdos7PrimePowerCombFamily.mem_support]
      have hcard : (Erdos7PrimePowerCombFamily.support (exponent d)).card ≤ 2 :=
        (card_le_card hsub).trans_eq (by decide)
      have hcol : Erdos7PrimePowerCombFamily.color prime (exponent d) 1 ≤ 2 := (min_le_left _ _).trans hcard
      have hd := (pow_dvd_pow (prime 1 : ℤ) (Nat.pos_of_ne_zero h5)).trans (h 1 hi)
      exact value_five_avoids_color (g 1) _ _ (Nat.pos_of_ne_zero h5) hc.1 hcol
        (by simpa only [pow_one, prime, Matrix.cons_val_one, gridPoint] using hd)
    · have h5z : exponent d 1 = 0 := by omega
      have h0 : exponent d 0 ≠ 0 := by
        obtain ⟨i, hi⟩ := exponent_nonzero d
        fin_cases i <;> simp_all
      have hS : Erdos7PrimePowerCombFamily.support (exponent d) = {0} := by
        ext i
        fin_cases i <;> simp [Erdos7PrimePowerCombFamily.mem_support, h0, h5z, h7z]
      have hc : Erdos7PrimePowerCombFamily.color prime (exponent d) 0 = 1 := by simp [Erdos7PrimePowerCombFamily.color, hS, prime]
      have hh := h 0 ((Erdos7PrimePowerCombFamily.mem_support _ _).mpr h0)
      rw [hc] at hh
      exact value_avoids_pure 0 (g 0) _ (Nat.pos_of_ne_zero h0) hh

/-- A comb private point misses every grid box already at the first7 digit. -/
theorem comb_point_misses_grid (d : Pattern) (g : Grid) :
    ¬ (7 : ℤ) ∣ Erdos7PrimePowerCombFamily.point prime (exponent d) 2 - gridPoint g 2 := by
  by_cases he : exponent d 2 = 0
  · simp only [Erdos7PrimePowerCombFamily.point, if_pos he, gridPoint]
    intro h
    apply first_digit_checks.2.1 (g 2)
    convert dvd_neg.mpr h using 1 <;> ring
  · have hi := (Erdos7PrimePowerCombFamily.mem_support _ _).mpr he
    have hc := Erdos7PrimePowerCombFamily.color_bounds prime (exponent d) prime_three_le 2 hi
    have hcol : Erdos7PrimePowerCombFamily.color prime (exponent d) 2 ≤ 3 :=
      (min_le_left _ _).trans (support_card_le_three _)
    simp only [Erdos7PrimePowerCombFamily.point, if_neg he, gridPoint, prime, Matrix.cons_val_two]
    intro h
    apply value_seven_avoids_color (g 2) _ _ (Nat.pos_of_ne_zero he) hc.1 hcol
    simpa only [neg_sub] using dvd_neg.mpr h

/-- Replace only the selected maximal comb patterns. -/
noncomputable def residue (d : Pattern) : Coord → ℤ :=
  if h : ∃ g, gridPattern g = d then gridPoint h.choose
  else Erdos7PrimePowerCombFamily.point prime (exponent d)

lemma residue_grid (g : Grid) : residue (gridPattern g) = gridPoint g := by
  classical
  have h : ∃ t, gridPattern t = gridPattern g := ⟨g, rfl⟩
  simp only [residue, dif_pos h]
  rw [gridPattern_injective h.choose_spec]

lemma residue_comb (d : Pattern) (h : ¬ ∃ g, gridPattern g = d) :
    residue d = Erdos7PrimePowerCombFamily.point prime (exponent d) := by
  classical
  simp only [residue, dif_neg h]

/-- Membership in the local box of a pattern. Zero exponents impose no constraint. -/
def Hits (x : Coord → ℤ) (d : Pattern) : Prop :=
  ∀ i, (prime i : ℤ) ^ exponent d i ∣ x i - residue d i

lemma hits_grid_iff (g h : Grid) : Hits (gridPoint g) (gridPattern h) ↔ g = h := by
  rw [Hits, residue_grid]
  constructor
  · intro hm
    funext i
    exact value_congruent_injective i (g i) (h i)
      ((pow_dvd_pow (prime i : ℤ) ((gridPattern_bounds h).1 i)).trans (hm i))
  · rintro rfl
    simp

lemma grid_not_comb (g : Grid) (d : Pattern) (hd : ¬ ∃ h, gridPattern h = d) :
    ¬ Hits (gridPoint g) d := by
  intro h
  apply grid_misses_comb g d
  intro i hi
  have hh := h i
  rw [residue_comb d hd] at hh
  simpa only [Erdos7PrimePowerCombFamily.point,
    if_neg ((Erdos7PrimePowerCombFamily.mem_support _ _).mp hi)] using hh

lemma grid_hits_iff (g : Grid) (d : Pattern) :
    Hits (gridPoint g) d ↔ d = gridPattern g := by
  classical
  by_cases hd : ∃ h, gridPattern h = d
  · obtain ⟨h, rfl⟩ := hd
    rw [hits_grid_iff]
    exact ⟨fun hh => by rw [hh], fun hh => (gridPattern_injective hh).symm⟩
  · exact iff_of_false (grid_not_comb g d hd) (fun h => hd ⟨g, h.symm⟩)

/-- All modified classes retain private points. -/
theorem private_residue (d k : Pattern) : Hits (residue d) k ↔ k = d := by
  classical
  by_cases hd : ∃ g, gridPattern g = d
  · obtain ⟨g, rfl⟩ := hd
    rw [residue_grid, grid_hits_iff]
  · rw [residue_comb d hd]
    by_cases hk : ∃ g, gridPattern g = k
    · obtain ⟨g, rfl⟩ := hk
      apply iff_of_false
      · intro hh
        apply comb_point_misses_grid d g
        have hb := (gridPattern_bounds g).1 2
        have hp : 1 ≤ exponent (gridPattern g) 2 := by
          have : depth 2 = 2 := rfl
          omega
        have hh := (pow_dvd_pow (prime 2 : ℤ) hp).trans (hh 2)
        simpa only [residue_grid, prime, Matrix.cons_val_two, pow_one] using hh
      · exact fun h => hd ⟨g, h⟩
    · constructor
      · intro hh
        apply Eq.symm
        apply exponent_injective
        apply (Erdos7PrimePowerCombFamily.private_pattern prime prime_three_le
          prime_properties.1 (exponent d) (exponent k) (support_nonempty k)).mp
        intro i hi
        have hm := hh i
        rw [residue_comb k hk] at hm
        simpa only [Erdos7PrimePowerCombFamily.point,
          if_neg ((Erdos7PrimePowerCombFamily.mem_support _ _).mp hi)] using hm
      · intro h
        subst k
        intro i
        rw [residue_comb d hd]
        simp

/-- The construction remains a partial family: the all-stem point is uncovered. -/
theorem stem_not_hit (d : Pattern) : ¬ Hits (fun _ => -1) d := by
  classical
  by_cases hd : ∃ g, gridPattern g = d
  · obtain ⟨g, rfl⟩ := hd
    intro hh
    have hb := (gridPattern_bounds g).1 2
    have hp : 1 ≤ exponent (gridPattern g) 2 := by
      have : depth 2 = 2 := rfl
      omega
    have hm := (pow_dvd_pow (prime 2 : ℤ) hp).trans (hh 2)
    rw [residue_grid] at hm
    change (7 : ℤ) ∣ -1 - value 2 (g 2) at hm
    apply first_digit_checks.2.1 (g 2)
    convert dvd_neg.mpr hm using 1 <;> ring
  · intro hh
    apply Erdos7PrimePowerCombFamily.stem_uncovered prime prime_three_le
      (exponent d) (support_nonempty d)
    intro i hi
    have hm := hh i
    rw [residue_comb d hd] at hm
    simpa only [Erdos7PrimePowerCombFamily.point,
      if_neg ((Erdos7PrimePowerCombFamily.mem_support _ _).mp hi)] using hm

#print axioms private_residue
#print axioms stem_not_hit
#print axioms value_avoids_pure
#print axioms grid_misses_comb
#print axioms comb_point_misses_grid
end Erdos7SignatureGridFamily
