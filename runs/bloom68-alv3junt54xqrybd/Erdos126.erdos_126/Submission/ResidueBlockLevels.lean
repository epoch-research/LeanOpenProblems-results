import Submission.ResidueBlockGeometry

/-!
# Entrywise kernels at one residue level

At a fixed modulus there is at most one oriented residue pair containing a
specified vertex.  Thus an occupied cross entry counts exactly one pair,
and a diagonal entry counts at most one nonself same-class level.  The only
arithmetic input for the cross identity is opposition of prime colors on a
nonself opposite pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

variable {ι : Type*} [Fintype ι]

def Opposite (a : ι → ℕ) (p k r : ℕ) (i j : ι) : Prop :=
  (i ∈ leftClass a p k r ∧ j ∈ rightClass a p k r) ∨
    (i ∈ rightClass a p k r ∧ j ∈ leftClass a p k r)

def SameSide (a : ι → ℕ) (p k r : ℕ) (i j : ι) : Prop :=
  (i ∈ leftClass a p k r ∧ j ∈ leftClass a p k r) ∨
    (i ∈ rightClass a p k r ∧ j ∈ rightClass a p k r)

noncomputable def crossLevel (a : ι → ℕ) (p k : ℕ) (i j : ι) : ℝ := by
  classical
  exact ∑ r : Fin (p ^ k),
    if Active a p k r then (block a p k r).cross i j else 0

noncomputable def diagLevel (a : ι → ℕ) (p k : ℕ) (i j : ι) : ℝ := by
  classical
  exact ∑ r : Fin (p ^ k),
    if Active a p k r then (block a p k r).diag i j else 0

open Classical in
theorem block_cross_eq_ite (a : ι → ℕ) (p k r : ℕ) (i j : ι) :
    (block a p k r).cross i j = if Opposite a p k r i j then Real.log (p : ℝ) else 0 := by
  classical
  have hi := left_right_disjoint a p k r k r i
  have hj := left_right_disjoint a p k r k r j
  by_cases hil : i ∈ leftClass a p k r <;>
    by_cases hir : i ∈ rightClass a p k r <;>
    by_cases hjl : j ∈ leftClass a p k r <;>
    by_cases hjr : j ∈ rightClass a p k r <;>
    first
    | exact False.elim (hi hil hir)
    | exact False.elim (hj hjl hjr)
    | simp only [Paired.Block.cross, Paired.indicator, block_weight, block_left, block_right,
        Opposite, hil, hir, hjl, hjr, ite_true, ite_false, mul_zero,
        mul_one, add_zero, zero_add, and_false, and_true,
        false_or, or_false]

open Classical in
theorem block_diag_eq_ite (a : ι → ℕ) (p k r : ℕ) (i j : ι) :
    (block a p k r).diag i j = if SameSide a p k r i j then Real.log (p : ℝ) else 0 := by
  classical
  have hi := left_right_disjoint a p k r k r i
  have hj := left_right_disjoint a p k r k r j
  by_cases hil : i ∈ leftClass a p k r <;>
    by_cases hir : i ∈ rightClass a p k r <;>
    by_cases hjl : j ∈ leftClass a p k r <;>
    by_cases hjr : j ∈ rightClass a p k r <;>
    first
    | exact False.elim (hi hil hir)
    | exact False.elim (hj hjl hjr)
    | simp only [Paired.Block.diag, Paired.indicator, block_weight, block_left, block_right,
        SameSide, hil, hir, hjl, hjr, ite_true, ite_false, mul_zero,
        mul_one, add_zero, zero_add, and_false, and_true,
        false_or, or_false]

private theorem sum_ite_of_unique {τ : Type*} [Fintype τ]
    (P : τ → Prop) [DecidablePred P] [Decidable (∃ r, P r)]
    (w : ℝ) (hu : ∀ r s, P r → P s → r = s) :
    (∑ r, if P r then w else 0) = if ∃ r, P r then w else 0 := by
  classical
  by_cases h : ∃ r, P r
  · obtain ⟨r, hr⟩ := h
    rw [if_pos ⟨r, hr⟩]
    calc
      _ = if P r then w else 0 := by
        apply Finset.sum_eq_single r
        · intro s hs hsr
          rw [if_neg (fun hPs => hsr (hu s r hPs hr))]
        · simp
      _ = w := if_pos hr
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro r hr
    exact if_neg (fun hPr => h ⟨r, hPr⟩)

/-- Congruence is equivalent to divisibility of the natural distance. -/
theorem modEq_iff_dvd_dist (q x y : ℕ) :
    x ≡ y [MOD q] ↔ q ∣ Nat.dist x y := by
  rcases le_total x y with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.modEq_iff_dvd' h]
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.ModEq.comm, Nat.modEq_iff_dvd' h]

private theorem not_dvd_two_of_modEq {q x r : ℕ}
    (hm : x ≡ r [MOD q]) (hr : ¬q ∣ 2 * r) : ¬q ∣ 2 * x := by
  intro hx
  exact hr (Nat.modEq_zero_iff_dvd.1 ((hm.mul_left 2).symm.trans hx.modEq_zero_nat))

private theorem not_dvd_two_of_dvd_add {q x r : ℕ}
    (hm : q ∣ x + r) (hr : ¬q ∣ 2 * r) : ¬q ∣ 2 * x := by
  intro hx
  have hd : q ∣ 2 * x + 2 * r := by
    simpa only [mul_add] using dvd_mul_of_dvd_right hm 2
  exact hr ((Nat.dvd_add_iff_right hx).2 hd)

theorem nonself_opposite {q x y : ℕ}
    (hm : q ∣ x + y) (hx : ¬q ∣ 2 * x) : ¬q ∣ 2 * y := by
  intro hy
  have hd : q ∣ 2 * x + 2 * y := by
    simpa only [mul_add] using dvd_mul_of_dvd_right hm 2
  exact hx ((Nat.dvd_add_iff_left hy).2 hd)

private theorem residue_unique (a : ι → ℕ) (p k : ℕ) (i : ι)
    (r s : Fin (p ^ k))
    (hr : i ∈ leftClass a p k r ∨ i ∈ rightClass a p k r)
    (hs : i ∈ leftClass a p k s ∨ i ∈ rightClass a p k s) : r = s := by
  have hm : (r : ℕ) ≡ (s : ℕ) [MOD p ^ k] := by
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact ((mem_leftClass a p k r i).1 hr).1.symm.trans
        ((mem_leftClass a p k s i).1 hs).1
    · exact False.elim (left_right_disjoint a p k r k s i hr hs)
    · exact False.elim (left_right_disjoint a p k s k r i hs hr)
    · have hz := ((mem_rightClass a p k r i).1 hr).1.modEq_zero_nat
      have hz' := ((mem_rightClass a p k s i).1 hs).1.modEq_zero_nat
      exact (hz.trans hz'.symm).add_left_cancel' (a i)
  apply Fin.ext
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt s.isLt] using hm

private theorem opposite_support (a : ι → ℕ) (p k r : ℕ) (i j : ι)
    (h : Opposite a p k r i j) : i ∈ leftClass a p k r ∨ i ∈ rightClass a p k r :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

private theorem same_support (a : ι → ℕ) (p k r : ℕ) (i j : ι)
    (h : SameSide a p k r i j) : i ∈ leftClass a p k r ∨ i ∈ rightClass a p k r :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

open Classical in
theorem crossLevel_eq_ite_exists (a : ι → ℕ) (p k : ℕ) (i j : ι) :
    crossLevel a p k i j =
      if ∃ r : Fin (p ^ k), Active a p k r ∧ Opposite a p k r i j
      then Real.log (p : ℝ) else 0 := by
  classical
  unfold crossLevel
  calc
    _ = ∑ r : Fin (p ^ k),
        if Active a p k r ∧ Opposite a p k r i j then Real.log (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [block_cross_eq_ite]
      by_cases hA : Active a p k r <;> simp [hA]
    _ = _ := sum_ite_of_unique
      (fun r : Fin (p ^ k) => Active a p k r ∧ Opposite a p k r i j)
      (Real.log (p : ℝ)) (fun r s hr hs => residue_unique a p k i r s
      (opposite_support a p k r i j hr.2) (opposite_support a p k s i j hs.2))

open Classical in
theorem diagLevel_eq_ite_exists (a : ι → ℕ) (p k : ℕ) (i j : ι) :
    diagLevel a p k i j =
      if ∃ r : Fin (p ^ k), Active a p k r ∧ SameSide a p k r i j
      then Real.log (p : ℝ) else 0 := by
  classical
  unfold diagLevel
  calc
    _ = ∑ r : Fin (p ^ k),
        if Active a p k r ∧ SameSide a p k r i j then Real.log (p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [block_diag_eq_ite]
      by_cases hA : Active a p k r <;> simp [hA]
    _ = _ := sum_ite_of_unique
      (fun r : Fin (p ^ k) => Active a p k r ∧ SameSide a p k r i j)
      (Real.log (p : ℝ)) (fun r s hr hs => residue_unique a p k i r s
      (same_support a p k r i j hr.2) (same_support a p k s i j hs.2))

private theorem opposite_condition (a : ι → ℕ) (p k r : ℕ) (i j : ι)
    (hA : Active a p k r) (h : Opposite a p k r i j) :
    p ^ k ∣ a i + a j ∧ ¬p ^ k ∣ 2 * a i := by
  rcases h with ⟨hil, hjr⟩ | ⟨hir, hjl⟩
  · obtain ⟨hi, hci⟩ := (mem_leftClass a p k r i).1 hil
    obtain ⟨hj, hcj⟩ := (mem_rightClass a p k r j).1 hjr
    have hz := (hi.add_left (a j)).trans hj.modEq_zero_nat
    refine ⟨?_, not_dvd_two_of_modEq hi hA.2.2⟩
    simpa only [add_comm] using Nat.modEq_zero_iff_dvd.1 hz
  · obtain ⟨hi, hci⟩ := (mem_rightClass a p k r i).1 hir
    obtain ⟨hj, hcj⟩ := (mem_leftClass a p k r j).1 hjl
    have hz := (hj.add_left (a i)).trans hi.modEq_zero_nat
    exact ⟨Nat.modEq_zero_iff_dvd.1 hz, not_dvd_two_of_dvd_add hi hA.2.2⟩

private theorem same_condition (a : ι → ℕ) (p k r : ℕ) (i j : ι)
    (hA : Active a p k r) (h : SameSide a p k r i j) :
    p ^ k ∣ Nat.dist (a i) (a j) ∧ ¬p ^ k ∣ 2 * a i := by
  rcases h with ⟨hil, hjl⟩ | ⟨hir, hjr⟩
  · obtain ⟨hi, hci⟩ := (mem_leftClass a p k r i).1 hil
    obtain ⟨hj, hcj⟩ := (mem_leftClass a p k r j).1 hjl
    exact ⟨(modEq_iff_dvd_dist _ _ _).1 (hi.trans hj.symm),
      not_dvd_two_of_modEq hi hA.2.2⟩
  · obtain ⟨hi, hci⟩ := (mem_rightClass a p k r i).1 hir
    obtain ⟨hj, hcj⟩ := (mem_rightClass a p k r j).1 hjr
    exact ⟨(modEq_iff_dvd_dist _ _ _).1
      ((hi.modEq_zero_nat.trans hj.modEq_zero_nat.symm).add_right_cancel' r),
      not_dvd_two_of_dvd_add hi hA.2.2⟩

private theorem exists_active_oriented (a : ι → ℕ) (p k : ℕ) (i j : ι)
    (hq : 0 < p ^ k) (hadd : p ^ k ∣ a i + a j) (hself : ¬p ^ k ∣ 2 * a i)
    (hci : primeColor p (a i) = true) (hcj : primeColor p (a j) = false) :
    ∃ r : Fin (p ^ k), Active a p k r ∧
      i ∈ leftClass a p k r ∧ j ∈ rightClass a p k r := by
  let r : Fin (p ^ k) := ⟨a i % (p ^ k), Nat.mod_lt _ hq⟩
  have hm : a i ≡ (r : ℕ) [MOD p ^ k] := (Nat.mod_mod (a i) (p ^ k)).symm
  have hil : i ∈ leftClass a p k r := (mem_leftClass a p k r i).2 ⟨hm, hci⟩
  have hsum : p ^ k ∣ a j + a i := by simpa only [add_comm] using hadd
  have hjr : j ∈ rightClass a p k r := (mem_rightClass a p k r j).2
    ⟨Nat.modEq_zero_iff_dvd.1 ((hm.add_left (a j)).symm.trans hsum.modEq_zero_nat), hcj⟩
  exact ⟨r, ⟨⟨i, hil⟩, ⟨j, hjr⟩, not_dvd_two_of_modEq hm.symm hself⟩, hil, hjr⟩

/-- Every nonself sum level is represented, once the opposite-class color
lemma is supplied.  Occupancy follows from the two entries themselves. -/
theorem crossLevel_eq (a : ι → ℕ) (p k : ℕ) (i j : ι) (hq : 0 < p ^ k)
    (hflip : p ^ k ∣ a i + a j → ¬p ^ k ∣ 2 * a i →
      primeColor p (a i) ≠ primeColor p (a j)) :
    crossLevel a p k i j =
      if p ^ k ∣ a i + a j ∧ ¬p ^ k ∣ 2 * a i then Real.log (p : ℝ) else 0 := by
  classical
  rw [crossLevel_eq_ite_exists]
  have he : (∃ r : Fin (p ^ k), Active a p k r ∧ Opposite a p k r i j) ↔
      p ^ k ∣ a i + a j ∧ ¬p ^ k ∣ 2 * a i := by
    constructor
    · rintro ⟨r, hA, hO⟩
      exact opposite_condition a p k r i j hA hO
    · rintro ⟨hadd, hself⟩
      have hc := hflip hadd hself
      cases hci : primeColor p (a i) with
      | false =>
          have hcj : primeColor p (a j) = true :=
            Bool.eq_true_of_not_eq_false (fun hj => hc (hci.trans hj.symm))
          have hadd' : p ^ k ∣ a j + a i := by simpa only [add_comm] using hadd
          obtain ⟨r, hA, hjl, hir⟩ := exists_active_oriented a p k j i hq hadd'
            (nonself_opposite hadd hself) hcj hci
          exact ⟨r, hA, Or.inr ⟨hir, hjl⟩⟩
      | true =>
          have hcj : primeColor p (a j) = false :=
            Bool.eq_false_of_not_eq_true (fun hj => hc (hci.trans hj.symm))
          obtain ⟨r, hA, hil, hjr⟩ := exists_active_oriented a p k i j hq hadd hself hci hcj
          exact ⟨r, hA, Or.inl ⟨hil, hjr⟩⟩
  simp only [he]

/-- Deleting empty opposite classes only reduces the same-side kernel. -/
theorem diagLevel_le (a : ι → ℕ) (p k : ℕ) (i j : ι) :
    diagLevel a p k i j ≤
      if p ^ k ∣ Nat.dist (a i) (a j) ∧ ¬p ^ k ∣ 2 * a i
      then Real.log (p : ℝ) else 0 := by
  classical
  rw [diagLevel_eq_ite_exists]
  by_cases h : ∃ r : Fin (p ^ k), Active a p k r ∧ SameSide a p k r i j
  · obtain ⟨r, hA, hD⟩ := h
    have hex : ∃ r : Fin (p ^ k), Active a p k r ∧ SameSide a p k r i j := ⟨r, hA, hD⟩
    simp only [if_pos hex, if_pos (same_condition a p k r i j hA hD), le_refl]
  · rw [if_neg h]
    split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_refl 0

end Erdos126Aux.ResidueBlocks
