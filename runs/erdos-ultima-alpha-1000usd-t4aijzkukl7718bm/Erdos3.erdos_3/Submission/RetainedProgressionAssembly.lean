import Submission.RestrictedProgressionRefinement
import Submission.PartialPartitionRefinement

/-! Refining retained complete progression fibers by arbitrary local partial
partitions. Both exceptional mass and exact progression geometry are preserved. -/
namespace Erdos3RetainedProgressionAssembly
open Finset Erdos3RestrictedProgressionRefinement Erdos3RestrictedPartialPartition
  Erdos3ProgressionFiberEquivalence Erdos3IntervalProgressionPartition
  Erdos3PartialPartitionRefinement Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

lemma retained_fiber_info {N d K : ℕ} (B : Finset (Fin N)) (a : Fin N)
    (ha : (cell (restrictLabel B (progressionLabel N d K)) (some a)).Nonempty) :
    (cell (progressionLabel N d K) (some a)).Nonempty ∧
      cell (progressionLabel N d K) (some a) ⊆ B := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨hx',hfull⟩ := (restrictLabel_some_iff B _ x a).mp ((mem_cell_iff _ _ _).mp hx)
  exact ⟨⟨x.val,(mem_cell_iff _ _ _).mpr hx'⟩,hfull⟩

noncomputable def retainedRefineLabel {N d K : ℕ} {J : Type*}
    (B : Finset (Fin N)) (hK : 0 < K) (b : Fin N → Fin K → Option J) : B → Option (Fin N × J) :=
  refineLabel (restrictLabel B (progressionLabel N d K))
    (fun a x ↦ b a ⟨x.val.val/d%K,Nat.mod_lt _ hK⟩)

lemma retainedRefineLabel_some_iff {N d K : ℕ} {J : Type*}
    (B : Finset (Fin N)) (hK : 0 < K) (b : Fin N → Fin K → Option J)
    (x : B) (a : Fin N) (i : J) :
    retainedRefineLabel (d := d) B hK b x = some (a,i) ↔
      restrictLabel B (progressionLabel N d K) x = some a ∧
      b a ⟨x.val.val/d%K,Nat.mod_lt _ hK⟩ = some i := by
  letI : Nonempty B := ⟨x⟩
  exact refineLabel_some_iff _ _ _ _ _

theorem retainedRefineLabel_bad_mass {N d K : ℕ} {J : Type*}
    (B : Finset (Fin N)) (hB : B.Nonempty) (hd : 0 < d) (hK : 0 < K)
    (b : Fin N → Fin K → Option J) {τ : ℝ} (hτ : 0 ≤ τ)
    (hbad : ∀ a, (cell (restrictLabel B (progressionLabel N d K)) (some a)).Nonempty →
      cellMass (b a) none ≤ τ) :
    cellMass (retainedRefineLabel (d := d) B hK b) none ≤
      cellMass (restrictLabel B (progressionLabel N d K)) none+τ := by
  letI : Nonempty B := hB.to_subtype
  apply refineLabel_bad_mass _ _ hτ
  intro a
  by_cases ha : (cell (restrictLabel B (progressionLabel N d K)) (some a)).Nonempty
  · obtain ⟨ha',hfull⟩ := retained_fiber_info B a ha
    rw [restricted_progression_inner_bad_charge hd hK B a ha' hfull (b a)]
    exact (mul_le_mul_of_nonneg_left (hbad a ha) (cellMass_nonneg _ _)).trans_eq (mul_comm _ _)
  · have hm : cellMass (restrictLabel B (progressionLabel N d K)) (some a) = 0 := by
      rw [cellMass_eq_card,Finset.not_nonempty_iff_eq_empty.mp ha,card_empty,Nat.cast_zero,zero_div]
    rw [hm,mul_zero]
    have hh := abs_cellCharge_le (restrictLabel B (progressionLabel N d K))
      (fun x ↦ if b a ⟨x.val.val/d%K,Nat.mod_lt _ hK⟩ = none then 1 else 0)
      (fun x ↦ by dsimp only; split_ifs <;> norm_num) (some a)
    rw [hm] at hh
    exact (le_abs_self _).trans hh

/-- Inner progression fibers of any shape compose with the retained coarse
progression. Every listed progression point belongs to B, and the entire
refined fiber is exactly that progression. -/
theorem retainedRefineLabel_geometry {N d K L D : ℕ} {J : Type*}
    (B : Finset (Fin N)) (hd : 0 < d) (hK : 0 < K)
    (b : Fin N → Fin K → Option J)
    (hgeom : ∀ a, (cell (restrictLabel B (progressionLabel N d K)) (some a)).Nonempty →
      ∀ i, (cell (b a) (some i)).Nonempty →
      ∃ s e : ℕ, 0 < e ∧ e ≤ D ∧ (∀ j < L, s+j*e < K) ∧
        ∀ k : Fin K, b a k = some i ↔ ∃ j : Fin L, k.val = s+j.val*e)
    (a : Fin N) (i : J)
    (hai : (cell (retainedRefineLabel (d := d) B hK b) (some (a,i))).Nonempty) :
    ∃ s e : ℕ, 0 < e ∧ e ≤ D*d ∧
      (∀ j < L, ∃ x : B, x.val.val = s+j*e) ∧
      ∀ x : B, retainedRefineLabel (d := d) B hK b x = some (a,i) ↔
        ∃ j : Fin L, x.val.val = s+j.val*e := by
  obtain ⟨x,hx⟩ := hai
  obtain ⟨hxa,hxi⟩ := (retainedRefineLabel_some_iff B hK b x a i).mp ((mem_cell_iff _ _ _).mp hx)
  have ha : (cell (restrictLabel B (progressionLabel N d K)) (some a)).Nonempty :=
    ⟨x,(mem_cell_iff _ _ _).mpr hxa⟩
  have hi : (cell (b a) (some i)).Nonempty :=
    ⟨⟨x.val.val/d%K,Nat.mod_lt _ hK⟩,(mem_cell_iff _ _ _).mpr hxi⟩
  obtain ⟨ha',hfull⟩ := retained_fiber_info B a ha
  obtain ⟨houter,hfiber⟩ := progressionLabel_fiber hd hK a ha'
  obtain ⟨s,e,he,heD,hinner,hfiber'⟩ := hgeom a ha i hi
  refine ⟨a.val+s*d,e*d,Nat.mul_pos he hd,Nat.mul_le_mul_right d heD,?_,?_⟩
  · intro j hj
    let l : Fin K := ⟨s+j*e,hinner j hj⟩
    let y : Fin N := ⟨a.val+l.val*d,houter l l.isLt⟩
    have hy : y ∈ B := hfull ((mem_cell_iff _ _ _).mpr ((hfiber y).mpr ⟨l,rfl⟩))
    refine ⟨⟨y,hy⟩,?_⟩
    dsimp [y,l]
    ring
  · intro y
    rw [retainedRefineLabel_some_iff B hK b y a i]
    constructor
    · rintro ⟨hya,hyi⟩
      have hya' := ((restrictLabel_some_iff B _ y a).mp hya).1
      obtain ⟨_,hay⟩ := progressionLabel_some_base hya'
      obtain ⟨j,hj⟩ := (hfiber' _).mp hyi
      have hyval : y.val.val = a.val+(y.val.val/d%K)*d := by
        rw [hay]
        exact (blockBase_add_offset d K y.val.val).symm
      refine ⟨j,?_⟩
      change y.val.val/d%K = s+j.val*e at hj
      rw [hyval,hj]
      ring
    · rintro ⟨j,hj⟩
      let l : Fin K := ⟨s+j.val*e,hinner j j.isLt⟩
      have hy : y.val.val = a.val+l.val*d := by rw [hj]; dsimp [l]; ring
      refine ⟨(restrictLabel_some_iff B _ y a).mpr ⟨(hfiber y.val).mpr ⟨l,hy⟩,hfull⟩,?_⟩
      have hcoord : (⟨y.val.val/d%K,Nat.mod_lt _ hK⟩ : Fin K) = l := by
        apply Fin.ext
        change y.val.val/d%K = l.val
        rw [hy]
        exact progressionLabel_coordinate hd hK a ha' l.isLt
      rw [hcoord]
      exact (hfiber' l).mpr ⟨j,rfl⟩

#print axioms retainedRefineLabel_bad_mass
#print axioms retainedRefineLabel_geometry
end Erdos3RetainedProgressionAssembly
