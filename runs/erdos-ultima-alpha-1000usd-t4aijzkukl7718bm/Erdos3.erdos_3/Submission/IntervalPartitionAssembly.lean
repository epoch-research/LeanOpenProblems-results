import Submission.PartialPartitionRefinement
import Submission.ProgressionFiberEquivalence

/-! Arbitrary local partial partitions can refine complete progression fibers,
with exact progression geometry and additive exceptional-mass losses. -/
namespace Erdos3IntervalPartitionAssembly
open Finset Erdos3PartialPartitionRefinement Erdos3ProgressionFiberEquivalence
  Erdos3IntervalProgressionPartition Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def coordinateRefineLabel {J : Type*} (N d M : ℕ) (hM : 0 < M)
    (b : Fin N → Fin M → Option J) : Fin N → Option (Fin N × J) :=
  refineLabel (progressionLabel N d M) (fun a x ↦ b a ⟨x.val/d%M,Nat.mod_lt _ hM⟩)

lemma coordinateRefineLabel_some_iff {J : Type*} {N d M : ℕ} (hM : 0 < M)
    (b : Fin N → Fin M → Option J) (x a : Fin N) (j : J) :
    coordinateRefineLabel N d M hM b x = some (a,j) ↔
      progressionLabel N d M x = some a ∧ b a ⟨x.val/d%M,Nat.mod_lt _ hM⟩ = some j := by
  letI : Nonempty (Fin N) := ⟨x⟩
  exact refineLabel_some_iff _ _ _ _ _

lemma progressionLabel_reconstruct {N d M : ℕ} {x a : Fin N}
    (hxa : progressionLabel N d M x = some a) :
    x.val = a.val+(x.val/d%M)*d := by
  obtain ⟨_,ha⟩ := progressionLabel_some_base hxa
  rw [ha]
  exact (blockBase_add_offset d M x.val).symm

lemma coordinateRefineLabel_bad_mass {J : Type*} {N d M : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hM : 0 < M) (b : Fin N → Fin M → Option J)
    {τ : ℝ} (hτ : 0 ≤ τ) (hb : ∀ a, cellMass (b a) none ≤ τ) :
    cellMass (coordinateRefineLabel N d M hM b) none ≤
      (d : ℝ)*(M : ℝ)/(N : ℝ)+τ := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hinner : cellMass (coordinateRefineLabel N d M hM b) none ≤
      cellMass (progressionLabel N d M) none+τ := by
    apply refineLabel_bad_mass _ _ hτ
    intro a
    by_cases ha : (cell (progressionLabel N d M) (some a)).Nonempty
    · rw [progressionLabel_inner_bad_charge hd hM a ha (b a)]
      have hh := hb a
      rw [cellMass_eq_card,Fintype.card_fin] at hh
      have hc := (div_le_iff₀ hM').mp hh
      rw [cellMass_eq_card,progressionLabel_cell_card hd hM a ha,Fintype.card_fin]
      calc
        _ ≤ (τ*(M : ℝ))/(N : ℝ) := div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)
        _ = _ := by ring
    · have hm : cellMass (progressionLabel N d M) (some a) = 0 := by
        rw [cellMass_eq_card,not_nonempty_iff_eq_empty.mp ha,card_empty,Nat.cast_zero,zero_div]
      rw [hm,mul_zero]
      have hh := abs_cellCharge_le (progressionLabel N d M)
        (fun x ↦ if b a ⟨x.val/d%M,Nat.mod_lt _ hM⟩ = none then 1 else 0)
        (fun _ ↦ by dsimp only; split_ifs <;> norm_num) (some a)
      rw [hm] at hh
      exact (le_abs_self _).trans hh
  apply hinner.trans
  apply add_le_add _ le_rfl
  rw [cellMass_eq_card,progressionLabel_bad_card hd hM,Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast (Nat.mod_lt N (Nat.mul_pos hd hM)).le

/-- Every good refined cell is exactly the image of one complete inner
progression under its outer positive-stride affine coordinate map. -/
theorem coordinateRefineLabel_geometry {J : Type*} {N d M L D : ℕ}
    (hd : 0 < d) (hM : 0 < M) (b : Fin N → Fin M → Option J)
    (hgeom : ∀ a j, (cell (b a) (some j)).Nonempty →
      ∃ s e : ℕ, 0 < e ∧ e ≤ D ∧ (∀ k < L, s+k*e < M) ∧
        ∀ y : Fin M, b a y = some j ↔ ∃ k : Fin L, y.val = s+k.val*e)
    (a : Fin N) (j : J)
    (hcell : (cell (coordinateRefineLabel N d M hM b) (some (a,j))).Nonempty) :
    ∃ s e : ℕ, 0 < e ∧ e ≤ D*d ∧ (∀ k < L, s+k*e < N) ∧
      ∀ x : Fin N, coordinateRefineLabel N d M hM b x = some (a,j) ↔
        ∃ k : Fin L, x.val = s+k.val*e := by
  obtain ⟨x,hx⟩ := hcell
  obtain ⟨hxa,hxj⟩ := (coordinateRefineLabel_some_iff hM b x a j).mp ((mem_cell_iff _ _ _).mp hx)
  have ha : (cell (progressionLabel N d M) (some a)).Nonempty := ⟨x,(mem_cell_iff _ _ _).mpr hxa⟩
  have hj : (cell (b a) (some j)).Nonempty :=
    ⟨⟨x.val/d%M,Nat.mod_lt _ hM⟩,(mem_cell_iff _ _ _).mpr hxj⟩
  obtain ⟨hout,hfiber⟩ := progressionLabel_fiber hd hM a ha
  obtain ⟨s,e,he,heD,hin,hinner⟩ := hgeom a j hj
  refine ⟨a.val+s*d,e*d,Nat.mul_pos he hd,Nat.mul_le_mul_right d heD,?_,?_⟩
  · intro k hk
    convert hout (s+k*e) (hin k hk) using 1 <;> ring
  · intro y
    rw [coordinateRefineLabel_some_iff hM b y a j]
    constructor
    · rintro ⟨hya,hyj⟩
      obtain ⟨k,hk⟩ := (hinner _).mp hyj
      have hy := progressionLabel_reconstruct hya
      change y.val/d%M = s+k.val*e at hk
      refine ⟨k,?_⟩
      rw [hy,hk]
      ring
    · rintro ⟨k,hk⟩
      let z : Fin M := ⟨s+k.val*e,hin k k.isLt⟩
      have hy : y.val = a.val+z.val*d := by rw [hk]; dsimp [z]; ring
      refine ⟨(hfiber y).mpr ⟨z,hy⟩,?_⟩
      have hcoord : (⟨y.val/d%M,Nat.mod_lt _ hM⟩ : Fin M) = z := by
        apply Fin.ext
        change y.val/d%M = z.val
        rw [hy]
        exact progressionLabel_coordinate hd hM a ha z.isLt
      rw [hcoord]
      exact (hinner z).mpr ⟨k,rfl⟩

#print axioms coordinateRefineLabel_bad_mass
#print axioms coordinateRefineLabel_geometry
end Erdos3IntervalPartitionAssembly
