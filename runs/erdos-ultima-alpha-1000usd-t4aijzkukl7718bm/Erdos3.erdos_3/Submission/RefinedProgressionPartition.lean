import Submission.ProgressionFiberEquivalence
import Submission.PartialPartitionRefinement

/-! Geometry and exceptional-mass bookkeeping for a two-level progression
partition. The second stride may depend on the first-level fiber. -/
namespace Erdos3RefinedProgressionPartition
open Finset Erdos3IntervalProgressionPartition Erdos3ProgressionFiberEquivalence
  Erdos3PartialPartitionRefinement Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def refinedProgressionLabel (N d M L : ℕ) (hM : 0 < M)
    (d₂ : Fin N → ℕ) : Fin N → Option (Fin N × Fin M) :=
  refineLabel (progressionLabel N d M)
    (fun a k ↦ progressionLabel M (d₂ a) L ⟨k.val/d%M,Nat.mod_lt _ hM⟩)

lemma refinedProgressionLabel_some_iff {N d M L : ℕ} (hM : 0 < M)
    (d₂ : Fin N → ℕ) (k a : Fin N) (b : Fin M) :
    refinedProgressionLabel N d M L hM d₂ k = some (a,b) ↔
      progressionLabel N d M k = some a ∧
      progressionLabel M (d₂ a) L ⟨k.val/d%M,Nat.mod_lt _ hM⟩ = some b := by
  letI : Nonempty (Fin N) := ⟨k⟩
  exact refineLabel_some_iff _ _ _ _ _

/-- Each nonexceptional refined fiber is a proper length-L progression. Its
stride is the product of the outer stride and that fiber's inner stride. -/
theorem refinedProgressionLabel_geometry {N d M L : ℕ}
    (hd : 0 < d) (hM : 0 < M) (hL : 0 < L) (d₂ : Fin N → ℕ)
    (hd₂ : ∀ a, 0 < d₂ a) (a : Fin N) (b : Fin M)
    (hab : (cell (refinedProgressionLabel N d M L hM d₂) (some (a,b))).Nonempty) :
    (∀ j < L, a.val+b.val*d+j*(d₂ a*d) < N) ∧
    (∀ k : Fin N, refinedProgressionLabel N d M L hM d₂ k = some (a,b) ↔
      ∃ j : Fin L, k.val = a.val+b.val*d+j.val*(d₂ a*d)) := by
  obtain ⟨x,hx⟩ := hab
  obtain ⟨hxa,hxb⟩ := (refinedProgressionLabel_some_iff hM d₂ x a b).mp ((mem_cell_iff _ _ _).mp hx)
  have ha : (cell (progressionLabel N d M) (some a)).Nonempty :=
    ⟨x,(mem_cell_iff _ _ _).mpr hxa⟩
  have hb : (cell (progressionLabel M (d₂ a) L) (some b)).Nonempty :=
    ⟨⟨x.val/d%M,Nat.mod_lt _ hM⟩,(mem_cell_iff _ _ _).mpr hxb⟩
  obtain ⟨houter,hfiber⟩ := progressionLabel_fiber hd hM a ha
  obtain ⟨hinner,hfiber'⟩ := progressionLabel_fiber (hd₂ a) hL b hb
  refine ⟨?_,?_⟩
  · intro j hj
    convert houter (b.val+j*d₂ a) (hinner j hj) using 1 <;> ring
  · intro k
    rw [refinedProgressionLabel_some_iff hM d₂ k a b]
    constructor
    · rintro ⟨hka,hkb⟩
      obtain ⟨j,hj⟩ := (hfiber' _).mp hkb
      obtain ⟨_,hak⟩ := progressionLabel_some_base hka
      have he : k.val = a.val+(k.val/d%M)*d := by
        rw [hak]
        exact (blockBase_add_offset d M k.val).symm
      refine ⟨j,?_⟩
      change k.val/d%M = b.val+j.val*d₂ a at hj
      rw [he,hj]
      ring
    · rintro ⟨j,hj⟩
      let l : Fin M := ⟨b.val+j.val*d₂ a,hinner j j.isLt⟩
      have hk : k.val = a.val+l.val*d := by rw [hj]; dsimp [l]; ring
      refine ⟨(hfiber k).mpr ⟨l,hk⟩,?_⟩
      have hcoord : (⟨k.val/d%M,Nat.mod_lt _ hM⟩ : Fin M) = l := by
        apply Fin.ext
        change k.val/d%M = l.val
        rw [hk]
        exact progressionLabel_coordinate hd hM a ha l.isLt
      rw [hcoord]
      exact (hfiber' l).mpr ⟨j,rfl⟩

/-- If every inner partition leaves at most B exceptional local indices,
the total additional exceptional proportion is at most B/M. -/
theorem refinedProgressionLabel_bad_mass {N d M L : ℕ}
    (hN : 0 < N) (hd : 0 < d) (hM : 0 < M) (d₂ : Fin N → ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbad : ∀ a, ((cell (progressionLabel M (d₂ a) L) none).card : ℝ) ≤ B) :
    cellMass (refinedProgressionLabel N d M L hM d₂) none ≤
      cellMass (progressionLabel N d M) none+B/(M : ℝ) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  apply refineLabel_bad_mass _ _ (by positivity : 0 ≤ B/(M : ℝ))
  intro a
  by_cases ha : (cell (progressionLabel N d M) (some a)).Nonempty
  · rw [progressionLabel_inner_bad_charge hd hM a ha (progressionLabel M (d₂ a) L),
      cellMass_eq_card,progressionLabel_cell_card hd hM a ha,Fintype.card_fin]
    calc
      _ ≤ B/(N : ℝ) := div_le_div_of_nonneg_right (hbad a) (Nat.cast_nonneg _)
      _ = B/(M : ℝ)*((M : ℝ)/(N : ℝ)) := by field_simp
  · have hm : cellMass (progressionLabel N d M) (some a) = 0 := by
      rw [cellMass_eq_card,Finset.not_nonempty_iff_eq_empty.mp ha,card_empty,Nat.cast_zero,zero_div]
    rw [hm,mul_zero]
    have hh := abs_cellCharge_le (progressionLabel N d M)
      (fun k ↦ if progressionLabel M (d₂ a) L ⟨k.val/d%M,Nat.mod_lt _ hM⟩ = none then 1 else 0)
      (fun k ↦ by dsimp only; split_ifs <;> norm_num) (some a)
    rw [hm] at hh
    exact (le_abs_self _).trans hh

#print axioms refinedProgressionLabel_geometry
#print axioms refinedProgressionLabel_bad_mass
end Erdos3RefinedProgressionPartition
