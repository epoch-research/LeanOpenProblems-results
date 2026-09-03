import Submission.StableBohrQuadraticPartition

/-! Exact averaging and properness for a cell specified by a natural-index
arithmetic progression. -/
namespace Erdos3ProgressionCellMean
open Finset Erdos3FinitePartitionIncrement Erdos3ProgressionFiberEquivalence
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

noncomputable def progressionCellEquiv {N L : ℕ} {J : Type*}
    (B : Finset (Fin N)) (c : B → Option J) (i : J) (a d : ℕ) (hd : 0 < d)
    (hpoints : ∀ j < L, ∃ x : B, x.val.val = a+j*d)
    (hfiber : ∀ x : B, c x = some i ↔ ∃ j : Fin L, x.val.val = a+j.val*d) :
    Fin L ≃ cell c (some i) := by
  let f : Fin L → cell c (some i) := fun j ↦
    ⟨(hpoints j.val j.isLt).choose,(mem_cell_iff _ _ _).mpr
      ((hfiber _).mpr ⟨j,(hpoints j.val j.isLt).choose_spec⟩)⟩
  have hval (j : Fin L) : (f j).val.val.val = a+j.val*d := (hpoints j.val j.isLt).choose_spec
  apply Equiv.ofBijective f
  constructor
  · intro j k hjk
    have hh := congrArg (fun x : cell c (some i) ↦ x.val.val.val) hjk
    dsimp only at hh
    rw [hval,hval] at hh
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hh))
  · intro x
    obtain ⟨j,hj⟩ := (hfiber x.val).mp ((mem_cell_iff _ _ _).mp x.property)
    refine ⟨j,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    exact (hval j).trans hj.symm

lemma progressionCellEquiv_val {N L : ℕ} {J : Type*}
    (B : Finset (Fin N)) (c : B → Option J) (i : J) (a d : ℕ) (hd : 0 < d)
    (hpoints : ∀ j < L, ∃ x : B, x.val.val = a+j*d)
    (hfiber : ∀ x : B, c x = some i ↔ ∃ j : Fin L, x.val.val = a+j.val*d) (j : Fin L) :
    (progressionCellEquiv B c i a d hd hpoints hfiber j).val.val.val = a+j.val*d :=
  (hpoints j.val j.isLt).choose_spec

lemma progressionCell_mean {N L : ℕ} {J W : Type*} [AddCommMonoid W] [Module ℚ≥0 W]
    (B : Finset (Fin N)) (c : B → Option J) (i : J) (a d : ℕ) (hd : 0 < d)
    (hpoints : ∀ j < L, ∃ x : B, x.val.val = a+j*d)
    (hfiber : ∀ x : B, c x = some i ↔ ∃ j : Fin L, x.val.val = a+j.val*d) (F : ℕ → W) :
    (𝔼 x : cell c (some i), F x.val.val.val) = 𝔼 j : Fin L, F (a+j.val*d) := by
  apply (Fintype.expect_equiv (progressionCellEquiv B c i a d hd hpoints hfiber) _ _ ?_).symm
  intro j
  rw [progressionCellEquiv_val]

lemma shifted_nat_AP_injective (p L a d : ℕ) [NeZero p] (hd : 0 < d)
    (hbelow : ∀ j < L, a+j*d < p) (b : ZMod p) :
    Function.Injective (fun j : Fin L ↦ b+((a+j.val*d : ℕ) : ZMod p)) := by
  intro i j hij
  have he := congrArg ZMod.val (add_left_cancel hij)
  rw [ZMod.val_natCast_of_lt (hbelow i i.isLt),ZMod.val_natCast_of_lt (hbelow j j.isLt)] at he
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he))

#print axioms progressionCell_mean
#print axioms shifted_nat_AP_injective
end Erdos3ProgressionCellMean
