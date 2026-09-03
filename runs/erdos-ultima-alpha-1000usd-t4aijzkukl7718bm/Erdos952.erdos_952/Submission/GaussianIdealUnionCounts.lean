import Submission.GaussianIdealBoxCounts

/-! Finite unions of principal-ideal residue classes have an explicit box
counting error. The error includes the number of classes; no uniform
long-prime-path estimate is asserted. -/
namespace Erdos952Investigation.GaussianIdealUnionCounts
open GaussianIdealRepresentatives GaussianIdealBoxCounts
open scoped BigOperators
set_option maxHeartbeats 0

abbrev ResiduePoints (g : GaussianInt) (S : Finset (GaussianInt ⧸ multiples g))
    (a : GaussianInt) (R : ℕ) :=
  {z : GaussianInt // InBox a R z ∧ Submodule.Quotient.mk z ∈ S}

instance (g : GaussianInt) (S : Finset (GaussianInt ⧸ multiples g))
    (a : GaussianInt) (R : ℕ) : Finite (ResiduePoints g S a R) := by
  let f : ResiduePoints g S a R → Box a R := fun z => ⟨z.val,z.property.1⟩
  apply Finite.of_injective f
  intro z w he
  exact Subtype.ext (congrArg (fun z : Box a R => z.val) he)

noncomputable def residueCount (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card (ResiduePoints g S a R)

noncomputable def residueEquiv (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R : ℕ) :
    ResiduePoints g S a R ≃ Σ c : S, CosetPoints g c.val a R where
  toFun z := ⟨⟨Submodule.Quotient.mk z.val,z.property.2⟩,⟨z.val,z.property.1,rfl⟩⟩
  invFun z := ⟨z.2.val,z.2.property.1,by rw [z.2.property.2]; exact z.1.property⟩
  left_inv z := by rfl
  right_inv z := by
    rcases z with ⟨⟨c,hc⟩,⟨z,hz,hq⟩⟩
    dsimp at hq
    subst c
    rfl

lemma residueCount_eq_sum (g : GaussianInt)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R : ℕ) :
    residueCount g S a R = ∑ c ∈ S, cosetCount g c a R := by
  classical
  rw [residueCount,Nat.card_congr (residueEquiv g S a R),Nat.card_sigma]
  exact Finset.sum_coe_sort S (fun c => cosetCount g c a R)

/-- The residue-class multiplicity is retained in both the main term and
the boundary error. -/
theorem residue_count_sqrt_error (g : GaussianInt) (hg : g ≠ 0)
    (S : Finset (GaussianInt ⧸ multiples g)) (a : GaussianInt) (R : ℕ) :
    |(residueCount g S a R : ℝ)-(S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      (S.card : ℝ)*(4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4) := by
  classical
  rw [residueCount_eq_sum,Nat.cast_sum]
  have he : (∑ c ∈ S, (cosetCount g c a R : ℝ))-
      (S.card : ℝ)*(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      ∑ c ∈ S, ((cosetCount g c a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ)) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑ c ∈ S, |(cosetCount g c a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S, (4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4) :=
      Finset.sum_le_sum (fun c _ => coset_count_sqrt_error g hg c a R)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

#print axioms residue_count_sqrt_error
end Erdos952Investigation.GaussianIdealUnionCounts
