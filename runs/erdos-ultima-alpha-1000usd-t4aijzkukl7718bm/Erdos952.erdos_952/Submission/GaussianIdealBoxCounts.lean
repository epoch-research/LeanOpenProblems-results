import Submission.GaussianIdealRepresentatives

/-! A discrete lattice-packing estimate for a Gaussian-ideal coset. The main
term is the box area divided by the ideal index, with an explicit boundary
error. This is a counting tool, not a bound for long Gaussian-prime paths. -/
namespace Erdos952Investigation.GaussianIdealBoxCounts
open GaussianIdealRepresentatives
set_option maxHeartbeats 0

def InBox (a : GaussianInt) (R : ℕ) (z : GaussianInt) : Prop :=
  a.re ≤ z.re ∧ z.re < a.re+(R : ℤ) ∧ a.im ≤ z.im ∧ z.im < a.im+(R : ℤ)

abbrev Box (a : GaussianInt) (R : ℕ) := {z : GaussianInt // InBox a R z}

def boxEquiv (a : GaussianInt) (R : ℕ) : Box a R ≃ Fin R × Fin R where
  toFun z :=
    (⟨(z.val.re-a.re).toNat,by have h := z.property; dsimp [InBox] at h; omega⟩,
     ⟨(z.val.im-a.im).toNat,by have h := z.property; dsimp [InBox] at h; omega⟩)
  invFun i := ⟨a+⟨i.1.val,i.2.val⟩,by
    have h₁ := i.1.isLt
    have h₂ := i.2.isLt
    dsimp [InBox]
    omega⟩
  left_inv z := by
    apply Subtype.ext
    have h := z.property
    dsimp [InBox] at h
    apply Zsqrtd.ext <;> dsimp <;> omega
  right_inv i := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

instance (a : GaussianInt) (R : ℕ) : Finite (Box a R) :=
  Finite.of_injective (boxEquiv a R) (boxEquiv a R).injective

lemma box_card (a : GaussianInt) (R : ℕ) : Nat.card (Box a R) = R^2 := by
  rw [Nat.card_congr (boxEquiv a R),Nat.card_prod,Nat.card_fin,pow_two]

abbrev CosetPoints (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a : GaussianInt) (R : ℕ) :=
  {z : GaussianInt // InBox a R z ∧ Submodule.Quotient.mk z = c}

instance (g : GaussianInt) (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    Finite (CosetPoints g c a R) := by
  let f : CosetPoints g c a R → Box a R := fun z => ⟨z.val,z.property.1⟩
  apply Finite.of_injective f
  intro z w he
  apply Subtype.ext
  exact congrArg (fun z : Box a R => z.val) he

noncomputable def cosetCount (g : GaussianInt) (c : GaussianInt ⧸ multiples g)
    (a : GaussianInt) (R : ℕ) : ℕ := Nat.card (CosetPoints g c a R)

/-- Translate a bounded representative system from each coset point. These
sets are disjoint and lie in the square enlarged by twice the representative
radius. This is a discrete argument; no area approximation is assumed. -/
theorem coset_count_upper (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    g.norm.natAbs*cosetCount g c a R ≤ (R+2*Nat.sqrt g.norm.natAbs)^2 := by
  let B := Nat.sqrt g.norm.natAbs
  let b : GaussianInt := a-⟨B,B⟩
  let f : (GaussianInt ⧸ multiples g) × CosetPoints g c a R → Box b (R+2*B) :=
    fun z => ⟨z.2.val+representative g hg z.1,by
      have hz := z.2.property.1
      have hr := abs_le.mp (representative_coordinates g hg z.1).1
      have hi := abs_le.mp (representative_coordinates g hg z.1).2
      dsimp only [InBox] at hz
      dsimp only [InBox,b]
      simp only [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_sub,Zsqrtd.im_sub,
        Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      change -(B : ℤ) ≤ (representative g hg z.1).re ∧
        (representative g hg z.1).re ≤ B at hr
      change -(B : ℤ) ≤ (representative g hg z.1).im ∧
        (representative g hg z.1).im ≤ B at hi
      omega⟩
  have hf : Function.Injective f := by
    intro u v he
    have hp := congrArg (fun z : Box b (R+2*B) => z.val) he
    change u.2.val+representative g hg u.1 = v.2.val+representative g hg v.1 at hp
    have hq := congrArg (Submodule.Quotient.mk (p := multiples g)) hp
    simp only [Submodule.Quotient.mk_add,representative_class,
      u.2.property.2,v.2.property.2] at hq
    have huv : u.1 = v.1 := add_left_cancel hq
    apply Prod.ext huv
    apply Subtype.ext
    rw [huv] at hp
    exact add_right_cancel hp
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,quotient_card g hg,box_card] at hh
  exact hh

/-- The shrunken square is covered by the bounded representatives translated
from coset points of the original square. -/
theorem coset_count_lower (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    (R-2*Nat.sqrt g.norm.natAbs)^2 ≤ g.norm.natAbs*cosetCount g c a R := by
  let B := Nat.sqrt g.norm.natAbs
  by_cases hR : 2*B ≤ R
  · letI : Finite (GaussianInt ⧸ multiples g) := quotient_finite g hg
    let b : GaussianInt := a+⟨B,B⟩
    let f : Box b (R-2*B) → (GaussianInt ⧸ multiples g) × CosetPoints g c a R :=
      fun w => by
        let q : GaussianInt ⧸ multiples g := Submodule.Quotient.mk w.val-c
        refine (q,⟨w.val-representative g hg q,?_,?_⟩)
        · have hw := w.property
          have hr := abs_le.mp (representative_coordinates g hg q).1
          have hi := abs_le.mp (representative_coordinates g hg q).2
          dsimp only [InBox,b] at hw
          dsimp only [InBox]
          simp only [Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_sub,Zsqrtd.im_sub] at hw ⊢
          change -(B : ℤ) ≤ (representative g hg q).re ∧
            (representative g hg q).re ≤ B at hr
          change -(B : ℤ) ≤ (representative g hg q).im ∧
            (representative g hg q).im ≤ B at hi
          omega
        · rw [Submodule.Quotient.mk_sub,representative_class]
          dsimp [q]
          abel
    have hf : Function.Injective f := by
      intro u v he
      have hq := congrArg Prod.fst he
      change (Submodule.Quotient.mk u.val : GaussianInt ⧸ multiples g)-c =
        Submodule.Quotient.mk v.val-c at hq
      have hz := congrArg (fun z : (GaussianInt ⧸ multiples g) × CosetPoints g c a R => z.2.val) he
      change u.val-representative g hg (Submodule.Quotient.mk u.val-c) =
        v.val-representative g hg (Submodule.Quotient.mk v.val-c) at hz
      rw [hq] at hz
      exact Subtype.ext (sub_left_injective hz)
    have hh := Nat.card_le_card_of_injective f hf
    rw [box_card,Nat.card_prod,quotient_card g hg] at hh
    exact hh
  · have hz : R-2*Nat.sqrt g.norm.natAbs = 0 := by dsimp [B] at hR; omega
    rw [hz]
    simp

/-- Multiplying the count by the ideal index gives the square's area, with
an explicit boundary discrepancy uniform in both the coset and the anchor. -/
theorem coset_count_discrepancy (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    |(g.norm.natAbs : ℤ)*(cosetCount g c a R : ℤ)-(R : ℤ)^2| ≤
      4*(R : ℤ)*(Nat.sqrt g.norm.natAbs : ℤ)+4*(Nat.sqrt g.norm.natAbs : ℤ)^2 := by
  let B := Nat.sqrt g.norm.natAbs
  have hu : (g.norm.natAbs : ℤ)*(cosetCount g c a R : ℤ) ≤ ((R : ℤ)+2*(B : ℤ))^2 := by
    exact_mod_cast coset_count_upper g hg c a R
  have hp : (0 : ℤ) ≤ (g.norm.natAbs : ℤ)*(cosetCount g c a R : ℤ) := by positivity
  apply abs_le.mpr
  constructor
  · by_cases hR : 2*B ≤ R
    · have hl : ((R-2*B : ℕ) : ℤ)^2 ≤ (g.norm.natAbs : ℤ)*(cosetCount g c a R : ℤ) := by
        exact_mod_cast coset_count_lower g hg c a R
      have hs : ((R-2*B : ℕ) : ℤ) = (R : ℤ)-2*(B : ℤ) := by omega
      rw [hs] at hl
      change -(4*(R : ℤ)*(B : ℤ)+4*(B : ℤ)^2) ≤ _
      nlinarith [sq_nonneg (B : ℤ)]
    · have hr : (R : ℤ) < 2*(B : ℤ) := by omega
      have hB : (0 : ℤ) ≤ B := Int.natCast_nonneg B
      have hR0 : (0 : ℤ) ≤ R := Int.natCast_nonneg R
      change -(4*(R : ℤ)*(B : ℤ)+4*(B : ℤ)^2) ≤ _
      nlinarith
  · change _ ≤ 4*(R : ℤ)*(B : ℤ)+4*(B : ℤ)^2
    nlinarith

/-- Normalized discrepancy suitable for a sieve remainder: the area is
R^2/norm(g), not an unspecified multiple of that main term. -/
theorem coset_count_real_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    |(cosetCount g c a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      (4*(R : ℝ)*(Nat.sqrt g.norm.natAbs : ℝ)+4*(Nat.sqrt g.norm.natAbs : ℝ)^2)/
        (g.norm.natAbs : ℝ) := by
  have hn : 0 < g.norm.natAbs := Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hm : (0 : ℝ) < g.norm.natAbs := by exact_mod_cast hn
  have hh : |(g.norm.natAbs : ℝ)*(cosetCount g c a R : ℝ)-(R : ℝ)^2| ≤
      4*(R : ℝ)*(Nat.sqrt g.norm.natAbs : ℝ)+4*(Nat.sqrt g.norm.natAbs : ℝ)^2 := by
    exact_mod_cast coset_count_discrepancy g hg c a R
  have he : (cosetCount g c a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ) =
      ((g.norm.natAbs : ℝ)*(cosetCount g c a R : ℝ)-(R : ℝ)^2)/(g.norm.natAbs : ℝ) := by
    field_simp
  rw [he,abs_div,abs_of_pos hm]
  exact div_le_div_of_nonneg_right hh hm.le

/-- The elementary lattice discrepancy has the expected inverse-square-root
scale in the ideal index, uniformly over all translated squares and cosets. -/
theorem coset_count_sqrt_error (g : GaussianInt) (hg : g ≠ 0)
    (c : GaussianInt ⧸ multiples g) (a : GaussianInt) (R : ℕ) :
    |(cosetCount g c a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4 := by
  have hn : 0 < g.norm.natAbs := Int.natAbs_pos.mpr (GaussianInt.norm_eq_zero.not.mpr hg)
  have hm : (0 : ℝ) < g.norm.natAbs := by exact_mod_cast hn
  have hB : (Nat.sqrt g.norm.natAbs : ℝ)^2 ≤ (g.norm.natAbs : ℝ) := by
    exact_mod_cast Nat.sqrt_le' g.norm.natAbs
  have hBs := Real.le_sqrt_of_sq_le hB
  apply (coset_count_real_error g hg c a R).trans
  calc
    (4*(R : ℝ)*(Nat.sqrt g.norm.natAbs : ℝ)+4*(Nat.sqrt g.norm.natAbs : ℝ)^2)/
        (g.norm.natAbs : ℝ) ≤
      (4*(R : ℝ)*Real.sqrt (g.norm.natAbs : ℝ)+4*(g.norm.natAbs : ℝ))/(g.norm.natAbs : ℝ) := by
      apply div_le_div_of_nonneg_right _ hm.le
      have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      nlinarith
    _ = 4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4 := by
      rw [add_div,mul_div_assoc,Real.sqrt_div_self']
      field_simp

noncomputable def idealCosetCount (g t a : GaussianInt) (R : ℕ) : ℕ :=
  Nat.card {z : GaussianInt // InBox a R z ∧ g ∣ z-t}

lemma idealCosetCount_eq (g t a : GaussianInt) (R : ℕ) :
    idealCosetCount g t a R = cosetCount g (Submodule.Quotient.mk t) a R := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro z
  rw [quotient_eq_iff_dvd]

/-- The same estimate stated with divisibility rather than quotient classes.
No prime-path or growing-pattern assertion is included. -/
theorem ideal_coset_sqrt_error (g : GaussianInt) (hg : g ≠ 0)
    (t a : GaussianInt) (R : ℕ) :
    |(idealCosetCount g t a R : ℝ)-(R : ℝ)^2/(g.norm.natAbs : ℝ)| ≤
      4*(R : ℝ)/Real.sqrt (g.norm.natAbs : ℝ)+4 := by
  rw [idealCosetCount_eq]
  exact coset_count_sqrt_error g hg _ a R

#print axioms coset_count_sqrt_error
#print axioms ideal_coset_sqrt_error
#print axioms coset_count_upper
#print axioms coset_count_lower
#print axioms coset_count_discrepancy
#print axioms coset_count_real_error
end Erdos952Investigation.GaussianIdealBoxCounts
