import FormalConjecturesUtil

/-! Coordinate-subgroup cardinal bounds for Suzuki root groups.
These algebraic lemmas do not settle the extremal-exponent conjecture. -/
namespace Erdos713SuzukiRootCoordinates
variable {F : Type*} [Field F]

lemma norm_inverse (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x^2) (x : F) :
    σ (x * σ x) / (x * σ x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hs : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  rw [map_mul, hσ]
  field_simp

lemma norm_injective (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x^2) :
    Function.Injective (fun x : F => x * σ x) := by
  intro x y h
  have := congrArg (fun z : F => σ z / z) h
  simpa only [norm_inverse σ hσ] using this

variable [CharP F 2]

/-- A nonempty coordinate set closed under the Suzuki root multiplication.
Inverse closure will follow from the fourth-power identity. -/
structure Closed (σ : F →+* F) where
  points : Set (F × F)
  zero_mem : (0, 0) ∈ points
  mul_mem : ∀ {a b c d}, (a,b) ∈ points → (c,d) ∈ points →
    (a+c, b+d+a*σ c) ∈ points

namespace Closed
variable {σ : F →+* F} (S : Closed σ)

lemma square_mem {a b : F} (h : (a,b) ∈ S.points) :
    (0,a*σ a) ∈ S.points := by
  simpa only [CharTwo.add_self_eq_zero, zero_add] using S.mul_mem h h

lemma inverse_mem {a b : F} (h : (a,b) ∈ S.points) :
    (a,b+a*σ a) ∈ S.points := by
  simpa using S.mul_mem h (S.square_mem h)

def projection : AddSubgroup F where
  carrier := {a | ∃ b, (a,b) ∈ S.points}
  zero_mem' := ⟨0,S.zero_mem⟩
  add_mem' := by
    rintro a c ⟨b,hb⟩ ⟨d,hd⟩
    exact ⟨b+d+a*σ c,S.mul_mem hb hd⟩
  neg_mem' := by
    intro a ha
    simpa only [CharTwo.neg_eq] using ha

def center : AddSubgroup F where
  carrier := {b | (0,b) ∈ S.points}
  zero_mem' := S.zero_mem
  add_mem' := by
    intro b d hb hd
    simpa using S.mul_mem hb hd
  neg_mem' := by
    intro b hb
    simpa only [CharTwo.neg_eq] using hb

lemma mem_projection {a : F} : a ∈ S.projection ↔ ∃ b, (a,b) ∈ S.points := Iff.rfl
lemma mem_center {b : F} : b ∈ S.center ↔ (0,b) ∈ S.points := Iff.rfl

lemma translate_mem {a b d : F} (h : (a,b) ∈ S.points) (hd : d ∈ S.center) :
    (a,b+d) ∈ S.points := by
  simpa using S.mul_mem h hd

lemma difference_mem {a b d : F} (hb : (a,b) ∈ S.points) (hd : (a,d) ∈ S.points) :
    b+d ∈ S.center := by
  have h := S.mul_mem hb (S.inverse_mem hd)
  have he : b+(d+a*σ a)+a*σ a = b+d := by
    calc
      _ = b+d+(a*σ a+a*σ a) := by abel
      _ = b+d := by rw [CharTwo.add_self_eq_zero, add_zero]
  simpa only [CharTwo.add_self_eq_zero, he] using h

noncomputable def liftCoord (a : S.projection) : F := Classical.choose a.property

lemma liftCoord_mem (a : S.projection) : (a.val,S.liftCoord a) ∈ S.points :=
  Classical.choose_spec a.property

/-- Every first-coordinate fiber is a coset of the central intersection. -/
noncomputable def fiberEquiv : S.points ≃ S.projection × S.center where
  toFun x :=
    let a : S.projection := ⟨x.val.1,x.val.2,x.property⟩
    (a,⟨x.val.2+S.liftCoord a, S.difference_mem x.property (S.liftCoord_mem a)⟩)
  invFun y := ⟨(y.1.val, S.liftCoord y.1+y.2.val),
    S.translate_mem (S.liftCoord_mem y.1) y.2.property⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    congr 1
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  right_inv y := by
    obtain ⟨a,b⟩ := y
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

/-- Squaring injects the projection into the central intersection. -/
noncomputable def normEmbedding (hσ : ∀ x, σ (σ x) = x^2) :
    S.projection ↪ S.center where
  toFun a := ⟨a.val*σ a.val, S.square_mem (S.liftCoord_mem a)⟩
  inj' := by
    intro a b h
    exact Subtype.ext (norm_injective σ hσ (congrArg Subtype.val h))

lemma card_eq_product : Nat.card S.points = Nat.card S.projection * Nat.card S.center := by
  rw [Nat.card_congr S.fiberEquiv, Nat.card_prod]

lemma projection_card_le_center [Finite F] (hσ : ∀ x, σ (σ x) = x^2) :
    Nat.card S.projection ≤ Nat.card S.center :=
  Nat.card_le_card_of_injective (S.normEmbedding hσ) (S.normEmbedding hσ).injective

lemma projection_card_sq_le [Finite F] (hσ : ∀ x, σ (σ x) = x^2) :
    Nat.card S.projection ^ 2 ≤ Nat.card S.points := by
  rw [S.card_eq_product, pow_two]
  exact Nat.mul_le_mul_left _ (S.projection_card_le_center hσ)

/-- In particular, every 32-element closed root-coordinate set has at most
four first coordinates. This justifies restricting the finite classification
to binary projection dimensions zero, one and two. -/
theorem projection_card_le_four [Finite F] (hσ : ∀ x, σ (σ x) = x^2)
    (hcard : Nat.card S.points = 32) : Nat.card S.projection ≤ 4 := by
  have hs := S.projection_card_sq_le hσ
  rw [hcard] at hs
  have hle : Nat.card S.projection ≤ 5 := by nlinarith
  have hprod := S.card_eq_product
  rw [hcard] at hprod
  by_contra h
  have he : Nat.card S.projection = 5 := by omega
  rw [he] at hprod
  omega

end Closed
end Erdos713SuzukiRootCoordinates
