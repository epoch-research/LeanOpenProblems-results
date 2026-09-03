import Submission.OuterCarryProfileExplore

/-! A rectangular radix equivalence and its exact subtraction carry. This
allows a low modulus and a different high modulus; it is not an infinite
integer construction. -/
namespace Erdos66RectangularRadix
open Erdos66CyclicThickening Erdos66OuterCarryProfile
open scoped Classical

variable (p Q : ℕ) [NeZero p] [NeZero Q]

def encode (z : ZMod p × ZMod Q) : ZMod (p*Q) :=
  ((z.1.val+p*z.2.val : ℕ) : ZMod (p*Q))

lemma encode_lt (z : ZMod p × ZMod Q) : z.1.val+p*z.2.val < p*Q := by
  have hx := ZMod.val_lt z.1
  have hy := ZMod.val_lt z.2
  have hp := NeZero.pos p
  nlinarith

lemma encode_val (z : ZMod p × ZMod Q) :
    (encode p Q z).val=z.1.val+p*z.2.val := ZMod.val_natCast_of_lt (encode_lt p Q z)

lemma encode_injective : Function.Injective (encode p Q) := by
  intro z w h
  have hv := congrArg ZMod.val h
  rw [encode_val, encode_val] at hv
  have hx := congrArg (· % p) hv
  have hy := congrArg (· / p) hv
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)] at hx
  simp only [Nat.add_mul_div_left _ _ (NeZero.pos p),
    Nat.div_eq_of_lt (ZMod.val_lt _), zero_add] at hy
  exact Prod.ext (ZMod.val_injective p hx) (ZMod.val_injective Q hy)

noncomputable def radixEquiv : (ZMod p × ZMod Q) ≃ ZMod (p*Q) :=
  Equiv.ofBijective (encode p Q)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨encode_injective p Q, by simp⟩)

lemma mul_cast_eq (x y : ℕ) (h : (x:ZMod Q)=(y:ZMod Q)) :
    (p:ZMod (p*Q))*x=p*y := by
  rw [←Nat.cast_mul, ←Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  have hh := (ZMod.natCast_eq_natCast_iff x y Q).mp h
  exact hh.mul_left' p

lemma encode_sub (t x : ZMod p) (s y : ZMod Q) :
    encode p Q (t,s)-encode p Q (x,y) =
      encode p Q (t-x,s-y-(borrow p t x:ZMod Q)) := by
  apply sub_eq_iff_eq_add.mpr
  let c := borrow p t x
  let v := s-y-(c:ZMod Q)
  have hl := Erdos66CyclicThickening.low_sub_val p t x
  have hh : (((v.val+y.val+c:ℕ):ZMod Q))=(s.val:ZMod Q) := by
    simp only [Nat.cast_add, ZMod.natCast_zmod_val, v]
    ring
  have hm := mul_cast_eq p Q _ _ hh
  have hl' : (((t-x).val+x.val:ℕ):ZMod (p*Q)) =
      ((t.val+p*c:ℕ):ZMod (p*Q)) := by rw [hl]
  dsimp only [encode, Prod.fst, Prod.snd]
  push_cast
  change (t.val+p*s.val:ZMod (p*Q)) =
    ((t-x).val+p*v.val)+(x.val+p*y.val)
  push_cast at hm hl'
  linear_combination -hl'-hm

noncomputable def radixSet (B : Finset (ZMod p × ZMod Q)) : Finset (ZMod (p*Q)) :=
  B.image (encode p Q)

lemma mem_radixSet (B : Finset (ZMod p × ZMod Q)) (z : ZMod p × ZMod Q) :
    encode p Q z∈radixSet p Q B ↔ z∈B := by
  simp only [radixSet, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, he⟩
    exact encode_injective p Q he ▸ hw
  · exact fun hz ↦ ⟨z,hz,rfl⟩

lemma radixSet_card (B : Finset (ZMod p × ZMod Q)) :
    (radixSet p Q B).card=B.card :=
  Finset.card_image_of_injective _ (encode_injective p Q)

/-- Exact mixed count, retaining the carry from the lower digit. -/
lemma mixed_count_formula (B C : Finset (ZMod p × ZMod Q)) (t : ZMod p) (s : ZMod Q) :
    cyclicCount (p*Q) (radixSet p Q B) (radixSet p Q C) (encode p Q (t,s)) =
      ∑ x : ZMod p, ∑ y : ZMod Q,
        if (x,y)∈B ∧ (t-x,s-y-(borrow p t x:ZMod Q))∈C then 1 else 0 := by
  rw [cyclicCount_sum, ←Equiv.sum_comp (radixEquiv p Q), Fintype.sum_prod_type]
  simp only [radixEquiv, Equiv.ofBijective_apply, encode_sub, mem_radixSet]

lemma encode_nat (n : ℕ) :
    encode p Q ((n:ZMod p),(n/p:ZMod Q))=(n:ZMod (p*Q)) := by
  have hm := mul_cast_eq p Q ((n/p)%Q) (n/p) (ZMod.natCast_mod (n/p) Q)
  simp only [encode, ZMod.val_natCast, Nat.cast_add, Nat.cast_mul]
  rw [hm, ←Nat.cast_mul, ←Nat.cast_add, Nat.mod_add_div]

lemma radixSet_univ : radixSet p Q Finset.univ=Finset.univ := by
  ext z
  obtain ⟨w, rfl⟩ := (radixEquiv p Q).surjective z
  change encode p Q w∈radixSet p Q Finset.univ ↔ _
  simp only [mem_radixSet, Finset.mem_univ]

end Erdos66RectangularRadix
