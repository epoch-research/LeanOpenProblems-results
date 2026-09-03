import FormalConjecturesUtil

/-! A polynomial-size finite cyclic carrier for Sidon slope labels. This is
an ordinary Sidon construction, not a Sidon subset of square values. -/
namespace Erdos773.PolynomialSidonSlopes
open Finset
set_option maxHeartbeats 2000000
noncomputable section

def value (D : ℕ) (i : Fin D) : ℕ := i.val+(2*D+1)*i.val^2
def height (D : ℕ) : ℕ := 3*(D+1)^3

def seed (D p : ℕ) : Finset (ZMod p) := univ.image (fun i : Fin D => (value D i : ZMod p))

lemma value_lt (D : ℕ) (i : Fin D) : value D i<height D := by
  have hi := i.isLt
  have hi2 := Nat.pow_le_pow_left hi.le 2
  have hm := Nat.mul_le_mul_left (2*D+1) hi2
  unfold value height
  nlinarith only [hm,hi]

lemma value_mod (D : ℕ) (i : Fin D) : value D i%(2*D+1)=i.val := by
  have hi : i.val<2*D+1 := by have hh := i.isLt; omega
  simp [value,Nat.add_mod,Nat.mod_eq_of_lt hi]

lemma value_injective (D : ℕ) : Function.Injective (value D) := by
  intro i j hij
  apply Fin.ext
  have hh := congrArg (fun n => n%(2*D+1)) hij
  simpa only [value_mod] using hh

lemma sum_sq_matching (a b c d : ℕ) (hs : a+b=c+d) (hq : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hsZ : (a:ℤ)+b=c+d := by exact_mod_cast hs
  have hqZ : (a:ℤ)^2+b^2=c^2+d^2 := by exact_mod_cast hq
  have hp : (a:ℤ)*b=c*d := by
    have hh := congrArg (fun z : ℤ => z^2) hsZ
    nlinarith only [hh,hqZ]
  have hf : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by
    linear_combination (a:ℤ)*hsZ-hp
  rcases mul_eq_zero.mp hf with h | h
  · left
    have hh : a=c := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh,by omega⟩
  · right
    have hh : a=d := by exact_mod_cast sub_eq_zero.mp h
    exact ⟨hh,by omega⟩

lemma value_pair_matching (D : ℕ) (a b c d : Fin D)
    (he : value D a+value D b=value D c+value D d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have hab : a.val+b.val<2*D+1 := by have ha := a.isLt; have hb := b.isLt; omega
  have hcd : c.val+d.val<2*D+1 := by have hc := c.isLt; have hd := d.isLt; omega
  have he' : a.val+b.val+(2*D+1)*(a.val^2+b.val^2)=
      c.val+d.val+(2*D+1)*(c.val^2+d.val^2) := by
    dsimp only [value] at he
    nlinarith only [he]
  have hs := congrArg (fun n => n%(2*D+1)) he'
  simp only [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hab,
    Nat.mod_eq_of_lt hcd] at hs
  have hm : (2*D+1)*(a.val^2+b.val^2)=(2*D+1)*(c.val^2+d.val^2) := by omega
  have hq := Nat.eq_of_mul_eq_mul_left (by omega : 0<2*D+1) hm
  rcases sum_sq_matching a b c d hs hq with h | h
  · exact Or.inl ⟨Fin.ext h.1,Fin.ext h.2⟩
  · exact Or.inr ⟨Fin.ext h.1,Fin.ext h.2⟩

lemma cast_injective (D p : ℕ) (hp : 2*height D<p) :
    Function.Injective (fun i : Fin D => (value D i:ZMod p)) := by
  intro i j hij
  apply value_injective D
  have hi : value D i<p := (value_lt D i).trans (by omega)
  have hj : value D j<p := (value_lt D j).trans (by omega)
  have hh := (ZMod.natCast_eq_natCast_iff' (value D i) (value D j) p).mp hij
  simpa only [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hh

lemma seed_card (D p : ℕ) (hp : 2*height D<p) : (seed D p).card=D := by
  rw [seed,card_image_of_injective _ (cast_injective D p hp)]
  simp

lemma seed_sidon (D p : ℕ) (hp : 2*height D<p) : IsSidon (seed D p : Set (ZMod p)) := by
  intro a ha b hb c hc d hd he
  simp only [seed,Finset.mem_coe] at ha hb hc hd
  obtain ⟨i,_,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := mem_image.mp hb
  obtain ⟨k,_,rfl⟩ := mem_image.mp hc
  obtain ⟨l,_,rfl⟩ := mem_image.mp hd
  have hik : value D i+value D k<p := by have hi := value_lt D i; have hk := value_lt D k; omega
  have hjl : value D j+value D l<p := by have hj := value_lt D j; have hl := value_lt D l; omega
  have he' : ((value D i+value D k:ℕ):ZMod p)=((value D j+value D l:ℕ):ZMod p) := by
    push_cast
    exact he
  have hh := (ZMod.natCast_eq_natCast_iff' _ _ p).mp he'
  rw [Nat.mod_eq_of_lt hik,Nat.mod_eq_of_lt hjl] at hh
  rcases value_pair_matching D i k j l hh with h | h
  · left; simp only [h.1,h.2,and_self]
  · right; simp only [h.1,h.2,and_self]

/-- Distinct equal directed differences of Sidon labels determine their
ordered endpoints. No multiplicative or square-Sidon property is asserted. -/
lemma difference_unique {G : Type*} [AddCommGroup G] {T : Set G} (hT : IsSidon T)
    {a b c d : G} (ha : a∈T) (hb : b∈T) (hc : c∈T) (hd : d∈T)
    (hab : a≠b) (he : a-b=c-d) : a=c ∧ b=d := by
  have hs : a+d=c+b := sub_eq_sub_iff_add_eq_add.mp he
  rcases hT a ha c hc d hd b hb hs with h | h
  · exact ⟨h.1,h.2.symm⟩
  · exact False.elim (hab h.1)

#print axioms seed_card
#print axioms seed_sidon
#print axioms difference_unique
end
end Erdos773.PolynomialSidonSlopes
