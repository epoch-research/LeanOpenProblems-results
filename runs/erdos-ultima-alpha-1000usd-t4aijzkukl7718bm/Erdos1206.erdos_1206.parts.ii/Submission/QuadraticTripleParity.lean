import FormalConjecturesUtil

/-! A uniform 2-adic sieve for a rationally parametrized family of quadratic
three-representation identities. No completeness of this family, and no
statement about arbitrary cubic odd cycles, is asserted. -/

namespace Erdos1206.QuadraticTripleParity
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Three pairs of binary quadratic forms have a common sum of cubes.
Signs of individual forms are unrestricted. -/
def forms {K : Type*} [CommRing K] (p q u v : K) : Fin 6 → K := ![
  q*((p^3-q^3)*u^2-6*p^3*u*v-3*(p^3+q^3)*v^2),
  p*((p^3-q^3)*u^2+6*q^3*u*v+3*(p^3+q^3)*v^2),
  q*((p^3-q^3)*u^2+6*p^3*u*v-3*(p^3+q^3)*v^2),
  p*((p^3-q^3)*u^2-6*q^3*u*v+3*(p^3+q^3)*v^2),
  p*((p^3+2*q^3)*u^2+3*(p^3-2*q^3)*v^2),
  q*(-(2*p^3+q^3)*u^2+3*(2*p^3-q^3)*v^2)]

lemma identities {K : Type*} [CommRing K] (p q u v : K) :
    forms p q u v 0 ^ 3 + forms p q u v 1 ^ 3 =
      forms p q u v 2 ^ 3 + forms p q u v 3 ^ 3 ∧
    forms p q u v 0 ^ 3 + forms p q u v 1 ^ 3 =
      forms p q u v 4 ^ 3 + forms p q u v 5 ^ 3 := by
  constructor <;> dsimp [forms] <;> ring

/-- Truncated 2-adic valuation: 0, 1, 2, or at least 3. -/
def class8 (z : ZMod 8) : ℕ :=
  if z.val%2=1 then 0 else if z.val%4=2 then 1 else if z.val=4 then 2 else 3

def odd8 (z : ZMod 8) : Prop := z.val%2=1
instance (z : ZMod 8) : Decidable (odd8 z) := inferInstanceAs (Decidable (z.val%2=1))

/-- Exhaustive local calculation over only 8^4 residue quadruples. -/
lemma residue_classes_not_constant : ∀ p q u v : ZMod 8,
    (odd8 p ∨ odd8 q) → (odd8 u ∨ odd8 v) →
    ¬ ∀ i : Fin 6, class8 (forms p q u v i) = class8 (forms p q u v 0) := by
  decide +kernel

lemma class8_mul_odd : ∀ g z : ZMod 8, odd8 z → class8 (g*z) = class8 g := by
  decide +kernel

lemma odd8_two_mul_add_one : ∀ z : ZMod 8, odd8 (2*z+1) := by
  decide +kernel

lemma odd8_intCast {z : ℤ} (hz : Odd z) : odd8 (z : ZMod 8) := by
  obtain ⟨k,hk⟩ := hz
  rw [hk]
  push_cast
  exact odd8_two_mul_add_one (k : ZMod 8)

lemma cast_forms (p q u v : ℤ) (i : Fin 6) :
    ((forms p q u v i : ℤ) : ZMod 8) =
      forms (p : ZMod 8) (q : ZMod 8) (u : ZMod 8) (v : ZMod 8) i := by
  fin_cases i <;> simp [forms]

/-- After division by any common integral scalar, not all six coordinates
can be odd, provided neither parameter pair is simultaneously even. -/
theorem not_all_odd_after_common_division (p q u v g : ℤ) (z : Fin 6 → ℤ)
    (hpq : Odd p ∨ Odd q) (huv : Odd u ∨ Odd v)
    (h : ∀ i, forms p q u v i = g*z i) : ¬ ∀ i, Odd (z i) := by
  intro hz
  have hpq8 : odd8 (p : ZMod 8) ∨ odd8 (q : ZMod 8) := hpq.imp odd8_intCast odd8_intCast
  have huv8 : odd8 (u : ZMod 8) ∨ odd8 (v : ZMod 8) := huv.imp odd8_intCast odd8_intCast
  apply residue_classes_not_constant (p : ZMod 8) q u v hpq8 huv8
  have hc (i : Fin 6) :
      class8 (forms (p : ZMod 8) (q : ZMod 8) (u : ZMod 8) (v : ZMod 8) i) =
        class8 (g : ZMod 8) := by
    rw [← cast_forms, h i, Int.cast_mul]
    exact class8_mul_odd (g : ZMod 8) (z i : ZMod 8) (odd8_intCast (hz i))
  intro i
  exact (hc i).trans (hc 0).symm

/-- Thus the divisor 2 meets every such normalized six-root configuration.
This does not classify all quadratic families or all odd cycles. -/
theorem even_coordinate_after_common_division (p q u v g : ℤ) (z : Fin 6 → ℤ)
    (hpq : Odd p ∨ Odd q) (huv : Odd u ∨ Odd v)
    (h : ∀ i, forms p q u v i = g*z i) : ∃ i, Even (z i) := by
  by_contra! hn
  apply not_all_odd_after_common_division p q u v g z hpq huv h
  intro i
  exact Int.not_even_iff_odd.mp (hn i)

#print axioms identities
#print axioms residue_classes_not_constant
#print axioms even_coordinate_after_common_division
end Erdos1206.QuadraticTripleParity
