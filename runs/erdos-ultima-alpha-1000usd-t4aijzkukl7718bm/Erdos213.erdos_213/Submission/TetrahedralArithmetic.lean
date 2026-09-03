import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic

/-!
Arithmetic constraints for a tetrahedral spherical-orbit construction.
These results do not assert a general-position rational parameter and do not
settle Erdős 213.
-/
namespace Erdos213.TetrahedralArithmetic

/-- Primitive integral coordinates, in a form convenient for divisibility. -/
def Primitive (a b c : ℤ) : Prop := ∃ r s t : ℤ, r*a+s*b+t*c = 1

def crossZero {R : Type*} [CommRing R] (a b c : R) : R :=
  2*(a^2+b^2+c^2-a*b-a*c-b*c)

set_option synthInstance.maxSize 10000 in
private lemma mod_four_obstruction : ∀ a b c : ZMod 4,
    IsSquare (a^2+b^2) → IsSquare (a^2+c^2) → IsSquare (b^2+c^2) →
    IsSquare (crossZero a b c) →
      a.val%2=0 ∧ b.val%2=0 ∧ c.val%2=0 := by
  change ∀ a b c : ZMod 4, (∃ r, a^2+b^2 = r*r) →
    (∃ r, a^2+c^2 = r*r) → (∃ r, b^2+c^2 = r*r) →
    (∃ r, crossZero a b c = r*r) →
    a.val%2=0 ∧ b.val%2=0 ∧ c.val%2=0
  decide

lemma integer_squareclass_one_even {a b c : ℤ}
    (hab : IsSquare (a^2+b^2)) (hac : IsSquare (a^2+c^2))
    (hbc : IsSquare (b^2+c^2)) (hc : IsSquare (crossZero a b c)) :
    (2 : ℤ) ∣ a ∧ (2 : ℤ) ∣ b ∧ (2 : ℤ) ∣ c := by
  have h₁ : IsSquare ((a : ZMod 4)^2+(b : ZMod 4)^2) := by
    simpa using hab.map (Int.castRingHom (ZMod 4))
  have h₂ : IsSquare ((a : ZMod 4)^2+(c : ZMod 4)^2) := by
    simpa using hac.map (Int.castRingHom (ZMod 4))
  have h₃ : IsSquare ((b : ZMod 4)^2+(c : ZMod 4)^2) := by
    simpa using hbc.map (Int.castRingHom (ZMod 4))
  have h₄ : IsSquare (crossZero (a : ZMod 4) (b : ZMod 4) (c : ZMod 4)) := by
    simpa [crossZero] using hc.map (Int.castRingHom (ZMod 4))
  obtain ⟨ha,hb,hc⟩ := mod_four_obstruction _ _ _ h₁ h₂ h₃ h₄
  have cast_div : ∀ z : ℤ, (z : ZMod 4).val%2 = 0 → (2 : ℤ) ∣ z := by
    intro z hz
    have hh : (((z : ZMod 4).val : ℤ)%2) = 0 := by exact_mod_cast hz
    rw [ZMod.val_intCast] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [Int.emod_emod_of_dvd _ (by norm_num : (2 : ℤ) ∣ 4)] at hh
    exact Int.dvd_of_emod_eq_zero hh
  exact ⟨cast_div a ha,cast_div b hb,cast_div c hc⟩

lemma primitive_not_squareclass_one {a b c : ℤ} (hp : Primitive a b c)
    (hab : IsSquare (a^2+b^2)) (hac : IsSquare (a^2+c^2))
    (hbc : IsSquare (b^2+c^2)) : ¬ IsSquare (crossZero a b c) := by
  intro hc
  obtain ⟨ha,hb,hc⟩ := integer_squareclass_one_even hab hac hbc hc
  obtain ⟨r,s,t,hp⟩ := hp
  have hdiv : (2 : ℤ) ∣ 1 := by
    rw [← hp]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right ha r) (dvd_mul_of_dvd_right hb s))
      (dvd_mul_of_dvd_right hc t)
  norm_num at hdiv

lemma common_face_squareclass_dvd_two {D : ℕ} (hD : Squarefree D)
    {a b c : ℤ} (hp : Primitive a b c)
    (hab : (D : ℤ) ∣ a^2+b^2) (hac : (D : ℤ) ∣ a^2+c^2)
    (hbc : (D : ℤ) ∣ b^2+c^2) : D ∣ 2 := by
  have hDi : Squarefree (D : ℤ) := Int.squarefree_natCast.mpr hD
  have ha : (D : ℤ) ∣ 2*a^2 := by
    convert dvd_sub (dvd_add hab hac) hbc using 1 <;> ring
  have hb : (D : ℤ) ∣ 2*b^2 := by
    convert dvd_sub (dvd_add hab hbc) hac using 1 <;> ring
  have hc : (D : ℤ) ∣ 2*c^2 := by
    convert dvd_sub (dvd_add hac hbc) hab using 1 <;> ring
  have sq_cancel : ∀ x : ℤ, (D : ℤ) ∣ 2*x^2 → (D : ℤ) ∣ 2*x := by
    intro x hx
    apply (hDi.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp
    convert dvd_mul_of_dvd_right hx 2 using 1 <;> ring
  obtain ⟨r,s,t,hp⟩ := hp
  have hdiv : (D : ℤ) ∣ 2 := by
    have hd := dvd_add
      (dvd_add (dvd_mul_of_dvd_right (sq_cancel a ha) r)
        (dvd_mul_of_dvd_right (sq_cancel b hb) s))
      (dvd_mul_of_dvd_right (sq_cancel c hc) t)
    convert hd using 1
    linear_combination -2*hp
  exact_mod_cast hdiv

/-- The same divisibility bound still holds when some face forms occur
with an extra factor of two. This is useful for the full signed-permutation
orbit; it does not assert any arithmetic parameter. -/
lemma common_doubled_face_squareclass_dvd_two {D : ℕ} (hD : Squarefree D)
    {a b c : ℤ} (hp : Primitive a b c)
    (hab : (D : ℤ) ∣ 2*(a^2+b^2)) (hac : (D : ℤ) ∣ 2*(a^2+c^2))
    (hbc : (D : ℤ) ∣ 2*(b^2+c^2)) : D ∣ 2 := by
  have hDi : Squarefree (D : ℤ) := Int.squarefree_natCast.mpr hD
  have ha : (D : ℤ) ∣ (2*a)^2 := by
    convert dvd_sub (dvd_add hab hac) hbc using 1 <;> ring
  have hb : (D : ℤ) ∣ (2*b)^2 := by
    convert dvd_sub (dvd_add hab hbc) hac using 1 <;> ring
  have hc : (D : ℤ) ∣ (2*c)^2 := by
    convert dvd_sub (dvd_add hac hbc) hab using 1 <;> ring
  have cancel : ∀ x : ℤ, (D : ℤ) ∣ x^2 → (D : ℤ) ∣ x := fun _ hx =>
    (hDi.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hx
  obtain ⟨r,s,t,hp⟩ := hp
  have hdiv : (D : ℤ) ∣ 2 := by
    have hd := dvd_add
      (dvd_add (dvd_mul_of_dvd_right (cancel _ ha) r)
        (dvd_mul_of_dvd_right (cancel _ hb) s))
      (dvd_mul_of_dvd_right (cancel _ hc) t)
    convert hd using 1
    linear_combination -2*hp
  exact_mod_cast hdiv

lemma squareclass_conflict {q : ℚ} (hq : q ≠ 0)
    (hs : IsSquare q) : ¬ IsSquare (2*q) := by
  intro ht
  have htwo : IsSquare (2 : ℚ) := by
    simpa [hq] using ht.div hs
  exact Nat.prime_two.not_isSquare (Rat.isSquare_natCast_iff.mp htwo)

/-- The three face forms and just one cross form already force common
square class 2 for a primitive integral tetrahedral-orbit parameter. -/
lemma common_squareclass_eq_two {D : ℕ} (hD : Squarefree D)
    {a b c : ℤ} (hp : Primitive a b c)
    (hab : ∃ r : ℤ, a^2+b^2 = (D : ℤ)*r^2)
    (hac : ∃ r : ℤ, a^2+c^2 = (D : ℤ)*r^2)
    (hbc : ∃ r : ℤ, b^2+c^2 = (D : ℤ)*r^2)
    (hcross : ∃ r : ℤ, crossZero a b c = (D : ℤ)*r^2) : D = 2 := by
  have hd : D ∣ 2 := common_face_squareclass_dvd_two hD hp
    (by obtain ⟨r,hr⟩ := hab; exact ⟨r^2,hr⟩)
    (by obtain ⟨r,hr⟩ := hac; exact ⟨r^2,hr⟩)
    (by obtain ⟨r,hr⟩ := hbc; exact ⟨r^2,hr⟩)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with rfl | h
  · exfalso
    apply primitive_not_squareclass_one hp
    · obtain ⟨r,hr⟩ := hab
      exact ⟨r,by simpa [pow_two] using hr⟩
    · obtain ⟨r,hr⟩ := hac
      exact ⟨r,by simpa [pow_two] using hr⟩
    · obtain ⟨r,hr⟩ := hbc
      exact ⟨r,by simpa [pow_two] using hr⟩
    · obtain ⟨r,hr⟩ := hcross
      exact ⟨r,by simpa [pow_two] using hr⟩
  · exact h

#print axioms common_doubled_face_squareclass_dvd_two
#print axioms squareclass_conflict
#print axioms integer_squareclass_one_even
#print axioms common_squareclass_eq_two
end Erdos213.TetrahedralArithmetic
