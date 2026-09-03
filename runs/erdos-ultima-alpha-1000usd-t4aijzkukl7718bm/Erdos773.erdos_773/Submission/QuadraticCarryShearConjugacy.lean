import Submission.QuadraticCarryParabola

/-!
Quadratic shears of the carry-aware construction are conjugate by multiplication
by a unit congruent to one modulo p. This is a modular identity, not a small-height
estimate or a settlement of Erdos 773.
-/
namespace Erdos773.QuadraticCarryShearConjugacy
open QuadraticCarryParabola
set_option maxHeartbeats 1000000
noncomputable section

/-- Multiplication by this factor is invertible modulo p squared. -/
theorem multiplier_unit (p t : ℕ) :
    IsCoprime (1 + p*t : ℤ) (p^2 : ℤ) := by
  have h : IsCoprime (1 + p*t : ℤ) (p : ℤ) := by
    refine ⟨1, -(t:ℤ), ?_⟩
    ring
  exact h.pow_right

/-- The target values transform by the square of the principal unit. -/
theorem target_shear (p t b : ℕ) [Fact p.Prime] (kap lam mu : ZMod p) :
    target p (kap+2*t) lam mu b ≡
      (1+p*t)^2 * target p kap lam mu b [MOD p^2] := by
  have hd : digit p (kap+2*t) lam mu b ≡
      digit p kap lam mu b+2*t*(b^2%p) [MOD p] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp only [digit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_zmod_val, ZMod.natCast_mod, Nat.cast_pow]
    ring
  have hs := (hd.mul_left' p).add_left (b^2%p)
  change target p (kap+2*t) lam mu b ≡
    b^2%p+p*(digit p kap lam mu b+2*t*(b^2%p)) [MOD p*p] at hs
  have he : (1+p*t)^2 * target p kap lam mu b =
      b^2%p+p*(digit p kap lam mu b+2*t*(b^2%p))+
      (t^2*(b^2%p)+2*t*digit p kap lam mu b+p*t^2*digit p kap lam mu b)*p^2 := by
    unfold target
    ring
  rw [he]
  simpa only [pow_two, Nat.modEq_add_mul_modulus_iff] using hs

/-- The high digit undergoes a linear shear. -/
theorem highDigit_shear (p t b : ℕ) [Fact p.Prime]
    (kap lam mu : ZMod p) (h2 : (2:ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    highDigit p (kap+2*t) lam mu b = (highDigit p kap lam mu b+t*b)%p := by
  have hb0 : (b:ZMod p) ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hbp, ZMod.val_zero] at hh
    omega
  have hd : ((kap+2*(t:ZMod p))*(b:ZMod p)^2+lam*b+mu-
      ((b^2/p:ℕ):ZMod p))/(2*(b:ZMod p)) =
      (kap*(b:ZMod p)^2+lam*b+mu-((b^2/p:ℕ):ZMod p))/(2*(b:ZMod p))+
        (t:ZMod p)*b := by
    field_simp
    ring
  unfold highDigit
  rw [hd]
  rw [← ZMod.val_natCast]
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]

/-- The canonical roots are conjugate modulo p squared, without a height claim. -/
theorem root_shear (p t b : ℕ) [Fact p.Prime]
    (kap lam mu : ZMod p) (h2 : (2:ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    root p (kap+2*t) lam mu b ≡
      (1+p*t)*root p kap lam mu b [MOD p^2] := by
  have hd : highDigit p (kap+2*t) lam mu b ≡
      highDigit p kap lam mu b+t*b [MOD p] := by
    rw [highDigit_shear p t b kap lam mu h2 hb hbp]
    exact Nat.mod_mod _ _
  have hs := (hd.mul_left' p).add_left b
  change root p (kap+2*t) lam mu b ≡
    b+p*(highDigit p kap lam mu b+t*b) [MOD p*p] at hs
  have he : (1+p*t)*root p kap lam mu b =
      b+p*(highDigit p kap lam mu b+t*b)+(t*highDigit p kap lam mu b)*p^2 := by
    unfold root
    ring
  rw [he]
  simpa only [pow_two, Nat.modEq_add_mul_modulus_iff] using hs


/-- Every quadratic shear is in the principal-unit orbit of the affine target. -/
theorem exists_affine_conjugacy (p b : ℕ) [Fact p.Prime]
    (kap lam mu : ZMod p) (h2 : (2:ZMod p) ≠ 0) (hb : 0<b) (hbp : b<p) :
    ∃ t<p, kap=2*(t:ZMod p) ∧
      root p kap lam mu b ≡ (1+p*t)*root p 0 lam mu b [MOD p^2] := by
  let t : ℕ := (kap/2).val
  have ht : 0+2*(t:ZMod p)=kap := by
    dsimp [t]
    rw [ZMod.natCast_zmod_val, zero_add]
    field_simp
  refine ⟨t, ZMod.val_lt _, ?_, ?_⟩
  · simpa only [zero_add] using ht.symm
  · simpa only [ht] using root_shear p t b 0 lam mu h2 hb hbp

/-- Even a root of height one can be sent to a canonical root near p squared.
The modular conjugacy therefore does not automatically transfer a height bound. -/
theorem height_not_preserved (p : ℕ) [Fact p.Prime] (h2 : (2:ZMod p) ≠ 0) :
    root p 0 1 (-1) 1=1 ∧
      root p (2*((p-1:ℕ):ZMod p)) 1 (-1) 1=1+p*(p-1) := by
  have hp : 1<p := (Fact.out : p.Prime).one_lt
  have hd : highDigit p 0 1 (-1) 1=0 := by
    simp [highDigit, Nat.div_eq_of_lt hp]
  constructor
  · simp [root, hd]
  · have hh := highDigit_shear p (p-1) 1 0 1 (-1) h2 (by omega) hp
    have hp' : p-1<p := by omega
    simp only [zero_add, hd, mul_one, Nat.mod_eq_of_lt hp'] at hh
    simp only [root, hh]

end
end Erdos773.QuadraticCarryShearConjugacy

#print axioms Erdos773.QuadraticCarryShearConjugacy.multiplier_unit
#print axioms Erdos773.QuadraticCarryShearConjugacy.target_shear
#print axioms Erdos773.QuadraticCarryShearConjugacy.highDigit_shear
#print axioms Erdos773.QuadraticCarryShearConjugacy.root_shear
#print axioms Erdos773.QuadraticCarryShearConjugacy.exists_affine_conjugacy
#print axioms Erdos773.QuadraticCarryShearConjugacy.height_not_preserved
