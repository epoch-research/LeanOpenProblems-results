import FormalConjecturesUtil

/-!
A ring-theoretic construction of Sidon squares. Integer evaluation need not preserve it.
This is an auxiliary result, not a proof of Erdős 773.
-/

namespace Erdos773

section Reduction

variable {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [CommRing S] [IsDomain S] [CharP S 2]

lemma square_collision_reduction_mod_two (f : R →+* S)
    (hker : ∀ x : R, f x = 0 → ∃ t : R, x = 2 * t)
    {a b c d : R} (he : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    (f a = f c ∧ f b = f d) ∨ (f a = f d ∧ f b = f c) := by
  have hm : (f a) ^ 2 + (f b) ^ 2 = (f c) ^ 2 + (f d) ^ 2 := by
    simpa only [map_add, map_pow] using congrArg f he
  have hs : f a + f b = f c + f d := by
    apply frobenius_inj S 2
    change (f a + f b) ^ 2 = (f c + f d) ^ 2
    simpa only [CharTwo.add_sq] using hm
  have hz : f (a + b - (c + d)) = 0 := by
    simp only [map_sub, map_add, hs, sub_self]
  obtain ⟨t, ht⟩ := hker _ hz
  have hsR : a + b = c + d + 2 * t := by
    linear_combination ht
  have hpR : a * b - c * d = 2 * t * (c + d + t) := by
    apply mul_left_cancel₀ (show (2 : R) ≠ 0 by norm_num)
    calc
      2 * (a * b - c * d) = (a + b) ^ 2 - (c + d) ^ 2 := by
        linear_combination -he
      _ = (c + d + 2 * t) ^ 2 - (c + d) ^ 2 := by rw [hsR]
      _ = 2 * (2 * t * (c + d + t)) := by ring
  have hp : f a * f b = f c * f d := by
    have h := congrArg f hpR
    simpa only [map_sub, map_mul, map_add, map_ofNat, CharTwo.two_eq_zero,
      zero_mul, sub_eq_zero] using h
  have hfac : (f a - f c) * (f a - f d) = 0 := by
    calc
      _ = (f a) ^ 2 - f a * (f c + f d) + f c * f d := by ring
      _ = (f a) ^ 2 - f a * (f a + f b) + f a * f b := by rw [← hs, ← hp]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfac with h | h
  · have hac := sub_eq_zero.mp h
    left
    refine ⟨hac, ?_⟩
    rw [hac] at hs
    exact add_left_cancel hs
  · have had := sub_eq_zero.mp h
    right
    refine ⟨had, ?_⟩
    rw [had] at hs
    linear_combination hs

lemma sidon_squares_of_injective_reduction (f : R →+* S)
    (hker : ∀ x : R, f x = 0 → ∃ t : R, x = 2 * t)
    (A : Set R) (hinj : A.InjOn f) :
    IsSidon ((fun x : R => x ^ 2) '' A) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ he
  rcases square_collision_reduction_mod_two f hker he with h | h
  · left
    exact ⟨congrArg (fun x : R => x ^ 2) (hinj ha hc h.1),
      congrArg (fun x : R => x ^ 2) (hinj hb hd h.2)⟩
  · right
    exact ⟨congrArg (fun x : R => x ^ 2) (hinj ha hd h.1),
      congrArg (fun x : R => x ^ 2) (hinj hb hc h.2)⟩

end Reduction

open Polynomial

def binaryPolynomials : Set (Polynomial ℤ) :=
  {P | ∀ n, P.coeff n = 0 ∨ P.coeff n = 1}

lemma binary_polynomial_squares_sidon :
    IsSidon ((fun P : Polynomial ℤ => P ^ 2) '' binaryPolynomials) := by
  let f : Polynomial ℤ →+* Polynomial (ZMod 2) :=
    Polynomial.mapRingHom (Int.castRingHom (ZMod 2))
  apply sidon_squares_of_injective_reduction f
  · intro P hP
    have hd : Polynomial.C (2 : ℤ) ∣ P := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff n) 2).mp
      have hc := congrArg (fun Q : Polynomial (ZMod 2) => Q.coeff n) hP
      simpa [f] using hc
    simpa using hd
  · intro P hP Q hQ he
    ext n
    have hc : (P.coeff n : ZMod 2) = (Q.coeff n : ZMod 2) := by
      simpa [f] using congrArg (fun T : Polynomial (ZMod 2) => T.coeff n) he
    rcases hP n with hp | hp <;> rcases hQ n with hq | hq <;> simp_all [hp, hq]

#print axioms binary_polynomial_squares_sidon

end Erdos773
