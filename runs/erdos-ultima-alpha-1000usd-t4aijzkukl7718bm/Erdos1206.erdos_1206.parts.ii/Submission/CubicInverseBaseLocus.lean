import Submission.CubicInverseHeight

/-! The base locus of the quadratic inverse. This describes arithmetic
concentration of its common divisor; it does not settle the density question. -/

namespace Erdos1206.CubicBaseLocus

variable {R : Type*} [CommRing R]

def inverseNormLeft (x w : R) : R := w^2-w*x+x^2
def inverseNormRight (y z : R) : R := y^2-y*z+z^2
def inverseDet (x y z w : R) : R := w*z-x*y

lemma inverse_base_identities (x y z w : R) :
    inverseB x y z w = 2*(inverseNormLeft x w-inverseNormRight y z) ∧
    x*(inverseB x y z w-inverseA x y z w) =
      2*(x-z)*inverseNormLeft x w+(2*w-x)*inverseDet x y z w ∧
    w*(inverseB x y z w-inverseA x y z w) =
      2*(w-y)*inverseNormLeft x w+(w-2*x)*inverseDet x y z w := by
  dsimp [inverseA,inverseB,inverseNormLeft,inverseNormRight,inverseDet]
  constructor; ring
  constructor <;> ring

/-- One rational diagonal line and two conjugate lines form the base locus
of the quadratic inverse. -/
theorem inverse_common_zero_iff {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (x y z w : F) :
    (inverseA x y z w=0 ∧ inverseB x y z w=0 ∧ inverseT x y z w=0) ↔
      (x=z ∧ y=w) ∨
      (inverseDet x y z w=0 ∧ inverseNormLeft x w=0 ∧ inverseNormRight y z=0) := by
  obtain ⟨hB,hx,hw⟩ := inverse_base_identities x y z w
  constructor
  · rintro ⟨hA0,hB0,hT0⟩
    have hDet : inverseDet x y z w=0 := by
      change 3*inverseDet x y z w=0 at hT0
      exact (mul_eq_zero.mp hT0).resolve_left h3
    rw [hA0,hB0,hDet] at hx hw
    by_cases hN : inverseNormLeft x w=0
    · right
      refine ⟨hDet,hN,?_⟩
      have hh : 2*(inverseNormLeft x w-inverseNormRight y z)=0 := hB.symm.trans hB0
      have hh' := (mul_eq_zero.mp hh).resolve_left h2
      rw [hN] at hh'
      simpa using hh'
    · left
      have hx' : 2*(x-z)*inverseNormLeft x w=0 := by simpa using hx.symm
      have hw' : 2*(w-y)*inverseNormLeft x w=0 := by simpa using hw.symm
      have hxx := (mul_eq_zero.mp ((mul_eq_zero.mp hx').resolve_right hN)).resolve_left h2
      have hww := (mul_eq_zero.mp ((mul_eq_zero.mp hw').resolve_right hN)).resolve_left h2
      exact ⟨sub_eq_zero.mp hxx,(sub_eq_zero.mp hww).symm⟩
  · rintro (⟨rfl,rfl⟩ | ⟨hDet,hN,hM⟩)
    · dsimp [inverseA,inverseB,inverseT]
      constructor; ring
      constructor <;> ring
    · have hB0 : inverseB x y z w=0 := by rw [hB,hN,hM]; ring
      have hT0 : inverseT x y z w=0 := by change 3*inverseDet x y z w=0; rw [hDet]; ring
      refine ⟨?_,hB0,hT0⟩
      rw [hB0,hN,hDet] at hx hw
      by_cases hx0 : x=0
      · by_cases hw0 : w=0
        · subst x w
          dsimp [inverseA,inverseNormRight] at hM ⊢
          linear_combination -2*hM
        · have hh : w*(-inverseA x y z w)=0 := by simpa using hw
          exact neg_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hw0)
      · have hh : x*(-inverseA x y z w)=0 := by simpa using hx
        exact neg_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hx0)

private lemma inverse_norm_anisotropic {p : ℕ} (hp : p.Prime) (hp3 : p%3=2)
    {x w : ZMod p} (h : inverseNormLeft x w=0) : x=0 ∧ w=0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcube : w^3=(-x)^3 := by
    dsimp [inverseNormLeft] at h
    linear_combination (w+x)*h
  have hw : w = -x := Erdos1206.cube_injective_zmod_of_mod_three_eq_two hp hp3 hcube
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro hdiv
    have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdiv
    omega
  have hxx : 3*x^2=0 := by
    dsimp [inverseNormLeft] at h
    rw [hw] at h
    linear_combination h
  have hx : x=0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hxx).resolve_left h3)
  exact ⟨hx,by simp [hw,hx]⟩

/-- At an odd inert prime, inverse cancellation occurs only on the rational
diagonal line, not on either of the two conjugate lines. -/
theorem inverse_common_zero_inert_iff {p : ℕ} (hp : p.Prime) (hp3 : p%3=2)
    (hp2 : p ≠ 2) (x y z w : ZMod p) :
    (inverseA x y z w=0 ∧ inverseB x y z w=0 ∧ inverseT x y z w=0) ↔
      x=z ∧ y=w := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    omega
  rw [inverse_common_zero_iff h2 h3]
  constructor
  · rintro (h | ⟨hDet,hN,hM⟩)
    · exact h
    · obtain ⟨hx,hw⟩ := inverse_norm_anisotropic hp hp3 hN
      have hM' : inverseNormLeft z y=0 := by simpa [inverseNormLeft,inverseNormRight] using hM
      obtain ⟨hz,hy⟩ := inverse_norm_anisotropic hp hp3 hM'
      simp [hx,hw,hz,hy]
  · exact Or.inl

#print axioms inverse_common_zero_iff
#print axioms inverse_common_zero_inert_iff


private lemma inverse_unit_of_nonzero_mod {p : ℕ} (hp : p.Prime) (k : ℕ) (n : ℤ)
    (hn : (n : ZMod p) ≠ 0) : IsUnit (n : ZMod (p^k)) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime n (p^k)).mpr
  have hnot : ¬ (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).not.mp hn
  have hc : IsCoprime (p : ℤ) n :=
    (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hnot
  simpa only [Nat.cast_pow] using hc.pow_left (m := k)

/-- The inert-prime description holds at every prime power for a primitive
root vector. No boundedness assumption on the roots is needed. -/
theorem inverse_common_prime_power_inert_iff {p : ℕ} (hp : p.Prime)
    (hp3 : p%3=2) (hp2 : p ≠ 2) {x y z w : ℤ}
    (hprimitive : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z ∧ (p : ℤ) ∣ w))
    (k : ℕ) :
    ((p : ℤ)^k ∣ inverseA x y z w ∧ (p : ℤ)^k ∣ inverseB x y z w ∧
      (p : ℤ)^k ∣ inverseT x y z w) ↔
      ((p : ℤ)^k ∣ x-z ∧ (p : ℤ)^k ∣ w-y) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
    omega
  have hu2 : IsUnit (2 : ZMod (p^k)) := by
    simpa using inverse_unit_of_nonzero_mod hp k 2 (by simpa using h2)
  have hu3 : IsUnit (3 : ZMod (p^k)) := by
    simpa using inverse_unit_of_nonzero_mod hp k 3 (by simpa using h3)
  have cast_zero (n : ℤ) : (n : ZMod (p^k))=0 ↔ (p : ℤ)^k ∣ n := by
    simpa only [Nat.cast_pow] using ZMod.intCast_zmod_eq_zero_iff_dvd n (p^k)
  constructor
  · rintro ⟨hA,hB,hT⟩
    by_cases hk : k=0
    · simp [hk]
    have hpk : (p : ℤ) ∣ (p : ℤ)^k := dvd_pow_self _ hk
    have hAp : inverseA (x : ZMod p) y z w=0 := by
      simpa [inverseA] using (ZMod.intCast_zmod_eq_zero_iff_dvd (inverseA x y z w) p).mpr (hpk.trans hA)
    have hBp : inverseB (x : ZMod p) y z w=0 := by
      simpa [inverseB] using (ZMod.intCast_zmod_eq_zero_iff_dvd (inverseB x y z w) p).mpr (hpk.trans hB)
    have hTp : inverseT (x : ZMod p) y z w=0 := by
      simpa [inverseT] using (ZMod.intCast_zmod_eq_zero_iff_dvd (inverseT x y z w) p).mpr (hpk.trans hT)
    obtain ⟨hxz,hyw⟩ := (inverse_common_zero_inert_iff hp hp3 hp2 x y z w).mp ⟨hAp,hBp,hTp⟩
    have hN : inverseNormLeft (x : ZMod p) w ≠ 0 := by
      intro hN0
      obtain ⟨hx,hw⟩ := inverse_norm_anisotropic hp hp3 hN0
      have hz : (z : ZMod p)=0 := hxz.symm.trans hx
      have hy : (y : ZMod p)=0 := hyw.trans hw
      exact hprimitive ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx,
        (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy,
        (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz,
        (ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp hw⟩
    have huN : IsUnit (inverseNormLeft (x : ZMod (p^k)) w) := by
      have hh := inverse_unit_of_nonzero_mod hp k (inverseNormLeft x w)
        (by simpa [inverseNormLeft] using hN)
      simpa [inverseNormLeft] using hh
    have hAK : inverseA (x : ZMod (p^k)) y z w=0 := by simpa [inverseA] using (cast_zero _).mpr hA
    have hBK : inverseB (x : ZMod (p^k)) y z w=0 := by simpa [inverseB] using (cast_zero _).mpr hB
    have hTK : inverseT (x : ZMod (p^k)) y z w=0 := by simpa [inverseT] using (cast_zero _).mpr hT
    have hDet : inverseDet (x : ZMod (p^k)) y z w=0 := by
      change 3*inverseDet (x : ZMod (p^k)) y z w=0 at hTK
      exact hu3.mul_right_eq_zero.mp hTK
    obtain ⟨_,hx,hw⟩ := inverse_base_identities (x : ZMod (p^k)) y z w
    rw [hAK,hBK,hDet] at hx hw
    have hx' : 2*((x : ZMod (p^k))-z)*inverseNormLeft (x : ZMod (p^k)) w=0 := by simpa using hx.symm
    have hw' : 2*((w : ZMod (p^k))-y)*inverseNormLeft (x : ZMod (p^k)) w=0 := by simpa using hw.symm
    have hx0 := hu2.mul_right_eq_zero.mp (huN.mul_left_eq_zero.mp hx')
    have hw0 := hu2.mul_right_eq_zero.mp (huN.mul_left_eq_zero.mp hw')
    exact ⟨(cast_zero _).mp (by simpa using hx0),(cast_zero _).mp (by simpa using hw0)⟩
  · rintro ⟨hx,hw⟩
    have hxz : (x : ZMod (p^k))=(z : ZMod (p^k)) := sub_eq_zero.mp (by simpa using (cast_zero _).mpr hx)
    have hwy : (w : ZMod (p^k))=(y : ZMod (p^k)) := sub_eq_zero.mp (by simpa using (cast_zero _).mpr hw)
    have hA0 : inverseA (x : ZMod (p^k)) y z w=0 := by rw [hxz,hwy]; dsimp [inverseA]; ring
    have hB0 : inverseB (x : ZMod (p^k)) y z w=0 := by rw [hxz,hwy]; dsimp [inverseB]; ring
    have hT0 : inverseT (x : ZMod (p^k)) y z w=0 := by rw [hxz,hwy]; dsimp [inverseT]; ring
    exact ⟨(cast_zero _).mp (by simpa [inverseA] using hA0),
      (cast_zero _).mp (by simpa [inverseB] using hB0),
      (cast_zero _).mp (by simpa [inverseT] using hT0)⟩

/-- Equivalently, the inert prime-power part of the inverse gcd is exactly
the prime-power part of the gcd of the two cross gaps. -/
lemma inverseGcd_inert_pow_dvd_iff {p : ℕ} (hp : p.Prime)
    (hp3 : p%3=2) (hp2 : p ≠ 2) {x y z w : ℤ}
    (hprimitive : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z ∧ (p : ℤ) ∣ w))
    (k : ℕ) :
    p^k ∣ inverseGcd x y z w ↔ p^k ∣ Int.gcd (x-z) (w-y) := by
  rw [inverseGcd,Nat.dvd_gcd_iff,Int.dvd_gcd_iff,← Int.natCast_dvd,Int.dvd_gcd_iff]
  simp only [Nat.cast_pow]
  rw [and_assoc]
  exact inverse_common_prime_power_inert_iff hp hp3 hp2 hprimitive k

#print axioms inverse_common_prime_power_inert_iff
#print axioms inverseGcd_inert_pow_dvd_iff

end Erdos1206.CubicBaseLocus
