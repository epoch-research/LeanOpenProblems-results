import Submission.QuadraticLocalAdmissibility

/-! Positive integral shifts of binary quadratics, preserving discriminants
and primitivity. An auxiliary sieve preparation. -/
namespace Erdos1206.PositiveQuadraticShift

section Formulas
variable {R : Type*} [CommRing R]
def beta (a b k : R) : R := 2*a*k+b
def gamma (a b c k : R) : R := a*k^2+b*k+c

lemma value_shift (a b c k s t : R) :
    a*s^2+beta a b k*s*t+gamma a b c k*t^2=
      a*(s+k*t)^2+b*(s+k*t)*t+c*t^2 := by
  dsimp [beta,gamma]
  ring

lemma discriminant_shift (a b c k : R) :
    beta a b k^2-4*a*gamma a b c k=b^2-4*a*c := by
  dsimp [beta,gamma]
  ring

lemma dvd_shift_iff (d a b c k : R) :
    (d ∣ a ∧ d ∣ beta a b k ∧ d ∣ gamma a b c k) ↔
      (d ∣ a ∧ d ∣ b ∧ d ∣ c) := by
  constructor
  · rintro ⟨ha,hb,hc⟩
    have hb' : d ∣ b := by
      have hh := dvd_sub hb (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha 2) k)
      simpa [beta] using hh
    have hc' : d ∣ c := by
      have hh := dvd_sub hc (dvd_add
        (dvd_mul_of_dvd_left ha (k^2)) (dvd_mul_of_dvd_left hb' k))
      simpa [gamma] using hh
    exact ⟨ha,hb',hc'⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha,dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha 2) k) hb,
      dvd_add (dvd_add (dvd_mul_of_dvd_left ha (k^2)) (dvd_mul_of_dvd_left hb k)) hc⟩
end Formulas

lemma coefficients_pos {a b c k : ℤ} (ha : 0 < a) (hk : |b|+|c|+1 ≤ k) :
    0 < k ∧ 0 < beta a b k ∧ 0 < gamma a b c k := by
  have hk0 : 0 < k := by have := abs_nonneg b; have := abs_nonneg c; omega
  have hb : 1 ≤ k+b := by have := neg_le_abs b; have := abs_nonneg c; omega
  have hc : 1 ≤ k+c := by have := neg_le_abs c; have := abs_nonneg b; omega
  have ha1 : 0 ≤ a-1 := by omega
  have h₁ := mul_nonneg ha1 hk0.le
  have h₂ := mul_nonneg ha1 (sq_nonneg k)
  have h₃ := mul_nonneg hk0.le (show 0 ≤ k+b-1 by omega)
  refine ⟨hk0,?_,?_⟩
  · dsimp [beta]; nlinarith
  · dsimp [gamma]; nlinarith

lemma nat_primitive {a b c k : ℤ} (ha : 0 ≤ a)
    (hb : 0 ≤ beta a b k) (hc : 0 ≤ gamma a b c k)
    (hprim : Nat.gcd a.natAbs (Nat.gcd b.natAbs c.natAbs)=1) :
    Nat.gcd a.toNat (Nat.gcd (beta a b k).toNat (gamma a b c k).toNat)=1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpg
  obtain ⟨hpa,hpbc⟩ := Nat.dvd_gcd_iff.mp hpg
  obtain ⟨hpb,hpc⟩ := Nat.dvd_gcd_iff.mp hpbc
  have hi (z : ℤ) (hz : 0 ≤ z) (h : p ∣ z.toNat) : (p:ℤ) ∣ z := by
    have hh : (p:ℤ) ∣ (z.toNat:ℤ) := by exact_mod_cast h
    simpa only [Int.toNat_of_nonneg hz] using hh
  obtain ⟨hqa,hqb,hqc⟩ := (dvd_shift_iff (p:ℤ) a b c k).mp
    ⟨hi a ha hpa,hi _ hb hpb,hi _ hc hpc⟩
  have hh := Nat.dvd_gcd (Int.natCast_dvd.mp hqa)
    (Nat.dvd_gcd (Int.natCast_dvd.mp hqb) (Int.natCast_dvd.mp hqc))
  rw [hprim] at hh
  exact hp.not_dvd_one hh

lemma nat_discriminant {a b c k : ℤ} (ha : 0 ≤ a)
    (hb : 0 ≤ beta a b k) (hc : 0 ≤ gamma a b c k) :
    QuadraticSquarefreeSieve.discriminant a.toNat (beta a b k).toNat (gamma a b c k).toNat=
      b^2-4*a*c := by
  simp only [QuadraticSquarefreeSieve.discriminant,Int.toNat_of_nonneg ha,
    Int.toNat_of_nonneg hb,Int.toNat_of_nonneg hc,discriminant_shift]

#print axioms coefficients_pos
#print axioms nat_primitive
#print axioms nat_discriminant
end Erdos1206.PositiveQuadraticShift
