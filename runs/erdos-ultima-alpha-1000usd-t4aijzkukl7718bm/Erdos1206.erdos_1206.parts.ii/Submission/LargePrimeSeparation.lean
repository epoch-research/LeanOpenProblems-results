import FormalConjecturesUtil

/-! Large primes cannot be shared by just two roots of a strict cubic
collision. This local arithmetic separation does not give a global density
bound or settle the cube-Sidon conjecture. -/

namespace Erdos1206.LargePrimeSeparation

lemma large_prime_cube_congruence {p N : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hsize : 3*N^2 < p^3) {x y : ℤ}
    (hx : |x| ≤ N) (hy : |y| ≤ N) (hxy : x ≠ y)
    (hcong : (p : ℤ)^3 ∣ x^3-y^3) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpnot3 : ¬ (p : ℤ) ∣ 3 := by
    intro h
    apply hp3
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
      (Int.natCast_dvd_natCast.mp h)
  have hN : (1 : ℤ) ≤ N := by
    by_contra h
    have hN0 : N = 0 := by omega
    simp only [hN0, Nat.cast_zero, abs_le] at hx hy
    omega
  have hsizeZ : 3*(N : ℤ)^2 < (p : ℤ)^3 := by exact_mod_cast hsize
  have hx2 : x^2 ≤ (N : ℤ)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg x) hx
    nlinarith [sq_abs x]
  have hy2 : y^2 ≤ (N : ℤ)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg y) hy
    nlinarith [sq_abs y]
  have hnorm : x^2+x*y+y^2 ≤ 3*(N : ℤ)^2 := by nlinarith [sq_nonneg (x-y)]
  have hnorm0 : 0 < x^2+x*y+y^2 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), sq_nonneg (x+y)]
  have hdiff : |x-y| ≤ 3*(N : ℤ)^2 := by
    have h := abs_sub x y
    nlinarith
  have hfact : (p : ℤ)^3 ∣ (x-y)*(x^2+x*y+y^2) := by
    convert hcong using 1 <;> ring
  have hpx : (p : ℤ) ∣ x := by
    by_contra hpx
    by_cases hpd : (p : ℤ) ∣ x-y
    · have hpq : ¬ (p : ℤ) ∣ x^2+x*y+y^2 := by
        intro h
        have hh : (p : ℤ) ∣ 3*x^2 := by
          convert dvd_add h (dvd_mul_of_dvd_left hpd (2*x+y)) using 1 <;> ring
        exact hpx (hpZ.dvd_of_dvd_pow ((hpZ.dvd_mul.mp hh).resolve_left hpnot3))
      have hh := hpZ.pow_dvd_of_dvd_mul_right 3 hpq hfact
      have hle := Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hxy)) (by simpa only [Int.abs_eq_natAbs] using Int.dvd_natAbs.mpr hh)
      omega
    · have hh := hpZ.pow_dvd_of_dvd_mul_left 3 hpd hfact
      have hle := Int.le_of_dvd hnorm0 hh
      omega
  refine ⟨hpx, hpZ.dvd_of_dvd_pow (n := 3) ?_⟩
  have hh : (p : ℤ) ∣ x^3-y^3 := (dvd_pow_self (p : ℤ) (by decide)).trans hcong
  have hp3x : (p : ℤ) ∣ x^3 := hpx.trans (dvd_pow_self x (by decide))
  convert dvd_sub hp3x hh using 1 <;> ring

lemma sum_cubes_large_prime {p N : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hsize : 3*N^2 < p^3) {x y : ℤ}
    (hx : |x| ≤ N) (hy : |y| ≤ N) (hxy : x ≠ -y)
    (hcong : (p : ℤ)^3 ∣ x^3+y^3) : (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y := by
  have hcong' : (p : ℤ)^3 ∣ x^3-(-y)^3 := by
    convert hcong using 1 <;> ring
  obtain ⟨h₁,h₂⟩ := large_prime_cube_congruence hp hp3 hsize hx
    (by simpa using hy) hxy hcong'
  exact ⟨h₁, (dvd_neg.mp h₂)⟩

lemma same_side {p N a b c d : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hsize : 3*N^2 < p^3) (hc : c ≤ N) (hd : d ≤ N) (hcd : 0 < c+d)
    (he : a^3+b^3=c^3+d^3) (ha : p ∣ a) (hb : p ∣ b) : p ∣ c ∧ p ∣ d := by
  have heZ : (a : ℤ)^3+b^3=c^3+d^3 := by exact_mod_cast he
  have haZ : (p : ℤ) ∣ a := Int.natCast_dvd_natCast.mpr ha
  have hbZ : (p : ℤ) ∣ b := Int.natCast_dvd_natCast.mpr hb
  have hcong : (p : ℤ)^3 ∣ (c : ℤ)^3+(d : ℤ)^3 := by
    rw [← heZ]
    exact dvd_add (pow_dvd_pow_of_dvd haZ 3) (pow_dvd_pow_of_dvd hbZ 3)
  obtain ⟨h₁,h₂⟩ := sum_cubes_large_prime hp hp3 hsize
    (x := c) (y := d) (by simpa using hc) (by simpa using hd) (by omega) hcong
  exact ⟨Int.natCast_dvd_natCast.mp h₁, Int.natCast_dvd_natCast.mp h₂⟩

lemma opposite_sides {p N a b c d : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hsize : 3*N^2 < p^3) (hb : b ≤ N) (hd : d ≤ N) (hbd : b ≠ d)
    (he : a^3+b^3=c^3+d^3) (ha : p ∣ a) (hc : p ∣ c) : p ∣ b ∧ p ∣ d := by
  have heZ : (a : ℤ)^3+b^3=c^3+d^3 := by exact_mod_cast he
  have haZ : (p : ℤ) ∣ a := Int.natCast_dvd_natCast.mpr ha
  have hcZ : (p : ℤ) ∣ c := Int.natCast_dvd_natCast.mpr hc
  have hcong : (p : ℤ)^3 ∣ (b : ℤ)^3-(d : ℤ)^3 := by
    have hh := dvd_sub (pow_dvd_pow_of_dvd hcZ 3) (pow_dvd_pow_of_dvd haZ 3)
    convert hh using 1 <;> linarith
  obtain ⟨h₁,h₂⟩ := large_prime_cube_congruence hp hp3 hsize
    (x := b) (y := d) (by simpa using hb) (by simpa using hd) (by omega) hcong
  exact ⟨Int.natCast_dvd_natCast.mp h₁, Int.natCast_dvd_natCast.mp h₂⟩

/-- In a strict positive collision, any two roots sharing a sufficiently
large prime force that prime to divide all four roots. -/
theorem shared_prime_dvd_all {p N a b c d : ℕ} (hp : p.Prime)
    (hsize : 3*N^2 < p^3) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hdN : d ≤ N) (he : a^3+d^3=b^3+c^3)
    (hshare : (p ∣ a ∧ p ∣ b) ∨ (p ∣ a ∧ p ∣ c) ∨ (p ∣ a ∧ p ∣ d) ∨
      (p ∣ b ∧ p ∣ c) ∨ (p ∣ b ∧ p ∣ d) ∨ (p ∣ c ∧ p ∣ d)) :
    p ∣ a ∧ p ∣ b ∧ p ∣ c ∧ p ∣ d := by
  have hp3 : p ≠ 3 := by
    intro hh
    subst p
    have hN : 4 ≤ N := by omega
    nlinarith
  rcases hshare with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · obtain ⟨h₃,h₄⟩ := opposite_sides hp hp3 hsize hdN (by omega) (by omega) he h₁ h₂
    exact ⟨h₁,h₂,h₄,h₃⟩
  · have he' : a^3+d^3=c^3+b^3 := by omega
    obtain ⟨h₃,h₄⟩ := opposite_sides hp hp3 hsize hdN (by omega) (by omega) he' h₁ h₂
    exact ⟨h₁,h₄,h₂,h₃⟩
  · obtain ⟨h₃,h₄⟩ := same_side hp hp3 hsize (by omega) (by omega) (by omega) he h₁ h₂
    exact ⟨h₁,h₃,h₄,h₂⟩
  · obtain ⟨h₃,h₄⟩ := same_side hp hp3 hsize (by omega) hdN (by omega) he.symm h₁ h₂
    exact ⟨h₃,h₁,h₂,h₄⟩
  · have he' : b^3+c^3=d^3+a^3 := by omega
    obtain ⟨h₃,h₄⟩ := opposite_sides hp hp3 hsize (by omega) (by omega) (by omega) he' h₁ h₂
    exact ⟨h₄,h₁,h₃,h₂⟩
  · have he' : c^3+b^3=d^3+a^3 := by omega
    obtain ⟨h₃,h₄⟩ := opposite_sides hp hp3 hsize (by omega) (by omega) (by omega) he' h₁ h₂
    exact ⟨h₄,h₃,h₁,h₂⟩

/-- A prime shared by two roots of a primitive strict collision is bounded
by the two-thirds power of the height (with the exact cubed bound below). -/
theorem primitive_shared_prime_bound {p a b c d : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (he : a^3+d^3=b^3+c^3)
    (hprimitive : Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1)
    (hshare : (p ∣ a ∧ p ∣ b) ∨ (p ∣ a ∧ p ∣ c) ∨ (p ∣ a ∧ p ∣ d) ∨
      (p ∣ b ∧ p ∣ c) ∨ (p ∣ b ∧ p ∣ d) ∨ (p ∣ c ∧ p ∣ d)) :
    p^3 ≤ 3*d^2 := by
  by_contra hh
  have hsize : 3*d^2 < p^3 := by omega
  obtain ⟨h₁,h₂,h₃,h₄⟩ := shared_prime_dvd_all hp hsize ha hab hbc hcd le_rfl he hshare
  have hh := Nat.dvd_gcd (Nat.dvd_gcd h₁ h₂) (Nat.dvd_gcd h₃ h₄)
  rw [hprimitive] at hh
  exact hp.ne_one (Nat.dvd_one.mp hh)

#print axioms large_prime_cube_congruence
#print axioms shared_prime_dvd_all
#print axioms primitive_shared_prime_bound

end Erdos1206.LargePrimeSeparation
