import FormalConjecturesUtil

/-! An infinite family of pairwise-coprime cubic collisions.
This is an obstruction to simple common-factor arguments, not a settlement of
the positive-density cube-Sidon conjecture. -/

namespace Erdos1206

private lemma quad_coprime_of_bezout
    {a b c d e f R k t : ℕ} {u v : ℤ}
    (hbez : u * ((a * t ^ 2 + b * t + c : ℕ) : ℤ) +
      v * ((d * t ^ 2 + e * t + f : ℕ) : ℤ) = R)
    (hR : R ∣ k) (ht : k ∣ t) (hcf : Nat.Coprime c f) :
    Nat.Coprime (a * t ^ 2 + b * t + c) (d * t ^ 2 + e * t + f) := by
  let g := Nat.gcd (a * t ^ 2 + b * t + c) (d * t ^ 2 + e * t + f)
  have hg₁ : g ∣ a * t ^ 2 + b * t + c := Nat.gcd_dvd_left _ _
  have hg₂ : g ∣ d * t ^ 2 + e * t + f := Nat.gcd_dvd_right _ _
  have hgR : (g : ℤ) ∣ (R : ℤ) := by
    rw [← hbez]
    apply dvd_add
    · exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hg₁) u
    · exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hg₂) v
  have hgt : g ∣ t := ((Int.natCast_dvd_natCast.mp hgR).trans hR).trans ht
  have hterm (a b : ℕ) : g ∣ a * t ^ 2 + b * t := by
    apply dvd_add
    · exact dvd_mul_of_dvd_right (hgt.trans (dvd_pow_self t (by decide))) a
    · exact dvd_mul_of_dvd_right hgt b
  have hgc : g ∣ c := (Nat.dvd_add_iff_right (hterm a b)).mpr hg₁
  have hgf : g ∣ f := (Nat.dvd_add_iff_right (hterm d e)).mpr hg₂
  have hgcf := Nat.dvd_gcd hgc hgf
  rw [hcf.gcd_eq_one] at hgcf
  exact Nat.dvd_one.mp hgcf

/-- The progression modulus clears six elementary Bézout constants. -/
def coprimeCubeModulus : ℕ := 5914635552

def coprimeCubeA (t : ℕ) : ℕ := 8428 * t ^ 2 + 62629 * t + 116863
def coprimeCubeB (t : ℕ) : ℕ := 8428 * t ^ 2 + 62587 * t + 116707
def coprimeCubeC (t : ℕ) : ℕ := 1204 * t ^ 2 + 9973 * t + 20359
def coprimeCubeD (t : ℕ) : ℕ := 1204 * t ^ 2 + 7915 * t + 12715

lemma coprimeCube_identity (t : ℕ) :
    coprimeCubeA t ^ 3 + coprimeCubeD t ^ 3 =
      coprimeCubeB t ^ 3 + coprimeCubeC t ^ 3 := by
  dsimp [coprimeCubeA, coprimeCubeB, coprimeCubeC, coprimeCubeD]
  ring

lemma coprimeCube_pairwise {t : ℕ} (ht : coprimeCubeModulus ∣ t) :
    Nat.Coprime (coprimeCubeA t) (coprimeCubeB t) ∧
    Nat.Coprime (coprimeCubeA t) (coprimeCubeC t) ∧
    Nat.Coprime (coprimeCubeA t) (coprimeCubeD t) ∧
    Nat.Coprime (coprimeCubeB t) (coprimeCubeC t) ∧
    Nat.Coprime (coprimeCubeB t) (coprimeCubeD t) ∧
    Nat.Coprime (coprimeCubeC t) (coprimeCubeD t) := by
  dsimp [coprimeCubeA, coprimeCubeB, coprimeCubeC, coprimeCubeD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply quad_coprime_of_bezout (R := 3078) (k := coprimeCubeModulus)
      (u := -1204 * (t : ℤ) - 4469) (v := 1204 * (t : ℤ) + 4475)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring
  · apply quad_coprime_of_bezout (R := 705888) (k := coprimeCubeModulus)
      (u := 1204 * (t : ℤ) + 5673) (v := -8428 * (t : ℤ) - 32529)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring
  · apply quad_coprime_of_bezout (R := 175446) (k := coprimeCubeModulus)
      (u := -301 * (t : ℤ) - 818) (v := 2107 * (t : ℤ) + 7532)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring
  · apply quad_coprime_of_bezout (R := 175446) (k := coprimeCubeModulus)
      (u := 301 * (t : ℤ) + 1418) (v := -2107 * (t : ℤ) - 8120)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring
  · apply quad_coprime_of_bezout (R := 705888) (k := coprimeCubeModulus)
      (u := -1204 * (t : ℤ) - 3271) (v := 8428 * (t : ℤ) + 30079)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring
  · apply quad_coprime_of_bezout (R := 150822) (k := coprimeCubeModulus)
      (u := 1204 * (t : ℤ) + 3443) (v := -1204 * (t : ℤ) - 5501)
      _ (by norm_num [coprimeCubeModulus]) ht (by norm_num [Nat.Coprime])
    push_cast
    ring

/-- Pairwise-coprime nontrivial collisions exist with all four roots exceeding
any prescribed bound. -/
lemma arbitrarily_large_pairwise_coprime_cube_collisions (N : ℕ) :
    ∃ a b c d : ℕ, N < a ∧ N < b ∧ N < c ∧ N < d ∧
      a ^ 3 + d ^ 3 = b ^ 3 + c ^ 3 ∧ a ≠ b ∧ a ≠ c ∧
      Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d ∧
      Nat.Coprime b c ∧ Nat.Coprime b d ∧ Nat.Coprime c d := by
  let t := coprimeCubeModulus * N
  have hNt : N ≤ t := by dsimp [t, coprimeCubeModulus]; omega
  refine ⟨coprimeCubeA t, coprimeCubeB t, coprimeCubeC t, coprimeCubeD t,
    ?_, ?_, ?_, ?_, coprimeCube_identity t, ?_, ?_,
    coprimeCube_pairwise (dvd_mul_right coprimeCubeModulus N)⟩
  · dsimp [coprimeCubeA]; omega
  · dsimp [coprimeCubeB]; omega
  · dsimp [coprimeCubeC]; omega
  · dsimp [coprimeCubeD]; omega
  · dsimp [coprimeCubeA, coprimeCubeB]; omega
  · dsimp [coprimeCubeA, coprimeCubeC]; omega

end Erdos1206
