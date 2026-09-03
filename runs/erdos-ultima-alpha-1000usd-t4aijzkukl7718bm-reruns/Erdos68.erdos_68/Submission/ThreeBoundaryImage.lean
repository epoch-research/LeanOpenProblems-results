import Submission.ThreeBoundaryKernel

/-! The exact integer image of three cleared boundary rows. This describes
attainability of pairs, not the size of weights attaining them, and does not
settle the irrationality conjecture in Spec.lean. -/

namespace ThreeBoundaryImage

open Finset

/-- The only obstruction to attaining a specified pair is a single gcd
congruence. No bound on the attaining weights is asserted. -/
theorem cleared_pair_iff_gcd_dvd (b : Fin 3 → ℤ) (C s z : ℤ) :
    (∃ w : Fin 3 → ℤ, (∑ i, w i) = s ∧ (∑ i, w i * b i) = C * z) ↔
      ((b 1 - b 0).gcd (b 2 - b 0) : ℤ) ∣ C * z - b 0 * s := by
  let u := b 1 - b 0
  let v := b 2 - b 0
  change (∃ w : Fin 3 → ℤ, (∑ i, w i) = s ∧ (∑ i, w i * b i) = C * z) ↔
    (u.gcd v : ℤ) ∣ C * z - b 0 * s
  constructor
  · rintro ⟨w, hs, hb⟩
    have hid : C * z - b 0 * s = u * w 1 + v * w 2 := by
      simp only [Fin.sum_univ_three] at hs hb
      dsimp [u, v]
      linear_combination b 0 * hs - hb
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_left (Int.gcd_dvd_left u v) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right u v) _)
  · rintro ⟨k, hk⟩
    let w : Fin 3 → ℤ := ![s - k * u.gcdA v - k * u.gcdB v,
      k * u.gcdA v, k * u.gcdB v]
    refine ⟨w, ?_, ?_⟩
    · simp [w, Fin.sum_univ_three]
      ring
    · have hab := Int.gcd_eq_gcd_ab u v
      have hrel : u * (k * u.gcdA v) + v * (k * u.gcdB v) = C * z - b 0 * s := by
        rw [hk, hab]
        ring
      simp [w, Fin.sum_univ_three]
      dsimp [u, v] at hrel
      linear_combination hrel

/-- Coprime boundary differences make every integer coefficient pair
attainable. The construction can require large weights. -/
theorem cleared_pair_surjective (b : Fin 3 → ℤ) (C : ℤ)
    (hc : IsCoprime (b 1 - b 0) (b 2 - b 0)) (s z : ℤ) :
    ∃ w : Fin 3 → ℤ, (∑ i, w i) = s ∧ (∑ i, w i * b i) = C * z := by
  apply (cleared_pair_iff_gcd_dvd b C s z).mpr
  rw [Int.isCoprime_iff_gcd_eq_one.mp hc]
  exact one_dvd _

end ThreeBoundaryImage

#print axioms ThreeBoundaryImage.cleared_pair_iff_gcd_dvd
#print axioms ThreeBoundaryImage.cleared_pair_surjective
