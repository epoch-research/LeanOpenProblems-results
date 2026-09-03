import Submission.Sieve729MaskProof
import Submission.Coordinates

/-! A finite-height barrier for this sieve would give a uniform squared-step lower bound of 8. -/

namespace Erdos952Investigation.Sieve729

set_option maxHeartbeats 0

lemma allowed_period (k : ℤ) (z : ℤ × ℤ) (hz : Allowed z) :
    Allowed (z.1 - k * period, z.2) := by
  intro j
  have hp : (prime j : ℤ) ∣ period := by exact_mod_cast prime_dvd_period j
  have hmod : (z.1 - k * period) % (prime j : ℤ) = z.1 % (prime j : ℤ) := by
    simp only [Int.sub_emod, Int.mul_emod, Int.emod_eq_zero_of_dvd hp, mul_zero,
      Int.zero_emod, sub_zero, Int.emod_emod]
  have he : normPoly (z.1 - k * period) z.2 % (prime j : ℤ) =
      normPoly z.1 z.2 % (prime j : ℤ) := by
    rw [← normPoly_mod (prime j) (z.1 - k * period) z.2, hmod, normPoly_mod]
  change normPoly (z.1 - k * period) z.2 % (prime j : ℤ) ≠ 0
  rw [he]
  exact hz j

lemma allowed_reflect (z : ℤ × ℤ) (hz : Allowed z) : Allowed (-1 - z.1, z.2) := by
  intro j
  have he : normPoly (-1 - z.1) z.2 = normPoly z.1 z.2 := by unfold normPoly; ring
  change normPoly (-1 - z.1) z.2 % (prime j : ℤ) ≠ 0
  rw [he]
  exact hz j

lemma allowed_swap (z : ℤ × ℤ) (hz : Allowed z) : Allowed (z.2, z.1) := by
  intro j
  have he : normPoly z.2 z.1 = normPoly z.1 z.2 := by unfold normPoly; ring
  change normPoly z.2 z.1 % (prime j : ℤ) ≠ 0
  rw [he]
  exact hz j

lemma prime_allowed {z : GaussianInt} (hz : Prime z) (hlarge : 841 < z.norm) :
    Allowed (coordU z, coordV z) := by
  have ho := prime_large_odd_coordinate_sum hz (by omega)
  have he : normPoly (coordU z) (coordV z) = z.norm := by
    rw [gaussian_norm_sq, coordinates_re ho, coordinates_im ho]
    rfl
  intro k
  change normPoly (coordU z) (coordV z) % (prime k : ℤ) ≠ 0
  rw [he]
  apply prime_large_norm_residue hz (prime_is_prime k)
  have hk : (prime k : ℤ) ≤ 29 := by exact_mod_cast prime_le k
  have hk0 : (0 : ℤ) ≤ prime k := Int.natCast_nonneg _
  nlinarith

lemma norm_lt_eight_coordinates {z w : GaussianInt}
    (hz : (z.re + z.im) % 2 = 1) (hw : (w.re + w.im) % 2 = 1)
    (hstep : (w - z).norm < 8) :
    PeriodicBarrier.KingStep (coordU z, coordV z) (coordU w, coordV w) := by
  have hnorm : (coordU w - coordU z) ^ 2 + (coordV w - coordV z) ^ 2 < 4 := by
    rw [gaussian_norm_sq] at hstep
    change (w.re - z.re) ^ 2 + (w.im - z.im) ^ 2 < 8 at hstep
    rw [coordinates_re hz, coordinates_im hz, coordinates_re hw, coordinates_im hw] at hstep
    nlinarith
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [sq_nonneg (coordU w - coordU z), sq_nonneg (coordV w - coordV z)]

theorem step_bound_gt_eight_of_barrier (barrier : PeriodicBarrier.Barrier Allowed)
    (x : ℕ → GaussianInt) (C : ℤ) (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 8 < C := by
  by_contra hC
  have hC : C ≤ 8 := le_of_not_gt hC
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx 841
  let y : ℕ → GaussianInt := fun n => x (N + n)
  have hyp (n : ℕ) : Prime (y n) := (h (N + n)).1
  have hyn (n : ℕ) : 841 < (y n).norm := hN (N + n) (by omega)
  have hyo (n : ℕ) : ((y n).re + (y n).im) % 2 = 1 :=
    prime_large_odd_coordinate_sum (hyp n) (by have := hyn n; omega)
  let f : ℕ → ℤ × ℤ := fun n => (coordU (y n), coordV (y n))
  apply PeriodicBarrier.no_injective_path barrier period (by norm_num [period])
    allowed_period allowed_reflect allowed_swap
  refine ⟨f, ?_, fun n => prime_allowed (hyp n) (hyn n), ?_⟩
  · intro i j hij
    have hu : coordU (y i) = coordU (y j) := congrArg Prod.fst hij
    have hv : coordV (y i) = coordV (y j) := congrArg Prod.snd hij
    have he : y i = y j := by
      apply Zsqrtd.ext
      · rw [coordinates_re (hyo i), coordinates_re (hyo j), hu, hv]
      · rw [coordinates_im (hyo i), coordinates_im (hyo j), hu, hv]
    have := hx he
    omega
  · intro n
    apply norm_lt_eight_coordinates (hyo n) (hyo (n + 1))
    have hs : (y (n + 1) - y n).norm < C := by
      simpa only [y, Nat.add_assoc] using (h (N + n)).2
    exact lt_of_lt_of_le hs hC

#print axioms step_bound_gt_eight_of_barrier

end Erdos952Investigation.Sieve729
