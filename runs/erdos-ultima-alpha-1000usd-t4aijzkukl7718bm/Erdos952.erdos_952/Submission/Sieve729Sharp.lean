import Submission.Sieve729Result
import Submission.Sieve729TenResult

/-! The exact jump threshold for one particular six-prime sieve. This does
not identify the threshold, or establish existence of any threshold, for
actual Gaussian-prime rays. -/
namespace Erdos952Investigation.Sieve729Sharp
open Sieve729
set_option maxHeartbeats 0

def HasSixPrimeRay (C : ℤ) : Prop :=
  ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    ∀ n, ((x n).re+(x n).im)%2 = 1 ∧
      (∀ k : Fin 6, (x n).norm % (prime k : ℤ) ≠ 0) ∧
      (x (n+1)-x n).norm < C

lemma no_ray_le_eight (C : ℤ) (hC : C ≤ 8) : ¬ HasSixPrimeRay C := by
  rintro ⟨x,hx,h⟩
  let f : ℕ → ℤ × ℤ := fun n => (coordU (x n),coordV (x n))
  apply PeriodicBarrier.no_injective_path certifiedBarrier period (by norm_num [period])
    allowed_period allowed_reflect allowed_swap
  refine ⟨f,?_,?_,?_⟩
  · intro i j hij
    have hu : coordU (x i) = coordU (x j) := congrArg Prod.fst hij
    have hv : coordV (x i) = coordV (x j) := congrArg Prod.snd hij
    apply hx
    apply Zsqrtd.ext
    · rw [coordinates_re (h i).1,coordinates_re (h j).1,hu,hv]
    · rw [coordinates_im (h i).1,coordinates_im (h j).1,hu,hv]
  · intro n k
    have he : normPoly (coordU (x n)) (coordV (x n)) = (x n).norm := by
      rw [gaussian_norm_sq,coordinates_re (h n).1,coordinates_im (h n).1]
      rfl
    change normPoly (coordU (x n)) (coordV (x n)) % (prime k : ℤ) ≠ 0
    rw [he]
    exact (h n).2.1 k
  · intro n
    exact norm_lt_eight_coordinates (h n).1 (h (n+1)).1 ((h n).2.2.trans_le hC)

lemma ray_at_nine : HasSixPrimeRay 9 := by
  obtain ⟨x,hx,h⟩ := Sieve729Ten.six_prime_sieve_ray_at_ten
  refine ⟨x,hx,?_⟩
  intro n
  refine ⟨(h n).1,(h n).2.1,?_⟩
  have he : (x (n+1)-x n).norm % 2 = 0 := by
    rw [norm_mod_two]
    simp only [Zsqrtd.re_sub,Zsqrtd.im_sub]
    have h0 := (h n).1
    have h1 := (h (n+1)).1
    omega
  have hh := (h n).2.2
  omega

/-- Sharp only for the stated sieve: it uses parity and the six norm-divisor
tests for `3, 5, 7, 13, 17, 29`, not Gaussian primality. -/
theorem six_prime_threshold (C : ℤ) : HasSixPrimeRay C ↔ 8 < C := by
  constructor
  · intro h
    by_contra! hC
    exact no_ray_le_eight C hC h
  · intro hC
    obtain ⟨x,hx,h⟩ := ray_at_nine
    refine ⟨x,hx,fun n => ⟨(h n).1,(h n).2.1,?_⟩⟩
    exact (h n).2.2.trans_le (by omega)

#print axioms six_prime_threshold
end Erdos952Investigation.Sieve729Sharp
