import Submission.BinaryCriticalMatrixCertificates

/-! A finite arithmetic obstruction to the first critical matrix search
family. This rules out its erased-transient template, not Erdős406. -/
namespace Erdos406BinaryCriticalResetObstruction
open Erdos406BinaryCriticalMatrix

lemma finite_obstruction (S : ℕ → ℝ) (X δ : ℝ) (hδ : 0≤δ)
    (hstep : ∀ n d : ℕ, d<2 → S (3*n+d)≤3*S n)
    (h2 : S 2=2) (h3 : S 3=X+16*δ)
    (h6 : 2*X≤S 6) (h7 : 16*δ^2≤S 7) (h256 : 2048≤S 256) : False := by
  have h26 := hstep 2 0 (by decide)
  have h27 := hstep 2 1 (by decide)
  have h39 := hstep 3 0 (by decide)
  have h928 := hstep 9 1 (by decide)
  have h2885 := hstep 28 1 (by decide)
  have h85256 := hstep 85 1 (by decide)
  norm_num only [Nat.reduceMul,Nat.reduceAdd,h2,h3] at h26 h27 h39 h928 h2885 h85256
  have hδ1 : δ≤1 := by nlinarith
  nlinarith

/-- Every nonnegative two-layer mass system with budget16 and a transient
annihilated by a zero bit fails the required affine construction inequalities.
The odd updates of x and y are otherwise arbitrary. -/
theorem no_reset_mass_model (x y t : ℕ → ℝ) (δ : ℝ) (hδ : 0≤δ)
    (hx0 : ∀ n, 0≤x n) (hy0 : ∀ n, 0≤y n)
    (hx : ∀ n : ℕ, 0<n → x (2*n)=2*x n+2*y n)
    (hy : ∀ n : ℕ, 0<n → y (2*n)=2*y n)
    (ht0 : ∀ n : ℕ, 0<n → t (2*n)=0)
    (ht1 : ∀ n : ℕ, 0<n → t (2*n+1)=δ*t n)
    (hx1 : x 1=0) (hy1 : y 1=1) (htone : t 1=16) :
    ¬ ∀ n d : ℕ, d<2 → x (3*n+d)+t (3*n+d)≤3*(x n+t n) := by
  intro hstep
  apply finite_obstruction (fun n => x n+t n) (x 3) δ hδ hstep
  · have hh := hx 1 (by decide)
    have ht := ht0 1 (by decide)
    norm_num only [Nat.reduceMul,hx1,hy1] at hh ht
    linarith
  · have ht := ht1 1 (by decide)
    norm_num only [Nat.reduceMul,Nat.reduceAdd,htone] at ht
    linarith
  · have hh := hx 3 (by decide)
    have ht := ht0 3 (by decide)
    norm_num only [Nat.reduceMul] at hh ht
    linarith [hy0 3]
  · have ht := ht1 3 (by decide)
    have ht3 := ht1 1 (by decide)
    norm_num only [Nat.reduceMul,Nat.reduceAdd,htone] at ht ht3
    nlinarith [hx0 7]
  · have hp := jordan_power_lower x y (fun n hn => (hx n hn).ge)
      (fun n hn => (hy n hn).ge) 8
    have ht := ht0 128 (by decide)
    norm_num only [Nat.reducePow,Nat.cast_ofNat,hx1,hy1,zero_mul,mul_zero,
      mul_one,zero_add] at hp
    norm_num only [Nat.reduceMul] at ht
    linarith

end Erdos406BinaryCriticalResetObstruction
