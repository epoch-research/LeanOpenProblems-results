import Submission.TwoIncrementObstruction
import Submission.UniformRationalStrip

/-! A split-prime projection can obstruct even backtracking walks using two
signed directions. The arithmetic separation hypothesis is essential. -/
namespace Erdos952Investigation
namespace SignedDirectionObstruction
open TwoIncrementObstruction
set_option maxHeartbeats 0

lemma val_succ_of_ne_zero {p : ℕ} (hp : p.Prime) (a b : ZMod p)
    (hb : b ≠ 0) (he : b = a+1) : b.val = a.val+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlt := ZMod.val_lt a
  have hval : b.val = (a.val+1)%p := by rw [he,ZMod.val_add,ZMod.val_one]
  have hpos : b.val ≠ 0 := by
    intro hh
    apply hb
    apply ZMod.val_injective
    simpa using hh
  have hsmall : a.val+1 < p := by
    by_contra hh
    have heq : a.val+1 = p := by omega
    rw [heq,Nat.mod_self] at hval
    exact hpos hval
  rwa [Nat.mod_eq_of_lt hsmall] at hval

lemma projection_neg {p : ℕ} (r : ZMod p) (z : GaussianInt) :
    projection r (-z) = -projection r z := by
  simp only [projection,Zsqrtd.re_neg,Zsqrtd.im_neg,Int.cast_neg]
  ring

/-- Avoiding one split-prime divisor forces the transverse coordinate into a
bounded interval, if the only possible directions are the stated two pairs. -/
theorem signed_direction_strip {p : ℕ} (hp : p.Prime) (r : ZMod p)
    (u v : GaussianInt) (hu : projection r u = 0) (hv : projection r v ≠ 0)
    (x : ℕ → GaussianInt) (hne : ∀ n, projection r (x n) ≠ 0)
    (hstep : ∀ n, x (n+1)-x n = u ∨ x (n+1)-x n = -u ∨
      x (n+1)-x n = v ∨ x (n+1)-x n = -v) :
    ∀ n, |(star u*(x n-x 0)).im| ≤ |(star u*v).im| *(p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun n => projection r (x n)/projection r v
  let D : ℤ := (star u*v).im
  have hf (n : ℕ) : f n ≠ 0 := div_ne_zero (hne n) hv
  have hdelta (n : ℕ) : f (n+1)-f n = projection r (x (n+1)-x n)/projection r v := by
    simp only [f,projection_sub,sub_div]
  have hlu : (star u*u).im = 0 := by
    simp only [Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star]
    ring
  have hl (n : ℕ) : (star u*(x (n+1)-x n)).im =
      D*((f (n+1)).val-(f n).val : ℤ) := by
    rcases hstep n with he | he | he | he
    · have hh : f (n+1) = f n := sub_eq_zero.mp (by rw [hdelta,he,hu,zero_div])
      rw [he,hlu,hh,sub_self,mul_zero]
    · have hh : f (n+1) = f n := sub_eq_zero.mp (by
        rw [hdelta,he,projection_neg,hu,neg_zero,zero_div])
      rw [he,mul_neg,Zsqrtd.im_neg,hlu,neg_zero,hh,sub_self,mul_zero]
    · have hdiff : f (n+1)-f n = 1 := by rw [hdelta,he,div_self hv]
      have hh : f (n+1) = f n+1 := by linear_combination hdiff
      have ht := val_succ_of_ne_zero hp (f n) (f (n+1)) (hf (n+1)) hh
      have ht' : ((f (n+1)).val : ℤ) = (f n).val+1 := by exact_mod_cast ht
      rw [he,ht']
      dsimp only [D]
      ring
    · have hh : f (n+1)-f n = -1 := by
        rw [hdelta,he,projection_neg,neg_div,div_self hv]
      have hh' : f n = f (n+1)+1 := by linear_combination -hh
      have ht := val_succ_of_ne_zero hp (f (n+1)) (f n) (hf n) hh'
      have ht' : ((f n).val : ℤ) = (f (n+1)).val+1 := by exact_mod_cast ht
      rw [he,mul_neg,Zsqrtd.im_neg,ht']
      dsimp only [D]
      ring
  have hform (n : ℕ) : (star u*(x n-x 0)).im = D*((f n).val-(f 0).val : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show star u*(x (n+1)-x 0) =
        star u*(x (n+1)-x n)+star u*(x n-x 0) by ring,Zsqrtd.im_add,hl,ih]
      ring
  intro n
  rw [hform,abs_mul]
  have hn := ZMod.val_lt (f n)
  have h0 := ZMod.val_lt (f 0)
  have hb : |((f n).val : ℤ)-(f 0).val| ≤ (p : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg D)

/-- The two directions may both be reversed arbitrarily. If a split-prime
projection kills just one of them, there is no injective prime walk. -/
theorem no_signed_direction_prime_walk {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (u v : GaussianInt) (hu0 : u ≠ 0)
    (hu : projection r u = 0) (hv : projection r v ≠ 0)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = u ∨ x (n+1)-x n = -u ∨
      x (n+1)-x n = v ∨ x (n+1)-x n = -v := by
  intro hstep
  let C : ℤ := max u.norm v.norm+1
  have hs (n : ℕ) : (x (n+1)-x n).norm < C := by
    rcases hstep n with he | he | he | he <;>
      simp only [he,Zsqrtd.norm_neg] <;> dsimp [C] <;> omega
  obtain ⟨N,hN⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
  let y : ℕ → GaussianInt := fun n => x (N+n)
  have hy : Function.Injective y := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hne (n : ℕ) : projection r (y n) ≠ 0 :=
    projection_nonzero hp r hr (hprime (N+n)) (hN _ (by omega))
  have hys (n : ℕ) : y (n+1)-y n = u ∨ y (n+1)-y n = -u ∨
      y (n+1)-y n = v ∨ y (n+1)-y n = -v := by
    simpa only [y,Nat.add_assoc] using hstep (N+n)
  have hstrip := signed_direction_strip hp r u v hu hv y hne hys
  let B : ℕ := (|(star u*v).im| *(p : ℤ)).toNat
  have hB : (B : ℤ) = |(star u*v).im| *(p : ℤ) := by
    dsimp [B]
    exact Int.toNat_of_nonneg (by positivity)
  obtain ⟨K,hK⟩ := UniformRationalStrip.uniform_prime_segment_bound
    (star u) (star_ne_zero.mpr hu0) C B
  have hbad : K < K := by
    apply hK y K hy.injOn
    · intro n _; exact hprime (N+n)
    · intro n _; simpa only [y,Nat.add_assoc] using hs (N+n)
    · intro n _; rw [hB]; exact hstrip n
  omega

/-- An explicit family, now allowing all four signs and arbitrary backtracking. -/
theorem no_signed_horizontal_prime_walk (K : ℕ) (hK : 2 ≤ K)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = ⟨K,1⟩ ∨ x (n+1)-x n = -(⟨K,1⟩ : GaussianInt) ∨
      x (n+1)-x n = ⟨K,-1⟩ ∨ x (n+1)-x n = -(⟨K,-1⟩ : GaussianInt) := by
  obtain ⟨p,hp,hp2,hpd⟩ := exists_odd_prime_dvd_square_add_one K hK
  letI : Fact p.Prime := ⟨hp⟩
  have he : (K : ZMod p)^2+1 = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff (K^2+1) p).mpr hpd
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one] using hh
  have hr : (-(K : ZMod p))^2 = -1 := by linear_combination he
  have hk : (K : ZMod p) ≠ 0 := by intro hh; simp [hh] at he
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp hh))
  apply no_signed_direction_prime_walk hp (-(K : ZMod p)) hr
    (⟨K,1⟩ : GaussianInt) (⟨K,-1⟩ : GaussianInt) _ _ _ x hx hprime
  · intro hh
    have := congrArg Zsqrtd.im hh
    norm_num at this
  · simp [projection]
  · have hh : projection (-(K : ZMod p)) (⟨K,-1⟩ : GaussianInt) =
        2*(K : ZMod p) := by
      simp only [projection,Int.cast_natCast,Int.cast_neg,Int.cast_one]
      ring
    rw [hh]
    exact mul_ne_zero htwo hk

#print axioms signed_direction_strip
#print axioms no_signed_direction_prime_walk
#print axioms no_signed_horizontal_prime_walk
end SignedDirectionObstruction
end Erdos952Investigation
