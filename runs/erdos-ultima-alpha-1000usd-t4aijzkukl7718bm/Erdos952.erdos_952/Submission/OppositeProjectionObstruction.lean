import Submission.TwoIncrementObstruction
import Submission.RationalStripObstruction

/-! A further restricted-step obstruction. Opposite nonzero split-prime
projections force the signed increment count into a bounded interval. This
confines a two-increment prime walk to a rational strip. It does not cover
arbitrary bounded sets of increments. -/
namespace Erdos952Investigation.OppositeProjectionObstruction
open TwoIncrementObstruction RationalStrip
set_option maxHeartbeats 0

lemma val_succ_without_zero {p : ℕ} (hp : p.Prime) (s t : ZMod p)
    (ht : t ≠ 0) (he : t = s+1) : t.val = s.val+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hs := ZMod.val_lt s
  have hv : t.val = (s.val+1)%p := by rw [he,ZMod.val_add,ZMod.val_one]
  have ht0 : t.val ≠ 0 := by
    intro hh
    apply ht
    apply ZMod.val_injective
    simpa using hh
  have hb : s.val+1 < p := by
    by_contra h
    have hh : s.val+1 = p := by omega
    rw [hh,Nat.mod_self] at hv
    exact ht0 hv
  rwa [Nat.mod_eq_of_lt hb] at hv

/-- A nearest-neighbor lift of a nonzero modular walk cannot cross a deleted
residue. The linear coordinate therefore stays within one modular interval. -/
lemma aligned_coordinate_bound {p : ℕ} (hp : p.Prime)
    (f : ℕ → ZMod p) (A : ℕ → ℤ) (t : ℤ) (hf : ∀ n, f n ≠ 0)
    (hs : ∀ n,
      (f (n+1) = f n+1 ∧ A (n+1) = A n+t) ∨
      (f (n+1)+1 = f n ∧ A (n+1) = A n-t)) :
    ∀ n, |A n-A 0| ≤ |t| * (p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hform (n : ℕ) : A n-A 0 = t*((f n).val-(f 0).val : ℤ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rcases hs n with ⟨h,hA⟩ | ⟨h,hA⟩
      · have hv := val_succ_without_zero hp (f n) (f (n+1)) (hf (n+1)) h
        rw [hA,hv]
        push_cast
        linear_combination ih
      · have hv := val_succ_without_zero hp (f (n+1)) (f n) (hf n) h.symm
        have hv' : ((f n).val : ℤ) = (f (n+1)).val+1 := by exact_mod_cast hv
        rw [hA]
        linear_combination ih+t*hv'
  intro n
  rw [hform n,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
  have h0 := ZMod.val_lt (f 0)
  have hn := ZMod.val_lt (f n)
  rw [abs_le]
  constructor <;> omega

lemma exists_normal (w : GaussianInt) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ a*w.re+b*w.im = 0 := by
  by_cases hw : w = 0
  · exact ⟨1,0,Or.inl one_ne_zero,by simp [hw]⟩
  · refine ⟨w.im,-w.re,?_,by ring⟩
    by_contra! h
    apply hw
    apply Zsqrtd.ext <;> simp_all

/-- In particular, a split prime dividing u+v but not u can supply the
hypotheses. No periodicity or recurrence of the choices is assumed. -/
theorem no_opposite_projection_prime_walk {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (u v : GaussianInt)
    (hu : projection r u ≠ 0) (hv : projection r v = -projection r u)
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = u ∨ x (n+1)-x n = v := by
  intro hs
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
  let y (n : ℕ) : GaussianInt := x (K+n)
  have hyinj : Function.Injective y := fun _ _ h => Nat.add_left_cancel (hx h)
  have hyprime (n : ℕ) : Prime (y n) := hprime (K+n)
  have hylarge (n : ℕ) : (p : ℤ)^2 < (y n).norm := hK _ (by omega)
  have hys (n : ℕ) : y (n+1)-y n = u ∨ y (n+1)-y n = v := by
    simpa only [y,Nat.add_assoc] using hs (K+n)
  obtain ⟨a,b,hab,habuv⟩ := exists_normal (u+v)
  let L (z : GaussianInt) : ℤ := a*z.re+b*z.im
  have hLsub (z w : GaussianInt) : L (z-w) = L z-L w := by
    simp only [L,Zsqrtd.re_sub,Zsqrtd.im_sub]; ring
  have hLuv : L v = -L u := by
    simp only [Zsqrtd.re_add,Zsqrtd.im_add] at habuv
    dsimp only [L]
    linear_combination habuv
  let f (n : ℕ) : ZMod p := projection r (y n)/projection r u
  have hf (n : ℕ) : f n ≠ 0 :=
    div_ne_zero (projection_nonzero hp r hr (hyprime n) (hylarge n)) hu
  have hfstep (n : ℕ) : f (n+1)-f n =
      projection r (y (n+1)-y n)/projection r u := by
    simp only [f,projection_sub,sub_div]
  have halign (n : ℕ) :
      (f (n+1) = f n+1 ∧ L (y (n+1)) = L (y n)+L u) ∨
      (f (n+1)+1 = f n ∧ L (y (n+1)) = L (y n)-L u) := by
    have hl : L (y (n+1))-L (y n) = L (y (n+1)-y n) := (hLsub _ _).symm
    rcases hys n with h | h
    · left
      have hh := hfstep n
      rw [h,div_self hu] at hh
      rw [h] at hl
      constructor
      · linear_combination hh
      · linear_combination hl
    · right
      have hh := hfstep n
      rw [h,hv,neg_div,div_self hu] at hh
      rw [h,hLuv] at hl
      constructor
      · linear_combination hh
      · linear_combination hl
  have hbound := aligned_coordinate_bound hp f (fun n => L (y n)) (L u) hf halign
  let C : ℤ := max u.norm v.norm+1
  have hyC (n : ℕ) : Prime (y n) ∧ (y (n+1)-y n).norm < C := by
    refine ⟨hyprime n,?_⟩
    rcases hys n with h | h
    · rw [h]; exact (le_max_left u.norm v.norm).trans_lt (lt_add_one _)
    · rw [h]; exact (le_max_right u.norm v.norm).trans_lt (lt_add_one _)
  apply not_in_rational_affine_strip y C hyinj hyC a b (L (y 0)) hab
  refine ⟨(L u).natAbs*p,?_⟩
  intro n
  simpa only [Nat.cast_mul,Int.natCast_natAbs,L] using hbound n

/-- An example where the new split prime17 divides the sum of the two
increments; it does not divide either increment. -/
theorem no_example_two_increment_ray (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = (⟨5,5⟩ : GaussianInt) ∨
      x (n+1)-x n = (⟨10,20⟩ : GaussianInt) := by
  exact no_opposite_projection_prime_walk (p := 17) (by norm_num)
    (13 : ZMod 17) (by decide +kernel) ⟨5,5⟩ ⟨10,20⟩
    (by decide +kernel) (by decide +kernel) x hx hp

#print axioms no_example_two_increment_ray
#print axioms aligned_coordinate_bound
#print axioms no_opposite_projection_prime_walk
end Erdos952Investigation.OppositeProjectionObstruction
