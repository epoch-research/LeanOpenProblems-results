import Submission.StripObstruction

/-! A computable Gaussian-primality decision procedure using a finite search
for proper Gaussian divisors. This is a decision procedure, not a statement
about the existence of bounded prime paths. -/
namespace Erdos952Investigation
namespace GaussianPrimeDecision
set_option maxHeartbeats 0

instance gaussianDvdDecidable : DecidableRel (fun a b : GaussianInt => a ∣ b) :=
  fun a b => decidable_of_iff (b % a = 0) EuclideanDomain.mod_eq_zero

lemma abs_im_le_norm (z : GaussianInt) : |z.im| ≤ z.norm := by
  have hs := Int.le_self_sq |z.im|
  rw [gaussian_norm_sq]
  nlinarith [sq_abs z.im,sq_nonneg z.re]

lemma norm_gt_one_of_nonunit {z : GaussianInt} (hz0 : z ≠ 0) (hzu : ¬ IsUnit z) :
    1 < z.norm := by
  have hp := GaussianInt.norm_pos.mpr hz0
  have hn : z.norm ≠ 1 := by
    intro hh
    exact hzu ((Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mp hh)
  omega

def point (z : GaussianInt) (r s : Fin (2*z.norm.natAbs+1)) : GaussianInt :=
  ⟨(r.val : ℤ)-(z.norm.natAbs : ℤ),(s.val : ℤ)-(z.norm.natAbs : ℤ)⟩

def PrimeTest (z : GaussianInt) : Prop :=
  1 < z.norm ∧ ∀ r s : Fin (2*z.norm.natAbs+1),
    ¬ (1 < (point z r s).norm ∧ (point z r s).norm < z.norm ∧ point z r s ∣ z)

instance (z : GaussianInt) : Decidable (PrimeTest z) :=
  inferInstanceAs (Decidable (_ ∧ ∀ r s : Fin (2*z.norm.natAbs+1), _))

theorem prime_iff_test (z : GaussianInt) : Prime z ↔ PrimeTest z := by
  constructor
  · intro hz
    refine ⟨norm_gt_one_of_nonunit hz.ne_zero hz.not_unit,?_⟩
    intro r s h
    exact not_prime_of_small_divisor h.2.2 h.1 h.2.1 hz
  · intro ht
    apply irreducible_iff_prime.mp
    refine ⟨?_,?_⟩
    · intro hu
      have he := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mpr hu
      have := ht.1
      omega
    · intro a b hab
      by_cases hau : IsUnit a
      · exact Or.inl hau
      by_cases hbu : IsUnit b
      · exact Or.inr hbu
      have hz0 : z ≠ 0 := by intro hh; have := ht.1; simp [hh] at this
      have ha0 : a ≠ 0 := by intro hh; apply hz0; simp [hab,hh]
      have hb0 : b ≠ 0 := by intro hh; apply hz0; simp [hab,hh]
      have ha := norm_gt_one_of_nonunit ha0 hau
      have hb := norm_gt_one_of_nonunit hb0 hbu
      have hn : z.norm = a.norm*b.norm := by rw [hab,Zsqrtd.norm_mul]
      have haz : a.norm < z.norm := by nlinarith
      have hB : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)
      have hrB := (abs_re_le_gaussian_norm a).trans haz.le
      have hiB := (abs_im_le_norm a).trans haz.le
      have hr := abs_le.mp hrB
      have hi := abs_le.mp hiB
      let r : Fin (2*z.norm.natAbs+1) := ⟨(a.re+(z.norm.natAbs : ℤ)).toNat,by omega⟩
      let s : Fin (2*z.norm.natAbs+1) := ⟨(a.im+(z.norm.natAbs : ℤ)).toNat,by omega⟩
      have he : point z r s = a := by
        apply Zsqrtd.ext <;> dsimp [point,r,s] <;> omega
      have hh := ht.2 r s
      rw [he] at hh
      exact (hh ⟨ha,haz,⟨b,hab⟩⟩).elim

instance gaussianPrimeDecidable : DecidablePred (fun z : GaussianInt => Prime z) :=
  fun z => decidable_of_iff (PrimeTest z) (prime_iff_test z).symm

#print axioms prime_iff_test

end GaussianPrimeDecision
end Erdos952Investigation
