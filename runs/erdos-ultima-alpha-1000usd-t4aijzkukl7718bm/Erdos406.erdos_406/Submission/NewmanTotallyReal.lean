import Submission.NewmanSmallFactors

/-! A degree-independent restriction on totally real monic factors.
This does not bound the degrees of nonreal factors and does not settle Erdős 406. -/
namespace Erdos406TotallyReal
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
  Erdos406SmallFactors

lemma norm_multiset_prod_le_one (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ ≤ 1) :
    ‖s.prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have hz := hs z (by simp)
    have ht := ih (fun a ha => hs a (by simp [ha]))
    nlinarith [norm_nonneg z, norm_nonneg s.prod]

lemma norm_multiset_prod_lt_one (s : Multiset ℂ) (hne : s ≠ 0)
    (hs : ∀ z ∈ s, ‖z‖ < 1) : ‖s.prod‖ < 1 := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | @cons z s ih =>
    rw [Multiset.prod_cons, norm_mul]
    have hz := hs z (by simp)
    have ht := norm_multiset_prod_le_one s (fun a ha => (hs a (by simp [ha])).le)
    nlinarith [norm_nonneg z, norm_nonneg s.prod]

/-- An integer evaluation of a monic polynomial vanishes if all its roots
lie in the open unit disk centered at that integer. -/
lemma eval_eq_zero_of_roots_in_disk (Q : ℤ[X]) (hQ : Q.Monic)
    (hdeg : 0 < Q.natDegree) (a : ℤ)
    (hr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖(a : ℂ) - z‖ < 1) :
    Q.eval a = 0 := by
  have hs := IsAlgClosed.splits (Q.map (Int.castRingHom ℂ))
  have he : (Q.map (Int.castRingHom ℂ)).eval (a : ℂ) = ((Q.eval a : ℤ) : ℂ) := by
    rw [eval_map]
    exact eval₂_at_apply (Int.castRingHom ℂ) a
  have hb : ‖((Q.eval a : ℤ) : ℂ)‖ < 1 := by
    rw [← he, hs.eval_eq_prod_roots_of_monic (hQ.map _)]
    apply norm_multiset_prod_lt_one
    · intro hh
      have hc : 0 < ((Q.map (Int.castRingHom ℂ)).roots.map
          (fun z => (a : ℂ) - z)).card := by
        rw [Multiset.card_map, ← hs.natDegree_eq_card_roots, hQ.natDegree_map]
        exact hdeg
      simp [hh] at hc
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz
      exact hr w hw
  rw [Complex.norm_intCast] at hb
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast hb)

/-- The only monic integer polynomials with all roots in the open unit disk
centered at an integer a are powers of X-a. -/
theorem eq_pow_of_roots_in_disk (Q : ℤ[X]) (hQ : Q.Monic) (a : ℤ)
    (hr : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, ‖(a : ℂ) - z‖ < 1) :
    Q = (X - C a) ^ Q.natDegree := by
  induction hn : Q.natDegree using Nat.strong_induction_on generalizing Q with
  | h n ih =>
    by_cases hn0 : n = 0
    · have hd : Q.natDegree = 0 := hn.trans hn0
      rw [hn0, pow_zero]
      exact hQ.natDegree_eq_zero.mp hd
    · have hp : 0 < Q.natDegree := by omega
      have hz := eval_eq_zero_of_roots_in_disk Q hQ hp a hr
      obtain ⟨R, he⟩ := (dvd_iff_isRoot (a := a) (p := Q)).mpr hz
      have hR : R.Monic := (monic_X_sub_C a).of_mul_monic_left (he ▸ hQ)
      have hd : Q.natDegree = 1 + R.natDegree := by
        rw [he, natDegree_mul (monic_X_sub_C a).ne_zero hR.ne_zero, natDegree_X_sub_C]
      have hRr : ∀ z ∈ (R.map (Int.castRingHom ℂ)).roots, ‖(a : ℂ) - z‖ < 1 := by
        intro z hz
        apply hr z
        apply (mem_roots (hQ.map _).ne_zero).mpr
        have hz' := (mem_roots (hR.map _).ne_zero).mp hz
        change (R.map (Int.castRingHom ℂ)).eval z = 0 at hz'
        change (Q.map (Int.castRingHom ℂ)).eval z = 0
        rw [he, Polynomial.map_mul, eval_mul, hz', mul_zero]
      have hi := ih R.natDegree (by omega) R hR hRr rfl
      have hn' : n = R.natDegree + 1 := by omega
      rw [he, hi, hn', pow_succ']

/-- Every totally real monic factor of a candidate is a power of X+1.
There is no degree bound or total-reality assertion for the other factors. -/
theorem candidate_totally_real_factor (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k)))
    (hreal : ∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, z.im = 0) :
    Q = (X + 1) ^ Q.natDegree := by
  have he := eq_pow_of_roots_in_disk Q hQ (-1) ?_
  · simpa using he
  intro z hz
  have hzi : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hreal z hz]
  have hroot := (mem_roots (hQ.map _).ne_zero).mp hz
  have hrealroot : (Q.map (Int.castRingHom ℝ)).eval z.re = 0 := by
    have hc := eval₂_at_apply Complex.ofRealHom z.re (p := Q.map (Int.castRingHom ℝ))
    rw [eval₂_map] at hc
    have hcomp : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := by
      ext n
      simp
    rw [hcomp] at hc
    change Q.eval₂ (Int.castRingHom ℂ) (z.re : ℂ) =
      (((Q.map (Int.castRingHom ℝ)).eval z.re : ℝ) : ℂ) at hc
    rw [hzi] at hc
    have hr : (Q.map (Int.castRingHom ℂ)).eval z = 0 := hroot
    rw [eval_map] at hr
    rw [hr] at hc
    exact Complex.ofReal_injective hc.symm
  have hneg : z.re < 0 := by
    by_contra hh
    have he := good_two_power_digits_head k hg
    have hd' := hd
    rw [he] at hd'
    have hp := factor_positive_on_ray _ Q hQ hd' z.re (le_of_not_gt hh)
    rw [hrealroot] at hp
    exact lt_irrefl _ hp
  have hb := candidate_factor_real_root_bound k hg Q hQ hd z.re hrealroot
  have hlo : -2 < z.re := (abs_lt.mp hb).1
  rw [← hzi]
  have hc : ((-1 : ℤ) : ℂ) - (z.re : ℂ) = ((-1 - z.re : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

#print axioms eq_pow_of_roots_in_disk
#print axioms candidate_totally_real_factor
end Erdos406TotallyReal
