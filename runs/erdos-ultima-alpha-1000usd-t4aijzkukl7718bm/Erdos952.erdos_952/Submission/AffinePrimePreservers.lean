import Submission.IsolatedGaussianPrimes
import Submission.FiniteCertificates

/-! Rigidity of affine maps preserving all Gaussian primes. This rules out
uniform affine changes of scale as a route from large jump bounds to small
ones; it does not settle the existence of a prime ray. -/
namespace Erdos952Investigation
namespace AffinePrimePreservers
set_option maxHeartbeats 0

/-- A nonconstant affine map with nonzero constant term takes arbitrarily
large inert rational primes to Gaussian nonprimes. -/
theorem arbitrarily_large_affine_counterexamples (a b : GaussianInt)
    (ha : a ≠ 0) (hb : b ≠ 0) (M : ℕ) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ Prime (p : GaussianInt) ∧
      ¬ Prime (a*(p : GaussianInt)+b) := by
  obtain ⟨p,hpT,hp,hp4⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max M b.norm.natAbs) (by decide : 4 ≠ 0) (by decide : Nat.Coprime 3 4)
  letI : Fact p.Prime := ⟨hp⟩
  have hpM : M < p := (le_max_left _ _).trans_lt hpT
  have hpG : Prime (p : GaussianInt) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp4
  by_cases hq : Prime (a*(p : GaussianInt)+b)
  · let q : GaussianInt := a*(p : GaussianInt)+b
    change Prime q at hq
    have hqpos : 0 < q.norm := GaussianInt.norm_pos.mpr hq.ne_zero
    have hqNat : 0 < q.norm.natAbs := Int.natAbs_pos.mpr hqpos.ne'
    have hpcop : p.Coprime q.norm.natAbs := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      have hd' : (p : ℤ) ∣ q.norm := by
        have hh : (p : ℤ) ∣ (q.norm.natAbs : ℤ) := by exact_mod_cast hd
        simpa only [GaussianInt.natCast_natAbs_norm] using hh
      have he : (q.norm : ZMod p) = (b.norm : ZMod p) := by
        simp [q,gaussian_norm_sq]
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd q.norm p).mpr hd'
      rw [he] at hz
      have hdb : (p : ℤ) ∣ b.norm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
      have hle : (p : ℤ) ≤ b.norm := Int.le_of_dvd (GaussianInt.norm_pos.mpr hb) hdb
      have hlt : b.norm.natAbs < p := (le_max_right _ _).trans_lt hpT
      have hlt' : (b.norm.natAbs : ℤ) < p := by exact_mod_cast hlt
      rw [GaussianInt.natCast_natAbs_norm] at hlt'
      omega
    have hpcop4 : p.Coprime 4 :=
      IsolatedGaussianPrimes.coprime_of_modEq hp4 (by decide)
    have hinj : Function.Injective (fun n : ℕ => a*(n : GaussianInt)+b) := by
      intro i j hij
      exact Nat.cast_injective (mul_left_cancel₀ ha (add_right_cancel hij))
    obtain ⟨T,hT⟩ := injective_escapes_norm (fun n : ℕ => a*(n : GaussianInt)+b) hinj q.norm
    obtain ⟨r,hrT,hr,hrp⟩ := Nat.forall_exists_prime_gt_and_modEq
      (max M T) (by positivity : 4*q.norm.natAbs ≠ 0) (hpcop4.mul_right hpcop)
    have hr4 : r % 4 = 3 :=
      (hrp.of_dvd (dvd_mul_right 4 q.norm.natAbs)).trans hp4
    letI : Fact r.Prime := ⟨hr⟩
    refine ⟨r,(le_max_left _ _).trans_lt hrT,hr,
      (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime r).mpr hr4,?_⟩
    have hmod : r ≡ p [MOD q.norm.natAbs] :=
      hrp.of_dvd (dvd_mul_left q.norm.natAbs 4)
    have hmodZ : (r : ℤ) ≡ (p : ℤ) [ZMOD q.norm.natAbs] :=
      Int.natCast_modEq_iff.mpr hmod
    have hdiff : (q.norm.natAbs : ℤ) ∣ (r : ℤ)-(p : ℤ) :=
      Int.modEq_iff_dvd.mp hmodZ.symm
    have hdiffG : (q.norm.natAbs : GaussianInt) ∣ (r : GaussianInt)-(p : GaussianInt) := by
      have hh := map_dvd (Int.castRingHom GaussianInt) hdiff
      simpa using hh
    have hqd : q ∣ (q.norm.natAbs : GaussianInt) := by
      rw [GaussianInt.natCast_natAbs_norm,Zsqrtd.norm_eq_mul_conj]
      exact dvd_mul_right q (star q)
    have hdiv : q ∣ a*(r : GaussianInt)+b := by
      have he : a*(r : GaussianInt)+b = a*((r : GaussianInt)-(p : GaussianInt))+q := by
        dsimp [q]
        ring
      rw [he]
      exact dvd_add (dvd_mul_of_dvd_right (hqd.trans hdiffG) a) (dvd_refl q)
    have hqone : 1 < q.norm := by
      have hne : q.norm ≠ 1 := by
        intro hh
        exact hq.not_unit ((Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) q).mp hh)
      omega
    exact not_prime_of_small_divisor hdiv hqone
      (hT r ((le_max_right _ _).trans hrT.le))
  · exact ⟨p,hpM,hp,hpG,hq⟩

/-- Nonconstant affine prime-preservers are exactly multiplication by a unit. -/
theorem nonconstant_affine_preserves_primes_iff (a b : GaussianInt) (ha : a ≠ 0) :
    (∀ z : GaussianInt, Prime z → Prime (a*z+b)) ↔ b = 0 ∧ IsUnit a := by
  constructor
  · intro h
    have hb : b = 0 := by
      by_contra hb
      obtain ⟨p,_,_,hp,hbad⟩ := arbitrarily_large_affine_counterexamples a b ha hb 0
      exact hbad (h p hp)
    refine ⟨hb,?_⟩
    have hh : Prime (a*(3 : GaussianInt)) := by simpa [hb] using h 3 gaussian_prime_three
    exact (hh.irreducible.isUnit_or_isUnit rfl).resolve_right gaussian_prime_three.not_unit
  · rintro ⟨rfl,hu⟩ z hz
    simpa using prime_mul_iff.mpr (Or.inr ⟨hu,hz⟩)

/-- Including constant maps gives a complete affine classification. -/
theorem affine_preserves_primes_iff (a b : GaussianInt) :
    (∀ z : GaussianInt, Prime z → Prime (a*z+b)) ↔
      (a = 0 ∧ Prime b) ∨ (b = 0 ∧ IsUnit a) := by
  by_cases ha : a = 0
  · subst a
    constructor
    · intro h
      exact Or.inl ⟨rfl,by simpa using h 3 gaussian_prime_three⟩
    · rintro (⟨_,hb⟩ | ⟨_,ha⟩) z hz
      · simpa using hb
      · exact (not_isUnit_zero ha).elim
  · rw [nonconstant_affine_preserves_primes_iff a b ha]
    simp [ha]

/-- In particular, a nonconstant affine prime-preserver does not shrink any
squared distance. No primality-preserving affine contraction is available. -/
theorem prime_preserving_affine_norm_difference (a b : GaussianInt) (ha : a ≠ 0)
    (h : ∀ z : GaussianInt, Prime z → Prime (a*z+b)) (z w : GaussianInt) :
    ((a*w+b)-(a*z+b)).norm = (w-z).norm := by
  obtain ⟨_,hu⟩ := (nonconstant_affine_preserves_primes_iff a b ha).mp h
  have hn : a.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) a).mpr hu
  have he : (a*w+b)-(a*z+b) = a*(w-z) := by ring
  rw [he,Zsqrtd.norm_mul,hn,one_mul]

#print axioms arbitrarily_large_affine_counterexamples
#print axioms affine_preserves_primes_iff
#print axioms prime_preserving_affine_norm_difference
end AffinePrimePreservers
end Erdos952Investigation
