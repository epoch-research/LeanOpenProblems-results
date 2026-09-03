import Submission.AffinePrimePreservers

/-! Rigidity of congruence-preserving maps which preserve Gaussian primes.
The hypothesis holds for polynomial evaluation maps. This is a restriction on
possible transformations of the prime graph, not a solution of the moat problem. -/
namespace Erdos952Investigation
namespace CongruencePrimePreservers
set_option maxHeartbeats 0

/-- Preservation of every principal congruence. -/
def PreservesCongruences (f : GaussianInt → GaussianInt) : Prop :=
  ∀ z w : GaussianInt, z-w ∣ f z-f w

def Nonconstant (f : GaussianInt → GaussianInt) : Prop :=
  ∃ z w : GaussianInt, f z ≠ f w

lemma norm_le_of_dvd {a b : GaussianInt} (hb : b ≠ 0) (h : a ∣ b) :
    a.norm ≤ b.norm :=
  Int.le_of_dvd (GaussianInt.norm_pos.mpr hb)
    (map_dvd (Zsqrtd.normMonoidHom (d := -1)) h)

lemma finite_fibers {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (hn : Nonconstant f) (c : GaussianInt) :
    {z | f z = c}.Finite := by
  obtain ⟨u,v,huv⟩ := hn
  have hw : ∃ w : GaussianInt, f w ≠ c := by
    by_cases hu : f u = c
    · exact ⟨v,fun hv => huv (hu.trans hv.symm)⟩
    · exact ⟨u,hu⟩
  obtain ⟨w,hw⟩ := hw
  have he : c-f w ≠ 0 := sub_ne_zero.mpr hw.symm
  apply ((norm_sublevel_finite (c-f w).norm).preimage
    (f := fun z : GaussianInt => z-w) sub_left_injective.injOn).subset
  intro z hz
  change f z = c at hz
  exact norm_le_of_dvd he (by simpa only [hz] using hc z w)

lemma natural_images_escape {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (hn : Nonconstant f) (B : ℤ) :
    ∃ T : ℕ, ∀ n ≥ T, B < (f (n : GaussianInt)).norm := by
  have hZ : {z : GaussianInt | (f z).norm ≤ B}.Finite :=
    (norm_sublevel_finite B).preimage' (fun w _ => finite_fibers hc hn w)
  have hN : {n : ℕ | (f (n : GaussianInt)).norm ≤ B}.Finite :=
    hZ.preimage (f := fun n : ℕ => (n : GaussianInt)) Nat.cast_injective.injOn
  obtain ⟨T,hT⟩ := hN.bddAbove
  refine ⟨T+1,?_⟩
  intro n hn
  by_contra! hbad
  have hh := hT hbad
  omega

lemma exists_large_inert_prime (M : ℕ) :
    ∃ p : ℕ, M < p ∧ p.Prime ∧ Prime (p : GaussianInt) ∧ p % 4 = 3 := by
  obtain ⟨p,hpM,hp,hp4⟩ := Nat.forall_exists_prime_gt_and_modEq M
    (by decide : 4 ≠ 0) (by decide : Nat.Coprime 3 4)
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hpM,hp,(GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mpr hp4,hp4⟩

/-- Nonconstant congruence-preserving prime-preservers must fix zero. -/
theorem preserver_zero {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (hn : Nonconstant f)
    (hp : ∀ z : GaussianInt, Prime z → Prime (f z)) : f 0 = 0 := by
  by_contra hb
  obtain ⟨p,hpB,hpP,hpG,hp4⟩ := exists_large_inert_prime (f 0).norm.natAbs
  let q : GaussianInt := f p
  have hq : Prime q := hp p hpG
  have hqpos : 0 < q.norm := GaussianInt.norm_pos.mpr hq.ne_zero
  have hqNat : 0 < q.norm.natAbs := Int.natAbs_pos.mpr hqpos.ne'
  have hdp : (p : GaussianInt) ∣ f p-f 0 := by simpa using hc p 0
  obtain ⟨d,hd⟩ := hdp
  have heq : f p = (p : GaussianInt)*d+f 0 := eq_add_of_sub_eq hd
  have hpcop : p.Coprime q.norm.natAbs := by
    apply hpP.coprime_iff_not_dvd.mpr
    intro hdiv
    have hdiv' : (p : ℤ) ∣ q.norm := by
      have hh : (p : ℤ) ∣ (q.norm.natAbs : ℤ) := by exact_mod_cast hdiv
      simpa only [GaussianInt.natCast_natAbs_norm] using hh
    have he : (q.norm : ZMod p) = ((f 0).norm : ZMod p) := by
      dsimp [q]
      rw [heq]
      simp [gaussian_norm_sq]
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd q.norm p).mpr hdiv'
    rw [he] at hh
    have hbdiv : (p : ℤ) ∣ (f 0).norm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hh
    have hle : (p : ℤ) ≤ (f 0).norm := Int.le_of_dvd (GaussianInt.norm_pos.mpr hb) hbdiv
    have hlt : ((f 0).norm.natAbs : ℤ) < p := by exact_mod_cast hpB
    rw [GaussianInt.natCast_natAbs_norm] at hlt
    omega
  have hp4' : p ≡ 3 [MOD 4] := hp4
  have hpcop4 : p.Coprime 4 :=
    IsolatedGaussianPrimes.coprime_of_modEq hp4' (by decide)
  obtain ⟨T,hT⟩ := natural_images_escape hc hn q.norm
  obtain ⟨r,hrT,hrP,hrp⟩ := Nat.forall_exists_prime_gt_and_modEq T
    (by positivity : 4*q.norm.natAbs ≠ 0) (hpcop4.mul_right hpcop)
  have hr4 : r % 4 = 3 :=
    (hrp.of_dvd (dvd_mul_right 4 q.norm.natAbs)).trans hp4'
  letI : Fact r.Prime := ⟨hrP⟩
  have hrG : Prime (r : GaussianInt) :=
    (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime r).mpr hr4
  have hmod : r ≡ p [MOD q.norm.natAbs] := hrp.of_dvd (dvd_mul_left q.norm.natAbs 4)
  have hmodZ : (r : ℤ) ≡ (p : ℤ) [ZMOD q.norm.natAbs] := Int.natCast_modEq_iff.mpr hmod
  have hdiff : (q.norm.natAbs : ℤ) ∣ (r : ℤ)-(p : ℤ) := Int.modEq_iff_dvd.mp hmodZ.symm
  have hdiffG : (q.norm.natAbs : GaussianInt) ∣ (r : GaussianInt)-(p : GaussianInt) := by
    simpa using map_dvd (Int.castRingHom GaussianInt) hdiff
  have hqd : q ∣ (q.norm.natAbs : GaussianInt) := by
    rw [GaussianInt.natCast_natAbs_norm,Zsqrtd.norm_eq_mul_conj]
    exact dvd_mul_right q (star q)
  have hdiv : q ∣ f (r : GaussianInt) := by
    have hh := dvd_add ((hqd.trans hdiffG).trans (hc r p)) (dvd_refl q)
    simpa only [q,sub_add_cancel] using hh
  have hqone : 1 < q.norm := by
    have hne : q.norm ≠ 1 := by
      intro hh
      exact hq.not_unit ((Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) q).mp hh)
    omega
  exact not_prime_of_small_divisor hdiv hqone (hT r hrT.le) (hp r hrG)

lemma prime_image_unit_multiple {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (h0 : f 0 = 0)
    (hp : ∀ z : GaussianInt, Prime z → Prime (f z))
    {z : GaussianInt} (hz : Prime z) :
    ∃ u : GaussianInt, IsUnit u ∧ f z = u*z := by
  have hd : z ∣ f z := by simpa [h0] using hc z 0
  obtain ⟨u,hu⟩ := hd
  have hunit : IsUnit u := ((hp z hz).irreducible.isUnit_or_isUnit hu).resolve_left hz.not_unit
  exact ⟨u,hunit,hu.trans (mul_comm _ _)⟩

/-- Fixing zero, congruence preservation and preservation of primes already
force a single unit multiplier on the entire Gaussian lattice. -/
theorem zero_preserver_rigidity {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (h0 : f 0 = 0)
    (hp : ∀ z : GaussianInt, Prime z → Prime (f z)) :
    ∃ u : GaussianInt, IsUnit u ∧ ∀ z : GaussianInt, f z = u*z := by
  obtain ⟨B,hB⟩ := ((norm_sublevel_finite 1).image
    (fun u : GaussianInt => (u-f 1).norm)).bddAbove
  have hunitBound (u : GaussianInt) (hu : IsUnit u) : (u-f 1).norm ≤ B := by
    have hn : u.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
    exact hB ⟨u,hn.le,rfl⟩
  have hi : Function.Injective (fun n : ℕ => (n : GaussianInt)-1) :=
    sub_left_injective.comp Nat.cast_injective
  obtain ⟨T,hT⟩ := injective_escapes_norm (fun n : ℕ => (n : GaussianInt)-1) hi B
  have hlargePrime (p : ℕ) (hpT : T ≤ p) (hpG : Prime (p : GaussianInt)) :
      IsUnit (f 1) ∧ f (p : GaussianInt) = f 1*(p : GaussianInt) := by
    obtain ⟨u,hu,hfu⟩ := prime_image_unit_multiple hc h0 hp hpG
    have hd : (p : GaussianInt)-1 ∣ u-f 1 := by
      have hh := dvd_sub (hc p 1) (dvd_mul_left ((p : GaussianInt)-1) u)
      have he : (f (p : GaussianInt)-f 1)-u*((p : GaussianInt)-1) = u-f 1 := by
        rw [hfu]
        ring
      rwa [he] at hh
    have he : u = f 1 := by
      by_contra hne
      have hsmall := norm_le_of_dvd (sub_ne_zero.mpr hne) hd
      have hbound := hunitBound u hu
      have hlarge := hT p hpT
      omega
    exact ⟨he ▸ hu,by simpa [he] using hfu⟩
  obtain ⟨p,hpT,_,hpG,_⟩ := exists_large_inert_prime T
  refine ⟨f 1,(hlargePrime p hpT.le hpG).1,?_⟩
  intro z
  by_contra hne
  have hnonzero : f z-f 1*z ≠ 0 := sub_ne_zero.mpr hne
  have hiz : Function.Injective (fun n : ℕ => z-(n : GaussianInt)) :=
    sub_right_injective.comp Nat.cast_injective
  obtain ⟨L,hL⟩ := injective_escapes_norm (fun n : ℕ => z-(n : GaussianInt)) hiz (f z-f 1*z).norm
  obtain ⟨r,hr,_,hrG,_⟩ := exists_large_inert_prime (max T L)
  have hfr := (hlargePrime r ((le_max_left _ _).trans hr.le) hrG).2
  have hd : z-(r : GaussianInt) ∣ f z-f 1*z := by
    have hh := dvd_sub (hc z r) (dvd_mul_left (z-(r : GaussianInt)) (f 1))
    have he : (f z-f (r : GaussianInt))-f 1*(z-(r : GaussianInt)) = f z-f 1*z := by
      rw [hfr]
      ring
    rwa [he] at hh
  have hsmall := norm_le_of_dvd hnonzero hd
  have hlarge := hL r ((le_max_right _ _).trans hr.le)
  omega

/-- Complete classification of congruence-preserving prime-preservers. -/
theorem prime_preserver_classification {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) :
    (∀ z : GaussianInt, Prime z → Prime (f z)) ↔
      (∃ c : GaussianInt, Prime c ∧ ∀ z : GaussianInt, f z = c) ∨
      (∃ u : GaussianInt, IsUnit u ∧ ∀ z : GaussianInt, f z = u*z) := by
  constructor
  · intro hp
    by_cases hn : Nonconstant f
    · exact Or.inr (zero_preserver_rigidity hc (preserver_zero hc hn hp) hp)
    · have hconst (z : GaussianInt) : f z = f 0 := by
        by_contra hz
        exact hn ⟨z,0,hz⟩
      exact Or.inl ⟨f 0,by simpa only [hconst 3] using hp 3 gaussian_prime_three,hconst⟩
  · rintro (⟨c,hc,hf⟩ | ⟨u,hu,hf⟩) z hz
    · rw [hf]
      exact hc
    · rw [hf]
      exact prime_mul_iff.mpr (Or.inr ⟨hu,hz⟩)

theorem nonconstant_prime_preserver_norm_difference {f : GaussianInt → GaussianInt}
    (hc : PreservesCongruences f) (hn : Nonconstant f)
    (hp : ∀ z : GaussianInt, Prime z → Prime (f z)) (z w : GaussianInt) :
    (f w-f z).norm = (w-z).norm := by
  obtain ⟨u,hu,hf⟩ := zero_preserver_rigidity hc (preserver_zero hc hn hp) hp
  have hn : u.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) u).mpr hu
  rw [hf w,hf z,← mul_sub,Zsqrtd.norm_mul,hn,one_mul]

/-- Polynomial maps preserving all Gaussian primes are constant prime maps or
unit multiples of `X`; nonlinear polynomial maps do not give prime-preserving
changes of scale. -/
theorem polynomial_prime_preservers (P : Polynomial GaussianInt) :
    (∀ z : GaussianInt, Prime z → Prime (P.eval z)) ↔
      (∃ c : GaussianInt, Prime c ∧ P = Polynomial.C c) ∨
      (∃ u : GaussianInt, IsUnit u ∧ P = Polynomial.C u*Polynomial.X) := by
  have hCong : PreservesCongruences (fun z : GaussianInt => P.eval z) :=
    fun z w => Polynomial.sub_dvd_eval_sub z w P
  rw [prime_preserver_classification hCong]
  constructor
  · rintro (⟨c,hPrime,hf⟩ | ⟨u,hu,hf⟩)
    · exact Or.inl ⟨c,hPrime,Polynomial.funext (fun z => by simpa using hf z)⟩
    · exact Or.inr ⟨u,hu,Polynomial.funext (fun z => by simpa using hf z)⟩
  · rintro (⟨c,hPrime,rfl⟩ | ⟨u,hu,rfl⟩)
    · exact Or.inl ⟨c,hPrime,fun z => by simp⟩
    · exact Or.inr ⟨u,hu,fun z => by simp⟩

#print axioms finite_fibers
#print axioms preserver_zero
#print axioms prime_preserver_classification
#print axioms nonconstant_prime_preserver_norm_difference
#print axioms polynomial_prime_preservers
end CongruencePrimePreservers
end Erdos952Investigation
