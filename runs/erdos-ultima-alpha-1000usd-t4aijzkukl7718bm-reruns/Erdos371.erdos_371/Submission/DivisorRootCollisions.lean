import FormalConjecturesUtil
import Submission.UnboundedPrimeDeletionLocal

/-! Arbitrarily large collisions for a divisor-root reduction, even when the
source cofactors have arbitrarily many distinct prime factors. This concerns
only the specified root construction, not all favorable targets or Erdős 371. -/

namespace Erdos371DivisorRootCollisions

open Finset Erdos371PrimeDeletionLocal Erdos371UnboundedPrimeDeletionLocal
abbrev P := Nat.maxPrimeFac

/-- Choose a nontrivial divisor of the cofactor and its least positive inverse
modulo the input's largest prime. The product is the reduced center. -/
def RootReduction (q c b : ℕ) : Prop :=
  ∃ d t : ℕ, d∣c ∧ 1<d ∧ 0<t ∧ t<q ∧ b=d*t ∧ q∣b-1

lemma rootReduction_iff {q c b : ℕ} (hq : q.Prime) (hc : 1<c)
    (hcq : c<q) (hdiv : c∣q+1) : RootReduction q c b ↔ b=q+1 := by
  constructor
  · rintro ⟨d,t,hdc,hd,ht,htq,hb,hqb⟩
    have hdq : d<q := (Nat.le_of_dvd (by omega : 0<c) hdc).trans_lt hcq
    have hdd : d∣q+1 := hdc.trans hdiv
    let u := (q+1)/d
    have hdu : d*u=q+1 := Nat.mul_div_cancel' hdd
    have hu : 0<u := Nat.div_pos (Nat.le_of_dvd (by omega : 0<q+1) hdd) (by omega)
    have huq : u<q := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr
      nlinarith [hq.two_le]
    have hcop : q.Coprime d := hq.coprime_iff_not_dvd.mpr (by
      intro h
      exact (not_le_of_gt hdq) (Nat.le_of_dvd (by omega : 0<d) h))
    have htm : 1 ≡ d*t [MOD q] :=
      (Nat.modEq_iff_dvd' (by nlinarith : 1≤d*t)).mpr (by simpa [hb] using hqb)
    have hum : d*u ≡ 1 [MOD q] := by
      rw [hdu]
      simp [Nat.ModEq]
    have htu : t=u :=
      (Nat.ModEq.cancel_left_of_coprime hcop (htm.symm.trans hum.symm)).eq_of_lt_of_lt htq huq
    rw [hb,htu,hdu]
  · rintro rfl
    refine ⟨c,(q+1)/c,dvd_refl _,hc,?_,?_,?_,?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega : 0<q+1) hdiv) (by omega)
    · apply (Nat.div_lt_iff_lt_mul (by omega : 0<c)).mpr
      nlinarith [hq.two_le]
    · exact (Nat.mul_div_cancel' hdiv).symm
    · simp

lemma no_distinct_root_targets {q c d : ℕ} (hq : q.Prime)
    (hc : 1<c) (hd : 1<d) (hcq : c<q) (hdq : d<q)
    (hcv : c∣q+1) (hdv : d∣q+1) :
    ¬ ∃ b e : ℕ, b≠e ∧ RootReduction q c b ∧ RootReduction q d e := by
  rintro ⟨b,e,hne,hb,he⟩
  exact hne (((rootReduction_iff hq hc hcq hcv).mp hb).trans
    ((rootReduction_iff hq hd hdq hdv).mp he).symm)

lemma predecessor_factor {r q : ℕ} (hr : 2≤r) (hd : r∣q+1) :
    r∣(r-1)*q-1 := by
  have he : (r-1)*q+q=r*q := by
    have hh : r-1+1=r := by omega
    nlinarith
  have hsub : r*q-(q+1)=(r-1)*q-1 := by omega
  exact hsub ▸ Nat.dvd_sub (dvd_mul_right r q) hd

/-- The cofactors can be fixed first, and the collision prime can then be
chosen beyond any prescribed bound. -/
lemma collision_parameters (K : ℕ) :
    ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ 2<r ∧ r<s ∧
      K≤(r-1).primeFactors.card ∧ K≤(s-1).primeFactors.card ∧
      ∀ N : ℕ, ∃ q : ℕ, N<q ∧ s<q ∧ q.Prime ∧
        r∣q+1 ∧ r-1∣q+1 ∧ s∣q+1 ∧ s-1∣q+1 := by
  obtain ⟨r,hr,hr2,hKr⟩ := exists_prime_with_many_factors_predecessor K
  have hc : r-1≠0 := by omega
  obtain ⟨s,hrs,hs,hsm⟩ := Nat.forall_exists_prime_gt_and_modEq r
    (q := r-1) (a := 1) hc (Nat.coprime_one_left (r-1))
  have hcd : r-1∣s-1 := (Nat.modEq_iff_dvd' (by omega : 1≤s)).mp hsm.symm
  have hKs : K≤(s-1).primeFactors.card :=
    hKr.trans (card_le_card (Nat.primeFactors_mono hcd (by omega)))
  refine ⟨r,s,hr,hs,hr2,hrs,hKr,hKs,?_⟩
  intro N
  let M := (r*(r-1))*(s*(s-1))
  have hM : M≠0 := by
    dsimp [M]
    exact mul_ne_zero (mul_ne_zero hr.ne_zero hc) (mul_ne_zero hs.ne_zero (by omega))
  have hM1 : 1≤M := Nat.one_le_iff_ne_zero.mpr hM
  have hcop : (M-1).Coprime M :=
    (Nat.coprime_self_sub_left hM1).mpr (Nat.coprime_one_left M)
  obtain ⟨q,hqN,hq,hqm⟩ := Nat.forall_exists_prime_gt_and_modEq (max N s)
    (q := M) (a := M-1) hM hcop
  have hmod := hqm.add_right 1
  rw [Nat.sub_add_cancel hM1] at hmod
  have hdM : M∣q+1 := Nat.modEq_zero_iff_dvd.mp
    (hmod.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl M)))
  have hrM : r*(r-1)∣M := dvd_mul_right _ _
  have hsM : s*(s-1)∣M := dvd_mul_left _ _
  refine ⟨q,(le_max_left _ _).trans_lt hqN,(le_max_right _ _).trans_lt hqN,hq,?_,?_,?_,?_⟩
  · exact ((dvd_mul_right r (r-1)).trans hrM).trans hdM
  · exact ((dvd_mul_left (r-1) r).trans hrM).trans hdM
  · exact ((dvd_mul_right s (s-1)).trans hsM).trans hdM
  · exact ((dvd_mul_left (s-1) s).trans hsM).trans hdM

lemma source_primeFactors_card {q c : ℕ} (hq : q.Prime) (hc : 0<c) (hcq : c<q) :
    (c*q).primeFactors.card=c.primeFactors.card+1 := by
  have hnot : q∉c.primeFactors := by
    intro h
    exact (not_le_of_gt hcq) (Nat.le_of_mem_primeFactors h)
  have he : (c*q).primeFactors=insert q c.primeFactors := by
    rw [Nat.primeFactors_mul hc.ne' hq.ne_zero,hq.primeFactors]
    ext t
    simp
  simp [he,hnot]

/-- These collisions persist beyond every cutoff and every fixed bound on
source factor count. Only divisor-root targets are being restricted. -/
theorem arbitrarily_large_collisions (K N : ℕ) :
    ∃ q c d : ℕ, q.Prime ∧ N<q ∧ 1<c ∧ c<d ∧ d<q ∧
      K≤c.primeFactors.card ∧ K≤d.primeFactors.card ∧
      K+1≤(c*q).primeFactors.card ∧ K+1≤(d*q).primeFactors.card ∧
      P (c*q)=q ∧ P (d*q)=q ∧ P (c*q-1)<q ∧ P (d*q-1)<q ∧
      P (q+1)<P q ∧ RootReduction q c (q+1) ∧ RootReduction q d (q+1) ∧
      ¬ ∃ b e : ℕ, b≠e ∧ RootReduction q c b ∧ RootReduction q d e := by
  obtain ⟨r,s,hr,hs,hr2,hrs,hKr,hKs,hqex⟩ := collision_parameters K
  obtain ⟨q,hqN,hsq,hq,hrv,hcv,hsv,hdv⟩ := hqex N
  have hc : 1<r-1 := by omega
  have hd : 1<s-1 := by omega
  have hcq : r-1<q := by omega
  have hdq : s-1<q := by omega
  have hq2 : 2<q := by omega
  have hpc : P ((r-1)*q)=q := height_of_small_mul (by omega) hcq.le hq
  have hpd : P ((s-1)*q)=q := height_of_small_mul (by omega) hdq.le hq
  have hmc := (height_bounds_of_prime_dvd (a := r-1) (by omega) (by omega)
    hr (hrs.trans hsq) (predecessor_factor hr.two_le hrv)).2
  have hmd := (height_bounds_of_prime_dvd (a := s-1) (by omega) (by omega)
    hs hsq (predecessor_factor hs.two_le hsv)).2
  refine ⟨q,r-1,s-1,hq,hqN,hc,by omega,hdq,hKr,hKs,?_,?_,hpc,hpd,hmc,hmd,?_,?_,?_,?_⟩
  · rw [source_primeFactors_card hq (by omega) hcq]
    omega
  · rw [source_primeFactors_card hq (by omega) hdq]
    omega
  · simpa only [P,hq.maxPrimeFac_eq_self] using Erdos371PrimeDiscrepancy.after_odd_prime hq hq2
  · exact (rootReduction_iff hq hc hcq hcv).mpr rfl
  · exact (rootReduction_iff hq hd hdq hdv).mpr rfl
  · exact no_distinct_root_targets hq hc hd hcq hdq hcv hdv

end Erdos371DivisorRootCollisions

#print axioms Erdos371DivisorRootCollisions.rootReduction_iff
#print axioms Erdos371DivisorRootCollisions.arbitrarily_large_collisions
