import FormalConjecturesUtil
import Submission.PrimeDeletionLocal

/-! The local prime-deletion sums are unbounded in the unfavorable direction.
This does not refute a cumulative linear bound or the density conjecture. -/

namespace Erdos371UnboundedPrimeDeletionLocal

open Finset Erdos371PrimeDeletion Erdos371PrimeDeletionLocal

lemma height_bounds_of_prime_dvd {a r q : ℕ} (ha : 0 < a)
    (har : a < r) (hr : r.Prime) (hrq : r < q) (hd : r ∣ a*q-1) :
    r ≤ P (a*q-1) ∧ P (a*q-1) < q := by
  have hq : 1 < q := hr.one_lt.trans hrq
  have hprod : q ≤ a*q := by simpa using Nat.mul_le_mul_right q ha
  have hm : 0 < a*q-1 := by omega
  have ht : 0 < (a*q-1)/r := Nat.div_pos (Nat.le_of_dvd hm hd) hr.pos
  have htq : (a*q-1)/r < q := by
    apply (Nat.div_lt_iff_lt_mul hr.pos).mpr
    have hh := Nat.mul_lt_mul_of_pos_right har (by omega : 0 < q)
    exact (Nat.sub_le _ _).trans_lt (by simpa only [Nat.mul_comm] using hh)
  refine ⟨Nat.le_maxPrimeFac hm.ne' hr hd, ?_⟩
  have he := Nat.maxPrimeFac_mul ht.ne' hr.ne_zero
  rw [Nat.div_mul_cancel hd, hr.maxPrimeFac_eq_self] at he
  change P (a*q-1) = max (P ((a*q-1)/r)) r at he
  rw [he]
  exact max_lt (Nat.maxPrimeFac_le.trans_lt htq) hrq

lemma rightLocal_eq_card_sub_one {a r q : ℕ} (ha : 0 < a)
    (har : a < r) (hr : r.Prime) (hq : q.Prime) (hrq : r < q)
    (hd : r ∣ a*q-1) :
    rightLocal (a*q-1) = (a.primeFactors.card : ℝ)-1 := by
  have haq : a < q := har.trans hrq
  have hprod : q ≤ a*q := by simpa using Nat.mul_le_mul_right q ha
  have he : a*q-1+1 = a*q := by omega
  have hh := height_bounds_of_prime_dvd ha har hr hrq hd
  have hheight : P (a*q) = q := height_of_small_mul ha haq.le hq
  have hqnot : q ∉ a.primeFactors := by
    intro h
    exact (not_le_of_gt haq) (Nat.le_of_mem_primeFactors h)
  have hfac : (a*q).primeFactors = insert q a.primeFactors := by
    rw [Nat.primeFactors_mul ha.ne' hq.ne_zero, hq.primeFactors]
    ext t
    simp
  have hterm (t : ℕ) (ht : t ∈ a.primeFactors) :
      (if t ∣ a*q then Erdos371PrimeDeletion.compare
        (P (a*q-1)) (P ((a*q)/t)) else 0) = 1 := by
    have hprime := Nat.prime_of_mem_primeFactors ht
    have hdiv : t ∣ a*q := dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors ht) q
    have hneq : t ≠ P (a*q) := by
      rw [hheight]
      intro h
      subst t
      exact hqnot ht
    rw [if_pos hdiv, quotient_height_eq hprime hdiv hneq, hheight]
    simp [Erdos371PrimeDeletion.compare, hh.2]
  have htop : Erdos371PrimeDeletion.compare (P (a*q-1)) (P a) = -1 := by
    have hsmall : P a < r := Nat.maxPrimeFac_le.trans_lt har
    simp [Erdos371PrimeDeletion.compare, show ¬P (a*q-1) < P a by omega]
  unfold rightLocal rightDeleted
  rw [he, hfac, sum_insert hqnot]
  rw [if_pos (dvd_mul_left q a), Nat.mul_div_cancel _ hq.pos, htop]
  rw [sum_congr rfl hterm]
  simp
  ring

lemma minus_residue_divides {r q : ℕ} (hr : 2 ≤ r)
    (hmod : q ≡ r-1 [MOD r]) : r ∣ (r-1)*q-1 := by
  have hm : q % r = r-1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show r-1 < r by omega)] using hmod
  have hqd : r ∣ q+1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [Nat.add_mod, hm]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < r)]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r), Nat.mod_self]
  have he : (r-1)*q+q=r*q := by
    calc
      _ = ((r-1)+1)*q := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hd := Nat.dvd_sub (dvd_mul_right r q) hqd
  have heq : r*q-(q+1)=(r-1)*q-1 := by omega
  rwa [heq] at hd

lemma exists_prime_with_many_factors_predecessor (K : ℕ) :
    ∃ r : ℕ, r.Prime ∧ 2 < r ∧ K ≤ (r-1).primeFactors.card := by
  obtain ⟨s, hs, hcard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq K
  let M := ∏ p ∈ s, p
  have hsp (p : ℕ) (hp : p ∈ s) : p.Prime := hs hp
  have hM : M ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hsp p hp).ne_zero)
  obtain ⟨r, hr2, hr, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq 2
    (q := M) (a := 1) hM (Nat.coprime_one_left M)
  refine ⟨r, hr, hr2, ?_⟩
  have hd : M ∣ r-1 := (Nat.modEq_iff_dvd' (show 1 ≤ r by omega)).mp hmod.symm
  have hsub : s ⊆ (r-1).primeFactors := by
    intro p hp
    have hpM : p ∣ M := dvd_prod_of_mem (fun x : ℕ => x) hp
    exact Nat.mem_primeFactors.mpr ⟨hsp p hp, hpM.trans hd, by omega⟩
  simpa only [hcard] using card_le_card hsub

/-- The local right-deletion sum exceeds every real bound at arbitrarily large
inputs. This says nothing about its cumulative sum. -/
theorem infinitely_many_rightLocal_gt (B : ℝ) :
    {n | B < rightLocal n}.Infinite := by
  obtain ⟨K, hKB⟩ := exists_nat_gt (B+1)
  obtain ⟨r, hr, hr2, hK⟩ := exists_prime_with_many_factors_predecessor K
  rw [Set.infinite_iff_exists_gt]
  intro N
  have hcop : (r-1).Coprime r := by
    exact (Nat.coprime_self_sub_left (show 1 ≤ r by omega)).mpr (Nat.coprime_one_left r)
  obtain ⟨q, hqN, hq, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max N r)
    (q := r) (a := r-1) hr.ne_zero hcop
  have hrq : r < q := lt_of_le_of_lt (le_max_right N r) hqN
  have hform := rightLocal_eq_card_sub_one (a := r-1) (by omega)
    (by omega) hr hq hrq (minus_residue_divides hr.two_le hmod)
  refine ⟨(r-1)*q-1, ?_, ?_⟩
  · change B < rightLocal ((r-1)*q-1)
    rw [hform]
    have hKr : (K : ℝ) ≤ (r-1).primeFactors.card := Nat.cast_le.mpr hK
    linarith
  · have hh : 2*q ≤ (r-1)*q := Nat.mul_le_mul_right q (by omega)
    omega

lemma height_bounds_of_prime_dvd_plus {a r q : ℕ} (ha : 0 < a)
    (har : a < r) (hr : r.Prime) (hrq : r < q) (hd : r ∣ a*q+1) :
    r ≤ P (a*q+1) ∧ P (a*q+1) < q := by
  have hq : 1 < q := hr.one_lt.trans hrq
  have ht : 0 < (a*q+1)/r := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hr.pos
  have htq : (a*q+1)/r < q := by
    apply (Nat.div_lt_iff_lt_mul hr.pos).mpr
    have hh := Nat.mul_le_mul_right q (show a+1 ≤ r by omega)
    nlinarith
  refine ⟨Nat.le_maxPrimeFac (by omega) hr hd, ?_⟩
  have he := Nat.maxPrimeFac_mul ht.ne' hr.ne_zero
  rw [Nat.div_mul_cancel hd, hr.maxPrimeFac_eq_self] at he
  change P (a*q+1) = max (P ((a*q+1)/r)) r at he
  rw [he]
  exact max_lt (Nat.maxPrimeFac_le.trans_lt htq) hrq

lemma leftLocal_eq_one_sub_card {a r q : ℕ} (ha : 0 < a)
    (har : a < r) (hr : r.Prime) (hq : q.Prime) (hrq : r < q)
    (hd : r ∣ a*q+1) :
    leftLocal (a*q) = 1-(a.primeFactors.card : ℝ) := by
  have haq : a < q := har.trans hrq
  have hh := height_bounds_of_prime_dvd_plus ha har hr hrq hd
  have hheight : P (a*q) = q := height_of_small_mul ha haq.le hq
  have hqnot : q ∉ a.primeFactors := by
    intro h
    exact (not_le_of_gt haq) (Nat.le_of_mem_primeFactors h)
  have hfac : (a*q).primeFactors = insert q a.primeFactors := by
    rw [Nat.primeFactors_mul ha.ne' hq.ne_zero, hq.primeFactors]
    ext t
    simp
  have hterm (t : ℕ) (ht : t ∈ a.primeFactors) :
      Erdos371PrimeDeletion.compare (P ((a*q)/t)) (P (a*q+1)) = -1 := by
    have hprime := Nat.prime_of_mem_primeFactors ht
    have hdiv : t ∣ a*q := dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors ht) q
    have hneq : t ≠ P (a*q) := by
      rw [hheight]
      intro h
      subst t
      exact hqnot ht
    rw [quotient_height_eq hprime hdiv hneq, hheight]
    simp [Erdos371PrimeDeletion.compare, show ¬q < P (a*q+1) by omega]
  have htop : Erdos371PrimeDeletion.compare (P a) (P (a*q+1)) = 1 := by
    have hsmall : P a < r := Nat.maxPrimeFac_le.trans_lt har
    simp [Erdos371PrimeDeletion.compare, show P a < P (a*q+1) by omega]
  unfold leftLocal
  rw [hfac, sum_insert hqnot, Nat.mul_div_cancel _ hq.pos, htop]
  rw [sum_congr rfl hterm]
  simp
  ring

lemma plus_residue_divides {r q : ℕ} (hr : 2 ≤ r)
    (hmod : q ≡ 1 [MOD r]) : r ∣ (r-1)*q+1 := by
  have hm : q % r = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < r by omega)] using hmod
  have hq : 1 ≤ q := by have := Nat.mod_le q r; omega
  have hd : r ∣ q-1 := (Nat.modEq_iff_dvd' hq).mp hmod.symm
  have he : (r-1)*q+q=r*q := by
    calc
      _ = ((r-1)+1)*q := by ring
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hh := Nat.dvd_sub (dvd_mul_right r q) hd
  have heq : r*q-(q-1)=(r-1)*q+1 := by omega
  rwa [heq] at hh

/-- The analogous local left-deletion sum is unbounded below at arbitrarily
large inputs. This does not contradict a cumulative lower bound. -/
theorem infinitely_many_leftLocal_lt (B : ℝ) :
    {n | leftLocal n < B}.Infinite := by
  obtain ⟨K, hKB⟩ := exists_nat_gt (1-B)
  obtain ⟨r, hr, hr2, hK⟩ := exists_prime_with_many_factors_predecessor K
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨q, hqN, hq, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max N r)
    (q := r) (a := 1) hr.ne_zero (Nat.coprime_one_left r)
  have hrq : r < q := lt_of_le_of_lt (le_max_right N r) hqN
  have hform := leftLocal_eq_one_sub_card (a := r-1) (by omega)
    (by omega) hr hq hrq (plus_residue_divides hr.two_le hmod)
  refine ⟨(r-1)*q, ?_, ?_⟩
  · change leftLocal ((r-1)*q) < B
    rw [hform]
    have hKr : (K : ℝ) ≤ (r-1).primeFactors.card := Nat.cast_le.mpr hK
    linarith
  · have hh : q ≤ (r-1)*q := by
      simpa using Nat.mul_le_mul_right q (show 1 ≤ r-1 by omega)
    omega

end Erdos371UnboundedPrimeDeletionLocal

#print axioms Erdos371UnboundedPrimeDeletionLocal.rightLocal_eq_card_sub_one
#print axioms Erdos371UnboundedPrimeDeletionLocal.infinitely_many_rightLocal_gt

#print axioms Erdos371UnboundedPrimeDeletionLocal.leftLocal_eq_one_sub_card
#print axioms Erdos371UnboundedPrimeDeletionLocal.infinitely_many_leftLocal_lt
