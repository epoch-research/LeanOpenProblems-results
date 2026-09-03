import FormalConjecturesUtil
import Submission.UnboundedPrimeDeletionLocal

/-! Simultaneous local failures of the two prime-deletion sign bounds.
Both unfavorable contributions can be arbitrarily large at the same center.
This rules out a pointwise paired bound, NOT a cumulative bound or Erdős 371. -/

namespace Erdos371PairedPrimeDeletionLocal

open Finset Erdos371PrimeDeletion Erdos371PrimeDeletionLocal
  Erdos371UnboundedPrimeDeletionLocal

/-- Primes in one suitable progression make both neighbors of `a*q`
have largest prime factors strictly between `P(a)` and `q`. -/
lemma simultaneous_neighbor_factors {r : ℕ} (hr : r.Prime) (hr2 : 2 < r) :
    ∃ s : ℕ, r < s ∧ s.Prime ∧ ∀ N : ℕ,
      ∃ q : ℕ, N < q ∧ s < q ∧ q.Prime ∧
        r ∣ (r-1)*q-1 ∧ s ∣ (r-1)*q+1 := by
  let a := r-1
  have ha : 0 < a := by dsimp [a]; omega
  obtain ⟨s, hrs, hs, hsmod⟩ := Nat.forall_exists_prime_gt_and_modEq r
    (q := a) (a := 1) ha.ne' (Nat.coprime_one_left a)
  have hsdiv : a ∣ s-1 := (Nat.modEq_iff_dvd' (show 1 ≤ s by omega)).mp hsmod.symm
  let k := (s-1)/a
  have hak : a*k = s-1 := by
    simpa only [k, Nat.mul_comm] using Nat.div_mul_cancel hsdiv
  have hk : 0 < k := Nat.div_pos (by dsimp [a]; omega) ha
  have hks : k < s := (Nat.div_le_self (s-1) a).trans_lt (by omega)
  have hkr : k.Coprime s := (hs.coprime_iff_not_dvd.mpr (by
    intro h
    exact (not_le_of_gt hks) (Nat.le_of_dvd hk h))).symm
  have har : a.Coprime r := (Nat.coprime_self_sub_left (show 1 ≤ r by omega)).mpr
    (Nat.coprime_one_left r)
  have hrsC : r.Coprime s := (Nat.coprime_primes hr hs).mpr hrs.ne
  let t := Nat.chineseRemainder hrsC a k
  have htr : (t : ℕ).Coprime r := by
    change (t : ℕ).gcd r = 1
    exact t.property.1.gcd_eq.trans har
  have hts : (t : ℕ).Coprime s := by
    change (t : ℕ).gcd s = 1
    exact t.property.2.gcd_eq.trans hkr
  refine ⟨s, hrs, hs, ?_⟩
  intro N
  obtain ⟨q, hqbig, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max N s)
    (q := r*s) (a := t) (Nat.mul_ne_zero hr.ne_zero hs.ne_zero) (htr.mul_right hts)
  have hqr : q ≡ a [MOD r] := (hqmod.of_mul_right s).trans t.property.1
  have hqs : q ≡ k [MOD s] := (hqmod.of_mul_left r).trans t.property.2
  refine ⟨q, (le_max_left _ _).trans_lt hqbig,
    (le_max_right _ _).trans_lt hqbig, hq, minus_residue_divides hr.two_le hqr, ?_⟩
  have hh := (hqs.mul_left a).add_right 1
  have he : a*k+1=s := by omega
  rw [he] at hh
  exact Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl s)))

/-- Unbounded unfavorable values occur simultaneously, not just in two
separately chosen sequences. The left observable uses the opposite orientation
from the plus-sum in the two-sided criterion. -/
theorem infinitely_many_simultaneous (B : ℝ) :
    {n | B < rightLocal (n-1) ∧ leftLocal n < -B}.Infinite := by
  obtain ⟨K, hKB⟩ := exists_nat_gt (B+1)
  obtain ⟨r, hr, hr2, hK⟩ := exists_prime_with_many_factors_predecessor K
  obtain ⟨s, hrs, hs, hqexists⟩ := simultaneous_neighbor_factors hr hr2
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨q, hqN, hsq, hq, hdminus, hdplus⟩ := hqexists N
  have ha : 0 < r-1 := by omega
  have hminus := rightLocal_eq_card_sub_one ha (by omega : r-1<r)
    hr hq (hrs.trans hsq) hdminus
  have hplus := leftLocal_eq_one_sub_card ha (by omega : r-1<s) hs hq hsq hdplus
  refine ⟨(r-1)*q, ?_, ?_⟩
  · change B < rightLocal ((r-1)*q-1) ∧ leftLocal ((r-1)*q) < -B
    rw [hminus, hplus]
    have hc : (K : ℝ) ≤ (r-1).primeFactors.card := Nat.cast_le.mpr hK
    constructor <;> linarith
  · have hh : q ≤ (r-1)*q := by simpa using Nat.mul_le_mul_right q ha
    omega

noncomputable def pairedLocal (n : ℕ) : ℝ := rightLocal (n-1) - leftLocal n

/-- The paired observable is exactly the sum of the minus and plus local
terms, with the same orientation as the two cumulative affine sums. -/
lemma pairedLocal_eq {n : ℕ} (hn : 0 < n) :
    pairedLocal n = ∑ p ∈ n.primeFactors,
      (Erdos371PrimeDeletion.compare (P (n-1)) (P (n/p)) +
       Erdos371PrimeDeletion.compare (P (n+1)) (P (n/p))) := by
  have he : n-1+1=n := by omega
  unfold pairedLocal rightLocal rightDeleted leftLocal
  rw [he, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  rw [if_pos hd]
  have hne : P (n/p) ≠ P (n+1) := by
    intro hh
    have hdiv : P (n+1) ∣ n := by
      rw [← hh]
      exact Nat.maxPrimeFac_dvd.trans (Nat.div_dvd_of_dvd hd)
    have hdiv1 : P (n+1) ∣ 1 := by
      have ht := Nat.dvd_sub (Nat.maxPrimeFac_dvd (n := n+1)) hdiv
      simpa only [Nat.add_sub_cancel_left] using ht
    exact (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).not_dvd_one hdiv1
  have hc : Erdos371PrimeDeletion.compare (P (n/p)) (P (n+1)) =
      -Erdos371PrimeDeletion.compare (P (n+1)) (P (n/p)) := by
    unfold Erdos371PrimeDeletion.compare
    split_ifs <;> norm_num <;> omega
  rw [hc]
  ring

/-- Even the sum of the two unfavorable local contributions has no
universal eventual upper bound. -/
theorem infinitely_many_paired_gt (B : ℝ) : {n | B < pairedLocal n}.Infinite := by
  apply (infinitely_many_simultaneous (B/2)).mono
  intro n hn
  change B < pairedLocal n
  dsimp only [Set.mem_setOf_eq] at hn
  dsimp only [pairedLocal]
  linarith [hn.1, hn.2]

end Erdos371PairedPrimeDeletionLocal

#print axioms Erdos371PairedPrimeDeletionLocal.simultaneous_neighbor_factors
#print axioms Erdos371PairedPrimeDeletionLocal.infinitely_many_simultaneous
#print axioms Erdos371PairedPrimeDeletionLocal.infinitely_many_paired_gt

#print axioms Erdos371PairedPrimeDeletionLocal.pairedLocal_eq
