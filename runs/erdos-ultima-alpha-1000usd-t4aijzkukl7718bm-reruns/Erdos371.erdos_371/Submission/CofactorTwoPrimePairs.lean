import FormalConjecturesUtil
import Submission.CofactorLabelEnergy

/-! The cofactor-label-two group is exactly a difference of two prime-pair
counts, up to one endpoint. This clarifies the strength of the full cofactor
energy criterion; it does not assert a cancellation estimate or prove Erdős 371. -/

namespace Erdos371CofactorTwoPrimePairs

open Finset Erdos371Cofactor

abbrev sign := Erdos371PrimeDiscrepancy.sign

def twoIndicator (n : ℕ) : ℤ := if cofactor n = 2 then 1 else 0

def localGroup (n : ℕ) : ℤ :=
  if Erdos371CofactorLabelEnergy.label n = 2 then sign n else 0

lemma cofactor_one_iff_prime {n : ℕ} (hn : 1 < n) :
    cofactor n = 1 ↔ n.Prime := by
  constructor
  · intro h
    have he := cofactor_mul n
    rw [h, one_mul] at he
    rw [← he]
    exact Nat.prime_maxPrimeFac_of_one_lt n hn
  · intro h
    rw [cofactor, P, h.maxPrimeFac_eq_self, Nat.div_self h.pos]

lemma cofactor_two_iff (n : ℕ) :
    cofactor n = 2 ↔ ∃ p : ℕ, p.Prime ∧ n = 2*p := by
  constructor
  · intro h
    have hn : 1 < n := by
      by_contra hh
      interval_cases n <;> norm_num [cofactor, P] at h
    refine ⟨P n, Nat.prime_maxPrimeFac_of_one_lt n hn, ?_⟩
    have he := cofactor_mul n
    rw [h] at he
    exact he.symm
  · rintro ⟨p, hp, rfl⟩
    rw [cofactor, small_cofactor_max (by decide : 0 < 2) hp hp.two_le]
    exact Nat.mul_div_cancel 2 hp.pos

lemma localGroup_eq (n : ℕ) :
    localGroup n = twoIndicator (n+1) - twoIndicator n +
      (if cofactor n = 2 ∧ (n+1).Prime then 1 else 0) -
      (if n.Prime ∧ cofactor (n+1) = 2 then 1 else 0) := by
  rcases n with _ | _ | _ | n
  · decide +kernel
  · decide +kernel
  · decide +kernel
  have hn : 3 ≤ n+3 := by omega
  have hpos := cofactor_pos (n := n+3) (by omega)
  have hpos' := cofactor_pos (n := n+3+1) (by omega)
  have hne := cofactor_consecutive_ne hn
  have hcmp := comparison_iff_cofactor_reverse hn
  have hp := cofactor_one_iff_prime (n := n+3) (by omega)
  have hp' := cofactor_one_iff_prime (n := n+3+1) (by omega)
  change (if min (cofactor (n+3)) (cofactor (n+3+1)) = 2 then
    (if P (n+3) < P (n+3+1) then (1:ℤ) else -1) else 0) =
      twoIndicator (n+3+1) - twoIndicator (n+3) +
      (if cofactor (n+3) = 2 ∧ (n+3+1).Prime then 1 else 0) -
      (if (n+3).Prime ∧ cofactor (n+3+1) = 2 then 1 else 0)
  simp only [hcmp, ← hp, ← hp']
  unfold twoIndicator
  split_ifs <;> omega

/-- Counts p with p and 2p+1 prime, using 2p as the range coordinate. -/
noncomputable def plusCount (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n => (∃ p : ℕ, p.Prime ∧ n = 2*p) ∧ (n+1).Prime).card

/-- Counts p with p and 2p-1 prime, using 2p-1 as the range coordinate. -/
noncomputable def minusCount (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter fun n => n.Prime ∧ ∃ p : ℕ, p.Prime ∧ n+1 = 2*p).card

lemma sum_indicator_increment (N : ℕ) :
    (∑ n ∈ range N, (twoIndicator (n+1) - twoIndicator n)) = twoIndicator N := by
  have hh := sum_range_succ' twoIndicator N
  rw [sum_range_succ] at hh
  have h0 : twoIndicator 0 = 0 := by decide +kernel
  rw [h0, add_zero] at hh
  rw [sum_sub_distrib]
  omega

/-- Exact signed identity. No asymptotic for either prime-pair count is used. -/
theorem group_two_eq_prime_pair_difference (N : ℕ) :
    Erdos371CofactorLabelEnergy.group 2 N =
      (plusCount N : ℤ) - minusCount N + twoIndicator N := by
  classical
  have he : Erdos371CofactorLabelEnergy.group 2 N = ∑ n ∈ range N, localGroup n := rfl
  rw [he]
  simp_rw [localGroup_eq]
  rw [sum_sub_distrib, sum_add_distrib, sum_indicator_increment]
  have hp : (∑ n ∈ range N, if cofactor n = 2 ∧ (n+1).Prime then (1:ℤ) else 0) =
      plusCount N := by
    simp only [cofactor_two_iff, plusCount, sum_boole]
  have hm : (∑ n ∈ range N, if n.Prime ∧ cofactor (n+1) = 2 then (1:ℤ) else 0) =
      minusCount N := by
    simp only [cofactor_two_iff, minusCount, sum_boole]
  rw [hp, hm]
  ring

lemma plusCount_odd (A : ℕ) :
    plusCount (2*A+1) =
      (((A+1).primesBelow.filter fun p => (2*p+1).Prime).card) := by
  classical
  symm
  unfold plusCount
  apply card_bij (fun p _ => 2*p)
  · intro p hp
    obtain ⟨hpA, hplus⟩ := mem_filter.mp hp
    obtain ⟨hpA, hp⟩ := Nat.mem_primesBelow.mp hpA
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), ⟨p, hp, rfl⟩, hplus⟩
  · intro p hp q hq he
    omega
  · intro n hn
    obtain ⟨hnA, ⟨p, hp, he⟩, hplus⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnA
    refine ⟨p, mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, ?_⟩, he.symm⟩
    simpa only [he] using hplus

lemma minusCount_odd (A : ℕ) :
    minusCount (2*A+1) =
      (((A+1).primesBelow.filter fun p => (2*p-1).Prime).card) := by
  classical
  symm
  unfold minusCount
  apply card_bij (fun p _ => 2*p-1)
  · intro p hp
    obtain ⟨hpA, hminus⟩ := mem_filter.mp hp
    obtain ⟨hpA, hp⟩ := Nat.mem_primesBelow.mp hpA
    have hp2 := hp.two_le
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hminus, p, hp, by omega⟩
  · intro p hp q hq he
    have hp2 := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2.two_le
    have hq2 := (Nat.mem_primesBelow.mp (mem_filter.mp hq).1).2.two_le
    omega
  · intro n hn
    obtain ⟨hnA, hminus, ⟨p, hp, he⟩⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnA
    have hnp : n = 2*p-1 := by omega
    refine ⟨p, mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, ?_⟩, hnp.symm⟩
    simpa only [hnp] using hminus

/-- At an odd endpoint, the correction vanishes and the two prime-pair
counts have exactly the same prime cutoff. -/
theorem group_two_odd (A : ℕ) :
    Erdos371CofactorLabelEnergy.group 2 (2*A+1) =
      ((((A+1).primesBelow.filter fun p => (2*p+1).Prime).card : ℤ) -
        (((A+1).primesBelow.filter fun p => (2*p-1).Prime).card)) := by
  have hnot : cofactor (2*A+1) ≠ 2 := by
    intro h
    obtain ⟨p, hp, he⟩ := (cofactor_two_iff _).mp h
    omega
  rw [group_two_eq_prime_pair_difference, plusCount_odd, minusCount_odd]
  simp [twoIndicator, hnot]

lemma group_two_sq_le_energy {N : ℕ} (hN : 4 ≤ N) :
    (Erdos371CofactorLabelEnergy.group 2 N : ℝ)^2 ≤
      Erdos371CofactorLabelEnergy.energy N := by
  have hm : 2 ∈ Erdos371CofactorLabels.labels (N+1) := by
    apply mem_image.mpr
    refine ⟨4, mem_range.mpr (by omega), ?_⟩
    decide +kernel
  exact single_le_sum
    (f := fun a => (Erdos371CofactorLabelEnergy.group a N : ℝ)^2)
    (fun _ _ => sq_nonneg _) hm

/-- In particular, a near-linear bound for the full cofactor-label energy
would imply square-root-scale cancellation in this prime-pair difference.
No such energy bound is proved here. -/
theorem prime_pair_difference_bound {N : ℕ} (hN : 4 ≤ N) :
    |(plusCount N : ℝ) - minusCount N| ≤
      Real.sqrt (Erdos371CofactorLabelEnergy.energy N) + 1 := by
  have hg : |(Erdos371CofactorLabelEnergy.group 2 N : ℝ)| ≤
      Real.sqrt (Erdos371CofactorLabelEnergy.energy N) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact group_two_sq_le_energy hN
  have hi : |(twoIndicator N : ℝ)| ≤ 1 := by
    unfold twoIndicator
    split_ifs <;> norm_num
  have he : (plusCount N : ℝ) - minusCount N =
      (Erdos371CofactorLabelEnergy.group 2 N : ℝ) - twoIndicator N := by
    have hh := group_two_eq_prime_pair_difference N
    have hh' : (Erdos371CofactorLabelEnergy.group 2 N : ℝ) =
        (plusCount N : ℝ) - minusCount N + twoIndicator N := by exact_mod_cast hh
    linarith
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hg hi)

end Erdos371CofactorTwoPrimePairs

#print axioms Erdos371CofactorTwoPrimePairs.group_two_eq_prime_pair_difference
#print axioms Erdos371CofactorTwoPrimePairs.prime_pair_difference_bound

#print axioms Erdos371CofactorTwoPrimePairs.group_two_odd
