import FormalConjecturesUtil
import Submission.SmoothPairEnergyObstruction

/-! Further obstructions to bounding prime-group energy by a constant times the
number of supported consecutive pairs for arbitrary prime supports.
These are not counterexamples to the original density conjecture, nor to a
bound with the full interval length on the right-hand side. -/

namespace Erdos371SupportEnergyConstants

open Erdos371SmoothPairEnergyObstruction

def support : Finset ℕ := {2,5,7,17,19,29,31}

def witnessPairs : Finset ℕ :=
  {1,4,7,16,19,28,31,34,49,124,289,475,1444,1519,6727,6859,8959,29791}

lemma support_prime : ∀ p ∈ support, p.Prime := by decide +kernel

def primeProduct : ℕ := ∏ p ∈ support, p

def certificate : ℕ := primeProduct ^ 15

lemma primeProduct_pos : 0 < primeProduct :=
  Finset.prod_pos (fun p hp => (support_prime p hp).pos)

lemma supported_iff_divides {n : ℕ} (hn : 0 < n) (hb : n ≤ 2^15) :
    n.primeFactors ⊆ support ↔ n ∣ certificate := by
  constructor
  · intro hs
    apply (Nat.dvd_iff_prime_pow_dvd_dvd certificate n).mpr
    intro p k hp hpk
    have hk : k ≤ 15 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      exact (Nat.pow_le_pow_left hp.two_le k).trans ((Nat.le_of_dvd hn hpk).trans hb)
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hpd : p ∣ n := (dvd_pow_self p hk0).trans hpk
      have hpm : p ∈ support := hs (Nat.mem_primeFactors.mpr ⟨hp,hpd,hn.ne'⟩)
      have hprod : p ∣ primeProduct := Finset.dvd_prod_of_mem id hpm
      exact (pow_dvd_pow_of_dvd hprod k).trans (pow_dvd_pow primeProduct hk)
  · intro hd
    have hh := Nat.primeFactors_mono hd (pow_ne_zero 15 primeProduct_pos.ne')
    simpa [certificate, Nat.primeFactors_pow, primeProduct,
      Nat.primeFactors_prod support_prime] using hh

def fast (n : ℕ) : Prop := 0 < n ∧ n ∣ certificate ∧ n+1 ∣ certificate

instance (n : ℕ) : Decidable (fast n) := inferInstanceAs (Decidable (_ ∧ _))

lemma fast_iff {n : ℕ} (hn : n < 29792) :
    fast n ↔ 0 < n ∧ n.primeFactors ⊆ support ∧ (n+1).primeFactors ⊆ support := by
  by_cases hp : 0 < n
  · simp only [fast, hp, true_and, supported_iff_divides hp (by omega : n ≤ 2^15),
      supported_iff_divides (by omega : 0 < n+1) (by omega : n+1 ≤ 2^15)]
  · simp [fast, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma fast_pairs : (Finset.range 29792).filter fast = witnessPairs := by decide +kernel

lemma pairs_exact : pairs support 29792 = witnessPairs := by
  rw [← fast_pairs]
  ext n
  simp only [pairs, Finset.mem_filter, Finset.mem_range]
  by_cases hn : n < 29792
  · rw [← fast_iff hn]
  · simp [hn]

lemma pair_count : (pairs support 29792).card = 18 := by
  rw [pairs_exact]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma energy_exact : energy support 29792 = 62 := by
  unfold energy group
  rw [pairs_exact]
  decide +kernel

lemma support_three_bound_fails :
    ¬ ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ N : ℕ,
      energy s N ≤ 3 * (pairs s N).card := by
  intro h
  have hh := h support support_prime 29792
  rw [energy_exact, pair_count] at hh
  norm_num at hh

end Erdos371SupportEnergyConstants

#print axioms Erdos371SupportEnergyConstants.support_three_bound_fails
