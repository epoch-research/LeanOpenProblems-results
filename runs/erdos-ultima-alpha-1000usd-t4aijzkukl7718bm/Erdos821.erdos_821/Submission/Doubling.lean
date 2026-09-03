import Submission.Work

/-!
# A barrier to amplification by doubling

The inverse-totient multiplicity is not monotone under doubling. This does not
settle Erdős 821; it rules out one possible elementary amplification step.
-/

open Nat Filter

namespace Erdos821

lemma primeFactors_subset_iff_of_dvd_two_pow {m k : ℕ} {S : Finset ℕ}
    (hm : m ∣ 2 ^ k) : m.primeFactors ⊆ S ↔ m = 1 ∨ 2 ∈ S := by
  obtain ⟨a, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm
  by_cases ha : a = 0
  · simp [ha]
  rw [Nat.primeFactors_pow 2 ha]
  simp [ha]

lemma admissibleSupports_two_pow_filter (k : ℕ) :
    admissibleSupports (2 ^ k) =
      (shiftedPrimeDivisors (2 ^ k)).powerset.filter (fun S =>
        (∏ p ∈ S, (p - 1)) ∣ 2 ^ k ∧
          (2 ^ k / (∏ p ∈ S, (p - 1)) = 1 ∨ 2 ∈ S)) := by
  apply Finset.filter_congr
  intro S _
  constructor
  · rintro ⟨hdiv, hsub⟩
    exact ⟨hdiv, (primeFactors_subset_iff_of_dvd_two_pow
      (Nat.div_dvd_of_dvd hdiv)).mp hsub⟩
  · rintro ⟨hdiv, hsub⟩
    exact ⟨hdiv, (primeFactors_subset_iff_of_dvd_two_pow
      (Nat.div_dvd_of_dvd hdiv)).mpr hsub⟩


lemma prime_of_pred_dvd_two_pow_le_32 {p k : ℕ} (hp : p.Prime)
    (hk : k ≤ 32) (hd : p - 1 ∣ 2 ^ k) :
    p ∈ ({2, 3, 5, 17, 257, 65537} : Finset ℕ) := by
  by_cases hp2 : p = 2
  · simp [hp2]
  obtain ⟨a, hak, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hpa : p = 2 ^ a + 1 := by have := hp.two_le; omega
  have ha0 : a ≠ 0 := by intro h; simp [h] at hpa; exact hp2 hpa
  obtain ⟨j, rfl⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < (2 : ℕ)) ha0 (hpa ▸ hp)
  have hj : j ≤ 5 := by
    have hjpow : 2 ^ j ≤ 2 ^ 5 := hak.trans hk
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hjpow
  interval_cases j <;> norm_num at hpa
  all_goals first | (solve | simp [hpa]) | skip
  subst p
  have hd641 : 641 ∣ 4294967297 := by decide
  have hbad := (Nat.dvd_prime hp).mp hd641
  norm_num at hbad

lemma shiftedPrimeDivisors_two_pow_31 :
    shiftedPrimeDivisors (2 ^ 31) = {2, 3, 5, 17, 257, 65537} := by
  ext p
  constructor
  · intro hp
    obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hp
    exact prime_of_pred_dvd_two_pow_le_32 hp (by decide) hd
  · intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [shiftedPrimeDivisors]

lemma shiftedPrimeDivisors_two_pow_32 :
    shiftedPrimeDivisors (2 ^ 32) = {2, 3, 5, 17, 257, 65537} := by
  ext p
  constructor
  · intro hp
    obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hp
    exact prime_of_pred_dvd_two_pow_le_32 hp le_rfl hd
  · intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [shiftedPrimeDivisors]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma g_two_pow_31 : g (2 ^ 31) = 33 := by
  rw [g_eq_card_admissibleSupports (by positivity), admissibleSupports_two_pow_filter,
    shiftedPrimeDivisors_two_pow_31]
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma g_two_pow_32 : g (2 ^ 32) = 32 := by
  rw [g_eq_card_admissibleSupports (by positivity), admissibleSupports_two_pow_filter,
    shiftedPrimeDivisors_two_pow_32]
  decide

/-- Multiplying the output by two can strictly decrease its multiplicity. -/
theorem exists_g_double_lt : ∃ n : ℕ, 0 < n ∧ g (2 * n) < g n := by
  refine ⟨2 ^ 31, by positivity, ?_⟩
  rw [show 2 * 2 ^ 31 = 2 ^ 32 by norm_num, g_two_pow_32, g_two_pow_31]
  norm_num

#print axioms g_two_pow_31
#print axioms g_two_pow_32
#print axioms exists_g_double_lt

end Erdos821
