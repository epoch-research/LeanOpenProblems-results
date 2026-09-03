import Submission.No9ConcreteSchedule
import Submission.PaddedCertifiedArithmetic

/-! Arithmetic obstruction for any finite exponent schedule extending the checked prefix. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7KilledSieve Erdos7CompressionSieve
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

lemma scheduleNormalizer_sum {n : ℕ} (p E : Fin n → ℕ) (hp : PrimeSchedule p E) (i : Fin n) :
    (∑ g∈Finset.range (E i),((p i:ℚ)⁻¹)^(g+1)) ≤ scheduleNormalizer p i := by
  have hpi : 1 < p i := primeSchedule_gt_one p E hp i
  unfold scheduleNormalizer
  split_ifs with hi
  · obtain ⟨heq,hE⟩ := hp.prefix_stage i hi
    by_cases h3 : (prefixControl i.val).p=3
    · rw [if_pos h3] at hE
      norm_num [hE,heq,h3,denominator]
    · have hpos : 1 ≤ (prefixControl i.val).p := by omega
      rw [denominator,if_neg h3,Nat.cast_sub hpos,Nat.cast_one,← heq]
      exact positive_power_sum_le (p i) hpi (E i)
  · exact positive_power_sum_le (p i) hpi (E i)

theorem scheduled_arithmetic_not_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (p E : Fin n → ℕ) (hp : PrimeSchedule p E)
    (S : Finset (Fin n)) (hcop : (S : Set (Fin n)).Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → Fin n → ℕ) (he : Function.Injective e) (he0 : ∀ k,∃ i,e k i≠0)
    (heE : ∀ k i,e k i ≤ E i) (heS : ∀ k i,e k i≠0 → i∈S) (a : κ → ℤ) :
    ¬(∀ x : ℤ,∃ k,((∏ i,p i^e k i:ℕ):ℤ) ∣ x-a k) := by
  exact arithmetic_padded_certified_not_cover p E (primeSchedule_gt_one p E hp) hp.E_pos S hcop e he he0 heE heS a
    (fun i => scheduleCap i.val) (scheduleNormalizer p) (fun i => scheduleCap_one_le i.val)
    (scheduleCap_le_prime p E hp) (scheduleNormalizer_pos p E hp) (scheduleNormalizer_sum p E hp)
    (scheduleLoss p) (scheduleMass p) (scheduleMass_zero p) (scheduleMass_succ p E hp)
    (fun t ht => (scheduleMass_pos p E hp t).le) (scheduleMass_pos p E hp n) (concrete_schedule_certificate p E hp)

#print axioms scheduled_arithmetic_not_cover
end Erdos7No9Certificate
