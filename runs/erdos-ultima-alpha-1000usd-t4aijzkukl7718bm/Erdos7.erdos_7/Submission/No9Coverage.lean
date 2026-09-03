import Submission.No9Schedule
import Submission.No9PrefixCoverage
import Submission.No9BlockCoverage0
import Submission.No9BlockCoverage1
import Submission.No9BlockCoverage2
import Submission.No9BlockCoverage3
import Submission.No9BlockCoverage4
import Submission.No9BlockCoverage5
import Submission.No9BlockCoverage6
import Submission.No9BlockCoverage7
import Submission.No9BlockCoverage8
import Submission.No9BlockCoverage9
import Submission.No9BlockCoverage10
import Submission.No9BlockCoverage11
import Submission.No9BlockCoverage12
import Submission.No9BlockCoverage13
import Submission.No9BlockCoverage14
import Submission.No9BlockCoverage15
import Submission.No9BlockCoverage16
import Submission.No9BlockCoverage17

/-! Certified candidate lists contain every prime from 3 through 1500000.
Candidates are not asserted prime: unused coordinates are padded abstractly. -/
namespace Erdos7No9Certificate
open Erdos7PrimeCoverage
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

theorem block_prime_coverage_checks_all (i : ℕ) (hi : i < blockLength) : blockPrimeCoverageCheck i=true := by
  change i < 288 at hi
  have hk : i/16 < 18 := by omega
  generalize heq : i/16=k at *
  interval_cases k
  · exact block_prime_coverages_0 i (by omega) (by omega)
  · exact block_prime_coverages_1 i (by omega) (by omega)
  · exact block_prime_coverages_2 i (by omega) (by omega)
  · exact block_prime_coverages_3 i (by omega) (by omega)
  · exact block_prime_coverages_4 i (by omega) (by omega)
  · exact block_prime_coverages_5 i (by omega) (by omega)
  · exact block_prime_coverages_6 i (by omega) (by omega)
  · exact block_prime_coverages_7 i (by omega) (by omega)
  · exact block_prime_coverages_8 i (by omega) (by omega)
  · exact block_prime_coverages_9 i (by omega) (by omega)
  · exact block_prime_coverages_10 i (by omega) (by omega)
  · exact block_prime_coverages_11 i (by omega) (by omega)
  · exact block_prime_coverages_12 i (by omega) (by omega)
  · exact block_prime_coverages_13 i (by omega) (by omega)
  · exact block_prime_coverages_14 i (by omega) (by omega)
  · exact block_prime_coverages_15 i (by omega) (by omega)
  · exact block_prime_coverages_16 i (by omega) (by omega)
  · exact block_prime_coverages_17 i (by omega) (by omega)

lemma prefix_covers_prime (p : ℕ) (hp : p.Prime) (hp0 : 3 ≤ p) (hp1 : p < 5000) :
    ∃ j,j < prefixLength ∧ (prefixControl j).p=p := by
  exact coverageCheck_sound 3 (5000-3) prefixLength (fun j => (prefixControl j).p) prefixWitness
    prefix_prime_coverage_check p hp hp0 (by omega)

lemma block_coverage_facts (i : ℕ) (hi : i < blockLength) :
    (blockControl i).lo < (blockControl i).hi ∧
    coverageCheck (blockControl i).lo ((blockControl i).hi-(blockControl i).lo) (blockControl i).count
      (blockCandidate i) (blockWitness i)=true ∧
    orderCheck (blockControl i).lo (blockControl i).hi (blockControl i).count (blockCandidate i)=true := by
  simpa only [blockPrimeCoverageCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using block_prime_coverage_checks_all i hi

lemma block_covers_prime (i : ℕ) (hi : i < blockLength) (p : ℕ) (hp : p.Prime)
    (hp0 : (blockControl i).lo ≤ p) (hp1 : p < (blockControl i).hi) :
    ∃ j,j < (blockControl i).count ∧ blockCandidate i j=p := by
  have hh := block_coverage_facts i hi
  exact coverageCheck_sound _ _ _ _ _ hh.2.1 p hp hp0 (by omega)

lemma block_candidate_bounds (i : ℕ) (hi : i < blockLength) (j : ℕ) (hj : j < (blockControl i).count) :
    (blockControl i).lo ≤ blockCandidate i j ∧ blockCandidate i j < (blockControl i).hi :=
  orderCheck_mem _ _ _ _ (block_coverage_facts i hi).2.2 j hj

lemma block_candidates_strictMono (i : ℕ) (hi : i < blockLength) :
    StrictMono (fun j : Fin (blockControl i).count => blockCandidate i j.val) :=
  orderCheck_strictMono _ _ _ _ (block_coverage_facts i hi).2.2

lemma block_order_facts : (blockControl 0).lo=5000 ∧ (blockControl (blockLength-1)).hi=1500001 ∧
    ∀ i,i < blockLength-1 → (blockControl i).hi=(blockControl (i+1)).lo := by
  simpa only [blockOrderCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_range,and_assoc] using block_order_check

def blockBoundary (i : ℕ) : ℕ := if i=0 then 5000 else (blockControl (i-1)).hi

lemma block_boundary_zero : blockBoundary 0=5000 := rfl
lemma block_boundary_last : blockBoundary blockLength=1500001 := by
  simpa only [blockBoundary,if_neg (by decide +kernel : blockLength≠0)] using block_order_facts.2.1
lemma block_boundary_succ (i : ℕ) : blockBoundary (i+1)=(blockControl i).hi := by
  simp only [blockBoundary,if_neg (by omega : i+1≠0),Nat.add_sub_cancel]
lemma block_boundary_eq_lo (i : ℕ) (hi : i < blockLength) : blockBoundary i=(blockControl i).lo := by
  by_cases hz : i=0
  · subst i; exact block_order_facts.1.symm
  · have hp : i-1 < blockLength-1 := by omega
    have hh := block_order_facts.2.2 (i-1) hp
    simpa only [blockBoundary,if_neg hz,Nat.sub_add_cancel (by omega : 1 ≤ i)] using hh

lemma interval_has_block (p : ℕ) (hp0 : 5000 ≤ p) (hp1 : p ≤ 1500000) :
    ∃ i,i < blockLength ∧ (blockControl i).lo ≤ p ∧ p < (blockControl i).hi := by
  obtain ⟨i,hi,hlo,hhi⟩ := exists_adjacent_interval blockBoundary blockLength p
    (by simpa only [block_boundary_zero] using hp0) (by rw [block_boundary_last]; omega)
  exact ⟨i,hi,by simpa only [block_boundary_eq_lo i hi] using hlo,by simpa only [block_boundary_succ] using hhi⟩

lemma all_small_primes_covered (p : ℕ) (hp : p.Prime) (hp0 : 3 ≤ p) (hp1 : p ≤ 1500000) :
    (∃ j,j < prefixLength ∧ (prefixControl j).p=p) ∨
    ∃ i j,i < blockLength ∧ j < (blockControl i).count ∧ blockCandidate i j=p := by
  by_cases hsmall : p < 5000
  · exact Or.inl (prefix_covers_prime p hp hp0 hsmall)
  · obtain ⟨i,hi,hlo,hhi⟩ := interval_has_block p (by omega) hp1
    obtain ⟨j,hj,heq⟩ := block_covers_prime i hi p hp hlo hhi
    exact Or.inr ⟨i,j,hi,hj,heq⟩

#print axioms all_small_primes_covered
end Erdos7No9Certificate
