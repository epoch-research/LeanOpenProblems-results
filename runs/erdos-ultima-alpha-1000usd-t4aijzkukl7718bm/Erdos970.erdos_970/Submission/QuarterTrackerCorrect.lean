import Submission.QuarterTracker
import Submission.QuarterLaplaceBounds

/-! Semantic correctness of the finite counter: the two accumulated weights
are exactly the scaled Laplace sums over actual cyclic residue phases. -/
namespace Erdos970.GapAverages.QuarterTracker
open Finset QuarterExample

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def good (x : ℕ) : ℕ := if ∀ p ∈ primes, ¬p ∣ x then 1 else 0

lemma fullPrefix_succ (a : ℕ) : CyclicSieve.fullPrefix primes (a+1) =
    CyclicSieve.fullPrefix primes a + (good (a+1) : ℤ) := by
  rw [← CyclicSieve.fullPrefix_sum primes primes_prime, sum_range_succ,
    CyclicSieve.fullPrefix_sum primes primes_prime]
  simp only [good, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma fastCount_update (m a : ℕ) : fastCount m (a+1)+good (a+1) =
    fastCount m a+good (a+m+1) := by
  have hn := CyclicSieve.fullPrefix_diff primes primes_prime m (a+1)
  have hc := CyclicSieve.fullPrefix_diff primes primes_prime m a
  have hs1 := fullPrefix_succ (a+m)
  have hs2 := fullPrefix_succ a
  have he : (a+1)+m = (a+m)+1 := by omega
  rw [he] at hn
  have hh : (CyclicSieve.natCount primes m (a+1) : ℤ)+(good (a+1) : ℤ) =
      (CyclicSieve.natCount primes m a : ℤ)+(good (a+m+1) : ℤ) := by omega
  simp only [fastCount_eq]
  exact_mod_cast hh

lemma deficit_update (m a B : ℕ) (h0 : fastCount m a ≤ B)
    (h1 : fastCount m (a+1) ≤ B) :
    (B-fastCount m a)+good (a+1)-good (a+m+1) = B-fastCount m (a+1) := by
  have hh := fastCount_update m a
  omega

lemma inc_mod (p a : ℕ) (hp : 1 < p) : inc p (a%p) = (a+1)%p := by
  have ha := Nat.mod_lt a (by omega : 0 < p)
  have he : (a+1)%p = (a%p+1)%p := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hp]
  rw [inc, he]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by omega : a%p+1 < p)).symm

def specState (a : ℕ) : State :=
  ⟨(a+1)%3,(a+1)%7,(a+1)%11,(a+1)%19,(a+1)%23,
    11887-fastCount 25236 a,23774-fastCount 50472 a,
    ∑ x ∈ range a, 2^(11887-fastCount 25236 x),
    ∑ x ∈ range a, 2^(23774-fastCount 50472 x)⟩

lemma oldGood_spec (a : ℕ) : oldGood (specState a) = good (a+1) := by
  simp [oldGood, specState, good, primes, Nat.dvd_iff_mod_eq_zero]

lemma endGood1_spec (a : ℕ) : endGood1 (specState a) = good (a+25236+1) := by
  have he : ((a+1)%3 ≠ 0 ∧ (a+1)%7 ≠ 6 ∧ (a+1)%11 ≠ 9 ∧
      (a+1)%19 ≠ 15 ∧ (a+1)%23 ≠ 18) ↔
      ∀ p ∈ primes, ¬p ∣ a+25236+1 := by
    norm_num [primes, Nat.dvd_iff_mod_eq_zero]
    omega
  simp only [endGood1, specState, good, he]

lemma endGood2_spec (a : ℕ) : endGood2 (specState a) = good (a+50472+1) := by
  have he : ((a+1)%3 ≠ 0 ∧ (a+1)%7 ≠ 5 ∧ (a+1)%11 ≠ 7 ∧
      (a+1)%19 ≠ 11 ∧ (a+1)%23 ≠ 13) ↔
      ∀ p ∈ primes, ¬p ∣ a+50472+1 := by
    norm_num [primes, Nat.dvd_iff_mod_eq_zero]
    omega
  simp only [endGood2, specState, good, he]

lemma step_spec (a : ℕ) : step (specState a) = specState (a+1) := by
  rw [step_eq]
  apply State.ext
  · exact inc_mod 3 (a+1) (by omega)
  · exact inc_mod 7 (a+1) (by omega)
  · exact inc_mod 11 (a+1) (by omega)
  · exact inc_mod 19 (a+1) (by omega)
  · exact inc_mod 23 (a+1) (by omega)
  · change (11887-fastCount 25236 a)+oldGood (specState a)-endGood1 (specState a) = _
    rw [oldGood_spec, endGood1_spec]
    exact deficit_update 25236 a 11887 (count_bounds a).1 (count_bounds (a+1)).1
  · change (23774-fastCount 50472 a)+oldGood (specState a)-endGood2 (specState a) = _
    rw [oldGood_spec, endGood2_spec]
    exact deficit_update 50472 a 23774 (count_bounds a).2 (count_bounds (a+1)).2
  · exact (sum_range_succ (fun x => 2^(11887-fastCount 25236 x)) a).symm
  · exact (sum_range_succ (fun x => 2^(23774-fastCount 50472 x)) a).symm

lemma initial_spec : initial = specState 0 := by
  apply State.ext <;>
    norm_num [initial, specState, fastCount, fastPrefix, positiveDivisors,
      negativeDivisors, KernelArithmetic.quotient_eq_div]
  all_goals decide

lemma run_spec (n a : ℕ) : run n (specState a) = specState (a+n) := by
  induction n generalizing a with
  | zero => simp only [run_zero, Nat.add_zero]
  | succ n ih =>
    rw [run_succ, step_spec, ih]
    congr 1
    omega

lemma run_initial_weights (n : ℕ) :
    (run n initial).w1 = ∑ x ∈ range n, 2^(11887-fastCount 25236 x) ∧
    (run n initial).w2 = ∑ x ∈ range n, 2^(23774-fastCount 50472 x) := by
  rw [initial_spec, run_spec, Nat.zero_add]
  exact ⟨rfl,rfl⟩

#print axioms run_initial_weights
end Erdos970.GapAverages.QuarterTracker
