import Submission.SelbergUnitWeights

/-! Bounds for the actual Selberg majorant. In particular, its value on
numbers with a bounded number of prime factors is bounded independently of
the sieve cutoff. -/
namespace Erdos972SelbergMajorantSize

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergUnitWeights

set_option maxHeartbeats 1500000

lemma selbergWeight_zero_of_not_squarefree (R : ℕ) {d : ℕ} (hs : ¬ Squarefree d) :
    selbergWeight R d = 0 := by
  by_cases hd : d = 0
  · simp [hd, selbergWeight]
  rw [selbergWeight_formula (Nat.pos_of_ne_zero hd)]
  simp only [moebius_eq_zero_of_not_squarefree hs, Int.cast_zero, zero_mul, zero_div]

theorem weightCoeff_abs_sum_square {R : ℕ} (hR : 1 ≤ R) :
    (∑ z ∈ weightIndices R, |weightCoeff R z|) ≤ (R:ℝ)^2 := by
  calc
    _ ≤ ∑ z ∈ weightIndices R, (1:ℝ) := by
      apply sum_le_sum
      intro z hz
      rw [weightCoeff, abs_mul]
      exact mul_le_one₀ (abs_selbergWeight_le_one hR _) (abs_nonneg _)
        (abs_selbergWeight_le_one hR _)
    _ = _ := by simp [weightIndices, pow_two]

lemma squarefree_divisor_card_le {n K : ℕ} (hn : n ≠ 0)
    (hK : n.primeFactorsList.length ≤ K) (R : ℕ) :
    ((Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d)).card ≤ 2^K := by
  have hmap : Set.MapsTo Nat.primeFactors
      ↑((Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d)) ↑n.primeFactors.powerset := by
    intro d hd
    change d ∈ (Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d) at hd
    exact mem_powerset.mpr (Nat.primeFactors_mono (mem_filter.mp hd).2.1 hn)
  have hinj : Set.InjOn Nat.primeFactors
      ↑((Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d)) := by
    intro d hd e he hde
    change d ∈ (Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d) at hd
    change e ∈ (Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d) at he
    change d.primeFactors = e.primeFactors at hde
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hd).2.2,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp he).2.2, hde]
  have hh := card_le_card_of_injOn Nat.primeFactors hmap hinj
  rw [card_powerset] at hh
  apply hh.trans
  apply Nat.pow_le_pow_right (by decide)
  exact (List.toFinset_card_le n.primeFactorsList).trans hK

lemma selberg_divisor_sum_bound {R n K : ℕ} (hR : 1 ≤ R) (hn : n ≠ 0)
    (hK : n.primeFactorsList.length ≤ K) :
    |∑ d ∈ Ioc 0 R, if d ∣ n then selbergWeight R d else 0| ≤ (2:ℝ)^K := by
  classical
  let T := (Ioc 0 R).filter (fun d => d ∣ n ∧ Squarefree d)
  have he : (∑ d ∈ Ioc 0 R, if d ∣ n then selbergWeight R d else 0) =
      ∑ d ∈ T, selbergWeight R d := by
    dsimp only [T]
    rw [sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hdn : d ∣ n <;> by_cases hs : Squarefree d <;>
      simp [selbergWeight_zero_of_not_squarefree, *]
  rw [he]
  calc
    _ ≤ ∑ d ∈ T, |selbergWeight R d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ T, (1:ℝ) := sum_le_sum (fun d _ => abs_selbergWeight_le_one hR d)
    _ = T.card := by simp
    _ ≤ _ := by exact_mod_cast squarefree_divisor_card_le hn hK R

noncomputable def majorantCap (K : ℕ) : ℝ := ((2:ℝ)^K)^2

lemma majorantCap_pos (K : ℕ) : 0 < majorantCap K := by unfold majorantCap; positivity

theorem majorant_bounded_factors {R n K : ℕ} (hR : 1 ≤ R) (hn : n ≠ 0)
    (hK : n.primeFactorsList.length ≤ K) : majorant R n ≤ majorantCap K := by
  have hb := selberg_divisor_sum_bound hR hn hK
  unfold majorant majorantCap
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb

#print axioms weightCoeff_abs_sum_square
#print axioms majorant_bounded_factors

end Erdos972SelbergMajorantSize
