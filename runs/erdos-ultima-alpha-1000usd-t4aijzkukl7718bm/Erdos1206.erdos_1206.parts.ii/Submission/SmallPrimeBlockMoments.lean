import Submission.PrimeBlockModelMoments

/-!
High moments for a small prime block and deterministic bounds for its large-
prime tail. These are inputs to moving-center estimates, not a Sidon theorem.
-/
namespace Erdos1206.SmallPrimeBlockMoments
open Finset PrimeBlockVariance PrimeBlockMomentComparison PrimeBlockModelMoments
open SharpPrimeBlockVariance SignedPrimeBlockExponential
open scoped Classical

/-- The comparison remainder can be absorbed when the block cardinality to
power 2k is at most the arithmetic prefix length. -/
theorem small_moment_le (P : Finset ℕ) (hP : ∀ p∈P,p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p∈P,|w p| ≤ 1) {k N : ℕ} (hk : 0 < k)
    (hcard : P.card^(2*k) ≤ N) :
    (∑ n∈Icc 1 N,(primeSum P w n-mean P w)^(2*k)) ≤
      3*(N:ℝ)*(12*(k:ℝ)*(mass P w+k))^k := by
  have hh := arithmetic_even_moment P hP w hw hk N
  have hl1 : (∑ p∈P,|w p|) ≤ P.card := by
    simpa using sum_le_sum (fun p hp => hw p hp)
  have he : (2*∑ p∈P,|w p|)^(2*k) ≤ (4:ℝ)^k*N := by
    calc
      _ ≤ (2*(P.card:ℝ))^(2*k) := by gcongr
      _ = (4:ℝ)^k*(P.card:ℝ)^(2*k) := by rw [mul_pow,pow_mul]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm := mass_nonneg P w
  have hbase : (4:ℝ) ≤ 12*(k:ℝ)*(mass P w+k) := by nlinarith
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hbase k
  have hpN := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg N)
  nlinarith

/-- Above the r-th root cutoff, fewer than r distinct primes can divide a
positive integer in the prefix. -/
theorem tail_abs_le (P : Finset ℕ) (w : ℕ → ℝ) {T r N n : ℕ}
    (hP : ∀ p∈P,p.Prime ∧ T < p) (hw : ∀ p∈P,|w p| ≤ 1)
    (hn : 0 < n) (hnN : n ≤ N) (hNT : N < (T+1)^r) :
    |primeSum P w n| ≤ r := by
  let D := P.filter (fun p => p∣n)
  have hDp : ∀ p∈D,p.Prime := fun p hp => (hP p (mem_filter.mp hp).1).1
  have hd : (∏ p∈D,p)∣n := (prime_prod_dvd_iff D hDp n).mpr
    (fun p hp => (mem_filter.mp hp).2)
  have hprod : (T+1)^D.card ≤ ∏ p∈D,p := by
    rw [←prod_const]
    apply prod_le_prod (fun _ _ => Nat.zero_le _)
    intro p hp
    have := (hP p (mem_filter.mp hp).1).2
    omega
  have hcard : D.card < r := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (Nat.succ_pos T) (show r ≤ D.card by omega)
    simp only [Nat.succ_eq_add_one] at hpow
    have hdn := Nat.le_of_dvd hn hd
    omega
  have he : primeSum P w n=∑ p∈D,w p := by
    simp only [primeSum,D,sum_filter,indicator]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> simp
  rw [he]
  calc
    _ ≤ ∑ p∈D,|w p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p∈D,(1:ℝ) := sum_le_sum (fun p hp => hw p (mem_filter.mp hp).1)
    _ ≤ r := by simpa using (show (D.card:ℝ) ≤ r by exact_mod_cast hcard.le)

lemma integer_root_cutoff {r : ℕ} (hr : 0 < r) (N : ℕ) :
    ∃ T : ℕ,T^r ≤ N ∧ N < (T+1)^r := by
  let T := Nat.findGreatest (fun t => t^r ≤ N) N
  have hT : T^r ≤ N := Nat.findGreatest_spec (P := fun t => t^r ≤ N) (Nat.zero_le N)
    (by simp [Nat.ne_of_gt hr])
  refine ⟨T,hT,?_⟩
  by_contra h
  have hp : (T+1)^r ≤ N := by omega
  have hle : T+1 ≤ N := (Nat.le_self_pow (Nat.ne_of_gt hr) (T+1)).trans hp
  exact (Nat.findGreatest_is_greatest (show T < T+1 by omega) hle) hp

lemma even_add_le (x y : ℝ) (k : ℕ) :
    (x+y)^(2*k) ≤ (4:ℝ)^k*(x^(2*k)+y^(2*k)) := by
  have he : Even (2*k) := even_two_mul k
  have hh := he.add_pow_le (a := x) (b := y)
  have hs : 0 ≤ x^(2*k)+y^(2*k) := add_nonneg (he.pow_nonneg x) (he.pow_nonneg y)
  have hpow : (2:ℝ)^(2*k-1) ≤ (4:ℝ)^k := by
    calc
      _ ≤ (2:ℝ)^(2*k) := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ = _ := by rw [pow_mul]; norm_num
  exact hh.trans (mul_le_mul_of_nonneg_right hpow hs)

#print axioms small_moment_le
#print axioms tail_abs_le
#print axioms integer_root_cutoff
#print axioms even_add_le
end Erdos1206.SmallPrimeBlockMoments
