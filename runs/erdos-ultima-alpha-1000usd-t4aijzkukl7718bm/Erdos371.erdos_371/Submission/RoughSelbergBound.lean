import Submission.TwoLinearSelberg

/-! A one-dimensional Selberg bound for integers avoiding small prime
factors. The polynomial sieve error is retained uniformly in the sample. -/
namespace Erdos371.FiniteSieve
open Finset

noncomputable def siftedCount (z M : ℕ) : ℕ :=
  avoidanceCount (range M) (fun p n => p ∣ n) (z+1).primesBelow

lemma exp_neg_primeHarmonic_le (z : ℕ) (hz : 1 ≤ z) :
    Real.exp (-primeHarmonic z) ≤ Real.exp 1/Real.log (z+1 : ℝ) := by
  have hl : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  apply (le_div_iff₀ hl).mpr
  have h := mul_le_mul_of_nonneg_left (log_le_exp_primeHarmonic z) (Real.exp_nonneg (-primeHarmonic z))
  convert h using 1
  rw [← Real.exp_add]
  congr 1
  ring

lemma siftedCount_selberg_exp (z M : ℕ) (hz : 1 ≤ z) :
    (siftedCount z M : ℝ) ≤ 2*M*Real.exp (-primeHarmonic z)+2*(z+1 : ℝ)^32 := by
  let S := (z+1).primesBelow
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (Nat.mem_primesBelow.mp h).2
  have hc : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hpS q hqS hpq
    exact (Nat.coprime_primes (hp p hpS) (hp q hqS)).mpr hpq
  have hZ : (1 : ℝ) < (z+1 : ℝ)^8 := one_lt_pow₀
    (by exact_mod_cast (show 1 < z+1 by omega)) (by decide)
  have hm : (∑ p ∈ S, Real.log p*(({0} : Finset ℕ).card : ℝ)/(p : ℝ)) ≤
      Real.log ((z+1 : ℝ)^8)/2 := by
    simp only [card_singleton,Nat.cast_one,mul_one,Real.log_pow,Nat.cast_ofNat]
    have hh : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ 4*Real.log (z+1 : ℝ) := by
      calc
        _ ≤ ∑ p ∈ S, Real.log p/((p : ℝ)-1) := by
          apply sum_le_sum
          intro p hpS
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p hpS).two_le
          exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
        _ ≤ _ := by simpa only [S,Nat.cast_add,Nat.cast_one] using prime_log_div_pred_sum_le (z+1)
    linarith
  have hh := residue_selberg_upper_bound S id (fun _ => ({0} : Finset ℕ))
    (fun p hpS => (hp p hpS).ne_zero) hc
    (fun p hpS => by simpa only [singleton_subset_iff,mem_range] using (hp p hpS).pos)
    (fun p hpS => by simpa only [card_singleton] using And.intro (by decide : 0 < 1) (hp p hpS).one_lt)
    ((z+1 : ℝ)^8) hZ hm M
  have hmass : (∑ p ∈ S, (1 : ℝ)/p)=primeHarmonic z := by
    simp only [S,primeHarmonic,primeReciprocalSum,Nat.primesBelow]
  have he : avoidanceCount (range M) (fun p n => n%id p ∈ ({0} : Finset ℕ)) S=siftedCount z M := by
    unfold avoidanceCount siftedCount
    congr 1
    ext n
    simp only [mem_filter,id_eq,mem_singleton,Nat.dvd_iff_mod_eq_zero,S]
  simp only [id_eq,card_singleton,Nat.cast_one,← pow_mul,Nat.reduceMul] at hh
  rw [show avoidanceCount (range M) (fun p n => n%p ∈ ({0} : Finset ℕ)) S=siftedCount z M from he,hmass] at hh
  exact hh

/-- Uniform in M, including short samples. No rounding term is dropped. -/
theorem siftedCount_selberg_bound (z M : ℕ) (hz : 1 ≤ z) :
    (siftedCount z M : ℝ) ≤ 2*Real.exp 1*M/Real.log (z+1 : ℝ)+2*(z+1 : ℝ)^32 := by
  have hh := mul_le_mul_of_nonneg_left (exp_neg_primeHarmonic_le z hz) (by positivity : (0 : ℝ) ≤ 2*M)
  exact (siftedCount_selberg_exp z M hz).trans (add_le_add (by convert hh using 1; ring) le_rfl)

#print axioms siftedCount_selberg_bound
end Erdos371.FiniteSieve
