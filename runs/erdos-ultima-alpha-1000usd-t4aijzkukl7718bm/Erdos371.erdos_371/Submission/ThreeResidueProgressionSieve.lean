import Submission.ProgressionSelberg

/-! A dimension-three upper sieve in an arithmetic progression, excluding
all sieving primes up to an explicit lower cutoff. -/
namespace Erdos371.FiniteSieve
open Finset

def upperSievingPrimes (D z : ℕ) : Finset ℕ := (z+1).primesBelow.filter (D < ·)

lemma mem_upperSievingPrimes (D z p : ℕ) :
    p ∈ upperSievingPrimes D z ↔ p.Prime ∧ D < p ∧ p ≤ z := by
  simp only [upperSievingPrimes,mem_filter,Nat.mem_primesBelow,Nat.lt_succ_iff]
  tauto

lemma upperSievingPrimes_mass_lower (D z : ℕ) :
    primeHarmonic z-primeHarmonic D ≤ ∑ p ∈ upperSievingPrimes D z, (1 : ℝ)/p := by
  have hs := sum_filter_add_sum_filter_not (z+1).primesBelow (D < ·) (fun p : ℕ => (1 : ℝ)/p)
  have hb : (∑ p ∈ (z+1).primesBelow with ¬D<p, (1 : ℝ)/p) ≤ primeHarmonic D := by
    change _ ≤ ∑ p ∈ (D+1).primesBelow, (1 : ℝ)/p
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpz,hpD⟩ := mem_filter.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,(Nat.mem_primesBelow.mp hpz).2⟩
    · intros; positivity
  change (∑ p ∈ upperSievingPrimes D z, (1 : ℝ)/p) + _ = primeHarmonic z at hs
  linarith

lemma exp_neg_three_primeHarmonic_le (z : ℕ) (hz : 1 ≤ z) :
    Real.exp (-3*primeHarmonic z) ≤ Real.exp 3/(Real.log (z+1 : ℝ))^3 := by
  have hpos : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z+1))
  have hs := pow_le_pow_left₀ hpos.le (log_le_exp_primeHarmonic z) 3
  apply (le_div_iff₀ (pow_pos hpos 3)).mpr
  have ht := mul_le_mul_of_nonneg_left hs (Real.exp_nonneg (-3*primeHarmonic z))
  convert ht using 1
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  norm_num
  ring

lemma upperSievingPrimes_exp_three_bound (D z : ℕ) (hz : 1 ≤ z) :
    Real.exp (-3*(∑ p ∈ upperSievingPrimes D z, (1 : ℝ)/p)) ≤
      Real.exp 3*Real.exp (3*primeHarmonic D)/(Real.log (z+1 : ℝ))^3 := by
  have hm := upperSievingPrimes_mass_lower D z
  calc
    _ ≤ Real.exp (-3*primeHarmonic z+3*primeHarmonic D) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-3*primeHarmonic z)*Real.exp (3*primeHarmonic D) := Real.exp_add _ _
    _ ≤ (Real.exp 3/(Real.log (z+1 : ℝ))^3)*Real.exp (3*primeHarmonic D) :=
      mul_le_mul_of_nonneg_right (exp_neg_three_primeHarmonic_le z hz) (Real.exp_nonneg _)
    _ = _ := by ring

/-- Three forbidden roots per sieving prime give a cubic logarithmic
saving; the progression density is retained. -/
theorem threeResidue_progression_sieve_bound (D z M r N : ℕ)
    (hD : 3 ≤ D) (hz : 1 ≤ z) (hM : 0 < M) (hMD : M ≤ D) (hrM : r < M)
    (R : ℕ → Finset ℕ)
    (hR : ∀ p ∈ upperSievingPrimes D z, R p ⊆ range p)
    (hcard : ∀ p ∈ upperSievingPrimes D z, (R p).card=3) :
    (((range N).filter (fun n => n%M=r ∧ ∀ p ∈ upperSievingPrimes D z, n%p ∉ R p)).card : ℝ) ≤
      2*Real.exp 3*Real.exp (3*primeHarmonic D)*N/(M*(Real.log (z+1 : ℝ))^3)+
        2*(M : ℝ)^8*(z+1 : ℝ)^96 := by
  let S := upperSievingPrimes D z
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ D < p ∧ p ≤ z :=
    (mem_upperSievingPrimes D z p).mp hp
  have hMS : M ∉ S := by intro hp; have := (hS M hp).2.1; omega
  have hcopM : ∀ p ∈ S, M.Coprime p := by
    intro p hp
    apply Nat.Coprime.symm
    apply ((hS p hp).1.coprime_iff_not_dvd).mpr
    intro hd
    have hh := Nat.le_of_dvd hM hd
    have hh' := (hS p hp).2.1
    omega
  have hc : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq
  have hr : ∀ p ∈ S, 0 < (R p).card ∧ (R p).card < p := by
    intro p hp
    rw [hcard p hp]
    have := (hS p hp).2.1
    omega
  have hZ : (1 : ℝ) < (z+1 : ℝ)^24 :=
    one_lt_pow₀ (by exact_mod_cast (by omega : 1 < z+1)) (by decide)
  have hsmall : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ 4*Real.log (z+1 : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (z+1).primesBelow, Real.log p/((p : ℝ)-1) := by
        apply (sum_le_sum ?_).trans
          (sum_le_sum_of_subset_of_nonneg (t := (z+1).primesBelow) ?_ ?_)
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
          exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
        · intro p hp
          exact Nat.mem_primesBelow.mpr ⟨by have := (hS p hp).2.2; omega,(hS p hp).1⟩
        · intro p hp _
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
          exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
      _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using prime_log_div_pred_sum_le (z+1)
  have hm : (∑ p ∈ S, Real.log p*((R p).card : ℝ)/p) ≤ Real.log ((z+1 : ℝ)^24)/2 := by
    have he : (∑ p ∈ S, Real.log p*((R p).card : ℝ)/p) =
        3*(∑ p ∈ S, Real.log p/(p : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [hcard p hp]
      push_cast
      ring
    rw [he,Real.log_pow]
    norm_num
    linarith
  have he : (∑ p ∈ S, ((R p).card : ℝ)/p)=3*(∑ p ∈ S, (1 : ℝ)/p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [hcard p hp]
    push_cast
    ring
  have hh := residue_selberg_progression_bound S R M r N hM hrM hMS hcopM
    (fun p hp => (hS p hp).1.ne_zero) hc hR hr ((z+1 : ℝ)^24) hZ hm
  rw [he,← pow_mul] at hh
  have hb := mul_le_mul_of_nonneg_left (upperSievingPrimes_exp_three_bound D z hz)
    (show (0 : ℝ) ≤ 2*N/M by positivity)
  apply hh.trans
  apply add_le_add _ le_rfl
  convert hb using 1 <;> dsimp only [S] <;> ring_nf

#print axioms threeResidue_progression_sieve_bound
end Erdos371.FiniteSieve
