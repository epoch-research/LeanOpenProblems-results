import Submission.UniformPrimeDifferenceSieve
import Submission.WienerAtomless
import Submission.PrimeNumberTheoremAP

/-! Regrouping prime-pair Fourier energies by positive differences, with
uniform Selberg bounds. All endpoint and diagonal terms are retained. -/
namespace Erdos371.DilationSpectrum
open Finset Filter MeasureTheory Complex FiniteSieve AbelPrimes
open scoped Topology ENNReal ComplexConjugate
set_option autoImplicit false

lemma sum_even_differences (S : Finset ℕ) (g : ℤ → ℝ) (hg : ∀ k, g (-k)=g k) :
    (∑ p ∈ S, ∑ q ∈ S, g ((p : ℤ)-q)) =
      S.card*g 0+2*∑ p ∈ S, ∑ q ∈ S, if q<p then g ((p : ℤ)-q) else 0 := by
  classical
  have he (p q : ℕ) : g ((p : ℤ)-q) = (if q=p then g 0 else 0)+
      (if q<p then g ((p : ℤ)-q) else 0)+(if p<q then g ((q : ℤ)-p) else 0) := by
    rcases lt_trichotomy p q with hpq | rfl | hpq
    · have hh := hg ((q : ℤ)-p)
      rw [neg_sub] at hh
      simp [hpq,hpq.ne,hpq.ne',hpq.not_gt,hh]
    · simp
    · simp [hpq,hpq.ne,hpq.ne',hpq.not_gt]
  have hdiag : (∑ p ∈ S, ∑ q ∈ S, if q=p then g 0 else 0) = S.card*g 0 := by
    simp
  have hswap : (∑ p ∈ S, ∑ q ∈ S, if p<q then g ((q : ℤ)-p) else 0) =
      ∑ p ∈ S, ∑ q ∈ S, if q<p then g ((p : ℤ)-q) else 0 := sum_comm
  conv_lhs => arg 2; ext p; arg 2; ext q; rw [he p q]
  simp only [sum_add_distrib,hdiag,hswap]
  ring

lemma positive_difference_sum (S : Finset ℕ) (N : ℕ) (hS : ∀ p ∈ S, p ≤ N) (F : ℕ → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, if q<p then F (p-q) else 0) =
      ∑ k ∈ range N, F (k+1)*((S.filter (fun q => q+(k+1) ∈ S)).card : ℝ) := by
  classical
  have hinner (q : ℕ) : (∑ p ∈ S, if q<p then F (p-q) else 0) =
      ∑ k ∈ range N, if q+(k+1) ∈ S then F (k+1) else 0 := by
    rw [← sum_filter,← sum_filter]
    apply sum_nbij' (fun p => p-q-1) (fun k => q+(k+1))
    · intro p hp
      obtain ⟨hp,hqp⟩ := mem_filter.mp hp
      have hpN := hS p hp
      refine mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩
      convert hp using 1 <;> omega
    · intro k hk
      obtain ⟨hk,hmem⟩ := mem_filter.mp hk
      exact mem_filter.mpr ⟨hmem,by omega⟩
    · intro p hp
      have := (mem_filter.mp hp).2
      omega
    · intro k hk
      omega
    · intro p hp
      have := (mem_filter.mp hp).2
      congr 1
      omega
  rw [sum_comm]
  simp_rw [hinner]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_filter,sum_const,nsmul_eq_mul,mul_comm]

lemma initialPrimes_partner_count_le (N k : ℕ) :
    ((initialPrimes N).filter (fun q => q+k ∈ initialPrimes N)).card ≤
      ((range (N+1)).filter (fun q => q.Prime ∧ (q+k).Prime)).card := by
  apply card_le_card
  intro q hq
  obtain ⟨hq,hqk⟩ := mem_filter.mp hq
  obtain ⟨hqN,hqp⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Icc.mp hqN).2; omega),hqp,(mem_filter.mp hqk).2⟩

lemma initialPrimes_even_difference_bound (N : ℕ) (g : ℤ → ℝ)
    (hg : ∀ k, g (-k)=g k) (hgn : ∀ k, 0 ≤ g k) :
    (∑ p ∈ initialPrimes N, ∑ q ∈ initialPrimes N, g ((p : ℤ)-q)) ≤
      (initialPrimes N).card*g 0+
        (2*primeDifferenceSieveConstant*(N+1 : ℝ)/(Real.log (N+2 : ℝ))^2)*
          ∑ k ∈ range N, slopeSieveFactor (2*(k+1))*g (k+1 : ℕ) := by
  rw [sum_even_differences _ g hg]
  have he (p q : ℕ) : (if q<p then g ((p : ℤ)-q) else 0) =
      if q<p then g ((p-q : ℕ) : ℤ) else 0 := by
    split_ifs with h
    · rw [Int.ofNat_sub h.le]
    · rfl
  simp_rw [he]
  rw [positive_difference_sum (initialPrimes N) N
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2) (fun n : ℕ => g (n : ℤ))]
  have hcount (k : ℕ) : (((initialPrimes N).filter (fun q => q+(k+1) ∈ initialPrimes N)).card : ℝ) ≤
      primeDifferenceSieveConstant*slopeSieveFactor (2*(k+1))*(N+1 : ℝ)/(Real.log (N+2 : ℝ))^2 := by
    have hh := primeDifference_count_uniform (k+1) (N+1) (by omega) (by omega)
    have hcard := Nat.cast_le (α := ℝ) |>.mpr (initialPrimes_partner_count_le N (k+1))
    apply hcard.trans
    simpa only [Nat.cast_add,Nat.cast_one,show (N : ℝ)+1+1=N+2 by ring] using hh
  apply add_le_add le_rfl
  rw [mul_sum]
  have hs := sum_le_sum (s := range N) (fun k _ => mul_le_mul_of_nonneg_left (hcount k) (hgn (k+1)))
  have ht := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  convert ht using 1 <;> simp only [Nat.cast_add,Nat.cast_one,mul_sum]
  all_goals
    apply sum_congr rfl
    intro k hk
    ring

#print axioms initialPrimes_even_difference_bound
end Erdos371.DilationSpectrum
