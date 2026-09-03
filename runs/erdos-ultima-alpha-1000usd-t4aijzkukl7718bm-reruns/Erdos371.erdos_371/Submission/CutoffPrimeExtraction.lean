import FormalConjecturesUtil
import Submission.SmoothCutoffVariation

/-! Exact extraction of the winning-prime contribution from a smooth-cutoff
jump. The change in the other bilinear rows remains as an explicit residual;
no estimate for its signed mean is asserted. -/

namespace Erdos371CutoffPrimeExtraction

open Finset Filter Erdos371PrimeDiscrepancy Erdos371LogarithmicSmoothCommutator
open Erdos371SmoothCutoffVariation
open scoped Topology

noncomputable def top (p n : ℕ) : ℝ := if 0<n ∧ P n=p then 1 else 0

lemma top_eq_difference (p n : ℕ) : top p n=smooth (p+1) n-smooth p n := by
  unfold top smooth P
  split_ifs <;> norm_num <;> omega

lemma top_nonzero_iff (p n : ℕ) : top p n≠0 ↔ 0<n ∧ P n=p := by
  simp [top]

lemma smooth_nonzero_iff (p n : ℕ) : smooth p n≠0 ↔ 0<n ∧ P n<p := by
  simp [smooth]

lemma extraction_unique {p n d : ℕ} (hp : p.Prime) (hd : d∣n)
    (hΛ : ArithmeticFunction.vonMangoldt d≠0) (ht : top p d≠0)
    (hs : smooth p (n/d)≠0) : P n=p ∧ d=p^n.factorization p := by
  obtain ⟨q,k,hq,hk,rfl⟩ := (isPrimePow_nat_iff _).mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  obtain ⟨_,hP⟩ := (top_nonzero_iff p _).mp ht
  rw [P,Nat.maxPrimeFac_pow hk.ne',hq.maxPrimeFac_eq_self] at hP
  subst q
  obtain ⟨ha,hPa⟩ := (smooth_nonzero_iff p _).mp hs
  have he : p^k*(n/p^k)=n := Nat.mul_div_cancel' hd
  have hPn : P n=p := by
    rw [← he,P,Nat.maxPrimeFac_mul (pow_ne_zero _ hp.ne_zero) ha.ne',
      Nat.maxPrimeFac_pow hk.ne',hp.maxPrimeFac_eq_self,max_eq_left hPa.le]
  have hnot : ¬p∣n/p^k := by
    intro hdiv
    have hle := Nat.le_maxPrimeFac ha.ne' hp hdiv
    exact (not_le.mpr hPa) hle
  have hv : n.factorization p=k := by
    calc
      _ = (p^k*(n/p^k)).factorization p := by rw [he]
      _ = k := by simp [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) ha.ne',
        hp.factorization_self,Nat.factorization_eq_zero_of_not_dvd hnot]
  exact ⟨hPn,by rw [hv]⟩

lemma ord_cofactor_smooth {p n : ℕ} (hp : p.Prime) (hn : 0<n) (hPn : P n=p) :
    smooth p (n/p^n.factorization p)=1 := by
  have ha := Nat.ordCompl_pos p hn.ne'
  have he := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm : P (n/p^n.factorization p)≤p := by
    calc
      _ ≤ max (P (p^n.factorization p)) (P (n/p^n.factorization p)) := le_max_right _ _
      _ = p := by rw [← Nat.maxPrimeFac_mul (Nat.ordProj_pos n p).ne' ha.ne',he]; exact hPn
  have hne : P (n/p^n.factorization p)≠p := by
    intro h
    have hd : P (n/p^n.factorization p)∣n/p^n.factorization p := Nat.maxPrimeFac_dvd
    rw [h] at hd
    exact Nat.not_dvd_ordCompl hp hn.ne' hd
  simp [smooth,ha,show P (n/p^n.factorization p)<p by omega]

/-- The prime power selected here is the FULL p-part. Its coefficient is
log p, not the valuation times log p. -/
theorem extraction_convolution {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0<n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d*top p d*smooth p (n/d)) =
      Real.log (p:ℝ)*top p n := by
  by_cases hPn : P n=p
  · have hdiv : p∣n := hPn ▸ Nat.maxPrimeFac_dvd
    have hv : 0<n.factorization p := hp.factorization_pos_of_dvd hn.ne' hdiv
    have hdmem : p^n.factorization p∈n.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p,hn.ne'⟩
    rw [sum_eq_single (p^n.factorization p)]
    · simp [top,hn,hPn,Nat.maxPrimeFac_pow hv.ne',hp.maxPrimeFac_eq_self,
        pow_pos hp.pos,ArithmeticFunction.vonMangoldt_apply_pow hv.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hp,ord_cofactor_smooth hp hn hPn]
    · intro d hd hne
      by_cases hΛ : ArithmeticFunction.vonMangoldt d=0
      · simp [hΛ]
      by_cases ht : top p d=0
      · simp [ht]
      by_cases hs : smooth p (n/d)=0
      · simp [hs]
      exact False.elim (hne (extraction_unique hp (Nat.mem_divisors.mp hd).1 hΛ ht hs).2)
    · exact fun h => False.elim (h hdmem)
  · rw [top,if_neg (by simp [hPn]),mul_zero]
    apply sum_eq_zero
    intro d hd
    by_cases hΛ : ArithmeticFunction.vonMangoldt d=0
    · simp [hΛ]
    by_cases ht : top p d=0
    · simp [ht]
    by_cases hs : smooth p (n/d)=0
    · simp [hs]
    exact False.elim (hPn (extraction_unique hp (Nat.mem_divisors.mp hd).1 hΛ ht hs).1)

noncomputable def primary (p N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*top p d*bilinear (smooth p) d N

noncomputable def residual (p N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ArithmeticFunction.vonMangoldt d*smooth (p+1) d*
    (bilinear (smooth (p+1)) d N-bilinear (smooth p) d N)

lemma jump_eq_primary_add_residual (p N : ℕ) :
    jump p N=primary p N+residual p N := by
  unfold jump primary residual weightedSum
  rw [← sum_sub_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [top_eq_difference]
  ring

lemma primary_eq_local_sum {p : ℕ} (hp : p.Prime) (N : ℕ) :
    primary p N=Real.log (p:ℝ)*∑ n ∈ Icc 1 N,
      top p n*(smooth p (n-1)-smooth p (n+1)) := by
  have he : primary p N=∑ n ∈ Icc 1 N,
      (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d*top p d*smooth p (n/d))*
        (smooth p (n-1)-smooth p (n+1)) := by
    simp only [sum_mul]
    rw [sum_divisors_reindex]
    unfold primary bilinear
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [Nat.mul_div_cancel _ (mem_Icc.mp hd).1]
    ring
  rw [he,mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [extraction_convolution hp (mem_Icc.mp hn).1]
  ring

lemma local_kernel {p : ℕ} (hp : p.Prime) (n : ℕ) :
    smooth p n*top p (n+1)-top p n*smooth p (n+1) =
      if winner n=p then (sign n:ℝ) else 0 := by
  have ht := hp.two_le
  by_cases hn : n=0
  · subst n
    simp [smooth,top,winner,P,show 1≠p by omega]
  · have hne := consecutive_ne n
    simp only [smooth,top,winner,sign,Int.cast_ite,Int.cast_one,Int.cast_neg,P] at *
    split_ifs <;> norm_num <;> omega

lemma local_sum_eq_group {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N, top p n*(smooth p (n-1)-smooth p (n+1))) =
      (group p N:ℝ)-top p N*smooth p (N+1) := by
  induction N with
  | zero => simp [group,top]
  | succ N ih =>
    have hgroup : (group p (N+1):ℝ)=(group p N:ℝ)+
        (if winner N=p then (sign N:ℝ) else 0) := by
      simp [group,sum_range_succ]
    rw [sum_Icc_succ_top (by omega),ih,hgroup,← local_kernel hp]
    simp only [Nat.add_sub_cancel]
    ring

/-- Exactly the original signed winning-prime group, up to its endpoint. -/
theorem primary_eq_log_group {p : ℕ} (hp : p.Prime) (N : ℕ) :
    primary p N=Real.log (p:ℝ)*((group p N:ℝ)-top p N*smooth p (N+1)) := by
  rw [primary_eq_local_sum hp,local_sum_eq_group hp]

/-- The residual contains the negative of the same signed group. The unsigned
cutoff-jump identity alone therefore does not remove this signed term. -/
theorem residual_eq {p : ℕ} (hp : p.Prime) (N : ℕ) :
    residual p N=interior p N-endpoint p N-
      Real.log (p:ℝ)*((group p N:ℝ)-top p N*smooth p (N+1)) := by
  have h := jump_eq_primary_add_residual p N
  rw [jump_eq,primary_eq_log_group hp] at h
  linarith

end Erdos371CutoffPrimeExtraction

#print axioms Erdos371CutoffPrimeExtraction.extraction_convolution
#print axioms Erdos371CutoffPrimeExtraction.primary_eq_log_group
#print axioms Erdos371CutoffPrimeExtraction.residual_eq
