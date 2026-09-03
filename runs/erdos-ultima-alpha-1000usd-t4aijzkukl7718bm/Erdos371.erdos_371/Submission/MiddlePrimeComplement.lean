import Submission.SmoothLowComplementCount

/-! Long low cofactors with no prime in the middle band (Y,W] have negligible
absolute contribution. The remaining signed middle-band term is not estimated. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma canonical_low_prime_small (W e p : ℕ) (he : Squarefree e)
    (hp : p ∈ (e/roughRadical W e).primeFactors) : p ≤ W := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpf := Nat.dvd_of_mem_primeFactors hp
  have hmul : (e/roughRadical W e)*roughRadical W e=e := Nat.div_mul_cancel (roughRadical_dvd W e)
  have hc : (e/roughRadical W e).Coprime (roughRadical W e) :=
    Nat.coprime_of_squarefree_mul (by rw [hmul]; exact he)
  have hpe := hpf.trans (Nat.div_dvd_of_dvd (roughRadical_dvd W e))
  by_contra hn
  have hpg : p ∣ roughRadical W e := by
    apply Nat.dvd_of_mem_primeFactors
    rw [roughRadical_primeFactors]
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp,hpe,he.ne_zero⟩,by omega⟩
  have hd := Nat.dvd_gcd hpf hpg
  rw [hc.gcd_eq_one] at hd
  exact hpp.not_dvd_one hd

lemma canonical_low_smooth_of_no_middle (B W Y n e : ℕ)
    (he : e ∣ roughRadical B (n*(n+1)))
    (hno : ¬∃ p ∈ largePrimeSet Y W, p ∣ e) :
    (e/roughRadical W e).primeFactors ⊆ largePrimeSet B Y := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpf := Nat.dvd_of_mem_primeFactors hp
  have hpe := hpf.trans (Nat.div_dvd_of_dvd (roughRadical_dvd W e))
  have hpB := roughRadical_prime_large B _ p hpp (hpe.trans he)
  have hpW := canonical_low_prime_small W e p ((roughRadical_squarefree B _).squarefree_of_dvd he) hp
  have hpY : p ≤ Y := by
    by_contra h
    exact hno ⟨p,(mem_largePrimeSet_iff p Y W).mpr ⟨hpp,by omega,hpW⟩,hpe⟩
  exact (mem_largePrimeSet_iff p B Y).mpr ⟨hpp,hpB,hpY⟩

noncomputable def middlePrimeComplementAt (B D U Y W n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e/roughRadical W e ∧ (∃ p ∈ largePrimeSet Y W, p ∣ e) ∧
        D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma longLow_middle_point_error (B D U Y W n : ℕ) :
    |longLowComplementAt B D U Y W n-middlePrimeComplementAt B D U Y W n| ≤
      smoothLowComplementCount B U Y W n := by
  have hc : (smoothLowComplementCount B U Y W n : ℝ)=
      ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
        if U < e/roughRadical W e ∧ (e/roughRadical W e).primeFactors ⊆ largePrimeSet B Y then (1 : ℝ) else 0 := by
    simp only [smoothLowComplementCount,sum_boole]
  rw [hc,longLowComplementAt,middlePrimeComplementAt,← mul_sub,← sum_sub_distrib,
    abs_mul,roughRadical_moebius_abs,one_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  have hed := (Nat.mem_divisors.mp he).1
  have hepos := Nat.pos_of_dvd_of_pos hed (roughRadical_pos B _)
  by_cases hl : U < e/roughRadical W e
  · by_cases hm : ∃ p ∈ largePrimeSet Y W, p ∣ e
    · have hm' := hm
      obtain ⟨p,hp,hpd⟩ := hm
      obtain ⟨hpp,hpY,hpW⟩ := (mem_largePrimeSet_iff p Y W).mp hp
      have hY := hpY.trans_le (Nat.le_maxPrimeFac hepos.ne' hpp hpd)
      simp only [hl,hY,hm',true_and,sub_self,abs_zero]
      split_ifs <;> norm_num
    · have hs := canonical_low_smooth_of_no_middle B W Y n e hed hm
      simp only [hl,hm,hs,true_and,and_true,false_and,if_false,sub_zero,if_true]
      split_ifs
      · rw [abs_mul,divisorSideColour_abs,mul_one,← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := e)
      · norm_num
  · simp [hl]

/-- Only the middle-band signed term survives after this absolute error
estimate. No independence of the attached high factors is assumed. -/
theorem longLow_middle_mean_error_zero (B D U Y W : ℕ → ℕ) (L : ℕ)
    (hW : ∀ᶠ N : ℕ in atTop, 1 < W N ∧ N+1 ≤ (W N)^L)
    (hcount : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      (smoothComplementCount (B N) (U N) (Y N) (n+1) : ℝ))/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      |longLowComplementAt (B N) (D N) (U N) (Y N) (W N) (n+1)-
        middlePrimeComplementAt (B N) (D N) (U N) (Y N) (W N) (n+1)|)/N) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n _ => abs_nonneg _) (Nat.cast_nonneg N)) _
    (smoothLowComplementCount_mean_zero B U Y W L hW hcount)
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact sum_le_sum (fun n _ => longLow_middle_point_error _ _ _ _ _ _)

#print axioms longLow_middle_mean_error_zero
end Erdos371
