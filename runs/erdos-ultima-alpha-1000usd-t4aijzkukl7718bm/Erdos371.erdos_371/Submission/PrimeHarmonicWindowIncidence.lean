import Submission.DyadicSeriesTools
import Submission.PrimeCurrentAbsoluteBudget

/-! Harmonic incidence bounds uniform in the prime and both endpoints. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def reciprocalInterval (L U : ℕ) : ℝ :=
  ∑ n ∈ Ico L U, (1 : ℝ)/n

noncomputable def multiplesReciprocalInterval (p L U : ℕ) : ℝ :=
  ∑ n ∈ Ico L U, if p ∣ n then (1 : ℝ)/n else 0

lemma reciprocalInterval_nonneg (L U : ℕ) : 0≤reciprocalInterval L U := by
  unfold reciprocalInterval
  positivity

lemma predecessor_residue_step (p n : ℕ) (hp : 1<p) (hn : 0<n) :
    ((n%p : ℕ) : ℝ)-((n-1)%p : ℕ) =
      1-(if p ∣ n then (p : ℝ) else 0) := by
  have h := Nat.add_mod_add_ite (n-1) 1 p
  rw [Nat.sub_add_cancel hn,Nat.mod_eq_of_lt hp] at h
  have hr := Nat.mod_lt (n-1) (by omega : 0<p)
  by_cases hd : p ∣ n
  · have hz := Nat.mod_eq_zero_of_dvd hd
    rw [hz] at h ⊢
    have he : (n-1)%p+1=p := by split_ifs at h <;> omega
    have her : (((n-1)%p : ℕ) : ℝ)+1=p := by exact_mod_cast he
    rw [if_pos hd]
    norm_num only [Nat.cast_zero]
    linarith
  · have hz : n%p≠0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have he : n%p=(n-1)%p+1 := by split_ifs at h <;> omega
    rw [if_neg hd,sub_zero]
    exact_mod_cast (show (n%p : ℤ)-((n-1)%p : ℕ)=1 by omega)

lemma multiples_reciprocal_core_bound (p L U : ℕ) (hp : 1<p)
    (hL : p≤L) (hLU : L≤U) :
    (p : ℝ)*multiplesReciprocalInterval p L U≤reciprocalInterval L U+1 := by
  let r (n : ℕ) : ℝ := ((n-1)%p : ℕ)/(p : ℝ)
  have hpp : (0 : ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hLL : (0 : ℝ)<L := by exact_mod_cast (by omega : 0<L)
  have hr (n : ℕ) : 0≤r n ∧ r n≤1 := by
    constructor
    · dsimp [r]; positivity
    · dsimp [r]
      apply (div_le_one hpp).mpr
      exact_mod_cast (Nat.mod_lt (n-1) (by omega : 0<p)).le
  have he (n : ℕ) (hn : n∈Ico L U) :
      (p : ℝ)*(if p ∣ n then (1 : ℝ)/n else 0)-1/(n : ℝ) =
        -(p : ℝ)*((r (n+1)-r n)/(n : ℝ)) := by
    have hnpos : 0<n := by have := (mem_Ico.mp hn).1; omega
    have hs := predecessor_residue_step p n hp hnpos
    dsimp only [r]
    rw [Nat.add_sub_cancel]
    by_cases hd : p ∣ n
    · rw [if_pos hd] at hs ⊢
      field_simp
      nlinarith
    · rw [if_neg hd] at hs ⊢
      field_simp
      nlinarith
  have hsum : (p : ℝ)*multiplesReciprocalInterval p L U-reciprocalInterval L U =
      -(p : ℝ)*∑ n ∈ Ico L U, (r (n+1)-r n)/(n : ℝ) := by
    unfold multiplesReciprocalInterval reciprocalInterval
    rw [mul_sum,← sum_sub_distrib,sum_congr rfl he,← mul_sum]
  have hd := reciprocal_derivative_Ico_bound r hr L U (by omega) hLU
  have hb : |(p : ℝ)*multiplesReciprocalInterval p L U-reciprocalInterval L U|≤1 := by
    rw [hsum,abs_mul,abs_neg,abs_of_pos hpp]
    calc
      _ ≤ (p : ℝ)*(1/(L : ℝ)) := mul_le_mul_of_nonneg_left hd hpp.le
      _ ≤ 1 := by rw [mul_one_div]; exact (div_le_one hLL).mpr (by exact_mod_cast hL)
  linarith [(abs_le.mp hb).2]

/-- Multiples of p have harmonic mass at most (H+1)/p on ANY positive
interval of harmonic mass H. The additive constant is independent of p. -/
theorem multiples_reciprocal_interval_bound (p L U : ℕ) (hp : 0<p) (hL : 0<L) :
    (p : ℝ)*multiplesReciprocalInterval p L U≤reciprocalInterval L U+1 := by
  by_cases hp1 : p=1
  · subst p
    simp only [multiplesReciprocalInterval,reciprocalInterval,one_dvd,if_true,
      Nat.cast_one,one_mul]
    linarith
  let T := max L p
  have hmass : multiplesReciprocalInterval p L U=multiplesReciprocalInterval p T U := by
    symm
    apply sum_subset (show Ico T U⊆Ico L U from
      fun n hn => mem_Ico.mpr ⟨(le_max_left _ _).trans (mem_Ico.mp hn).1,(mem_Ico.mp hn).2⟩)
    intro n hn hnt
    have hnpos : 0<n := hL.trans_le (mem_Ico.mp hn).1
    have hnp : n<p := by
      have h := mem_Ico.mp hn
      simp only [mem_Ico,not_and] at hnt
      dsimp [T] at hnt
      omega
    rw [if_neg (fun hd => (Nat.le_of_dvd hnpos hd).not_gt hnp)]
  have hrec : reciprocalInterval T U≤reciprocalInterval L U := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Ico.mpr ⟨(le_max_left _ _).trans (mem_Ico.mp hn).1,(mem_Ico.mp hn).2⟩
    · intro n _ _; positivity
  rw [hmass]
  by_cases hTU : T≤U
  · exact (multiples_reciprocal_core_bound p T U (by omega) (le_max_right _ _) hTU).trans
      (by linarith)
  · simp only [multiplesReciprocalInterval,Finset.Ico_eq_empty_of_le (not_le.mp hTU).le,sum_empty,mul_zero]
    linarith [reciprocalInterval_nonneg L U]

lemma primeLabelReciprocal_le_multiples (p n : ℕ) :
    primeLabelReciprocal p n ≤ (if p ∣ n then (1 : ℝ)/n else 0) := by
  unfold primeLabelReciprocal
  split_ifs with h hp
  · rfl
  · exact False.elim (hp (h ▸ Nat.maxPrimeFac_dvd))
  · positivity
  · rfl

lemma reciprocalInterval_shift_le (L U : ℕ) (hL : 0<L) :
    reciprocalInterval (L+1) (U+1)≤reciprocalInterval L U := by
  unfold reciprocalInterval
  rw [← sum_Ico_add' (fun n : ℕ => (1 : ℝ)/n) L U 1]
  apply sum_le_sum
  intro n hn
  have hnpos : 0<n := hL.trans_le (mem_Ico.mp hn).1
  apply one_div_le_one_div_of_le (by exact_mod_cast hnpos)
  push_cast
  linarith

/-- A uniform incidence bound on the WHOLE window, sharper in its ratio
dependence than the earlier 2a/p bound for [N,aN). -/
theorem primeWinner_harmonic_window_label_bound (p L U : ℕ)
    (hp : 0<p) (hL : 0<L) (hLU : L≤U) :
    (p : ℝ)*|rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L| ≤
      3*(reciprocalInterval L U+1) := by
  have hb : |rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L| ≤
      multiplesReciprocalInterval p L U+2*multiplesReciprocalInterval p (L+1) (U+1) := by
    unfold rawPrimeWinnerHarmonic
    rw [← sum_Ico_eq_sub _ hLU,← Real.norm_eq_abs]
    calc
      _ ≤ ∑ n ∈ Ico L U, ‖primeWinnerHarmonicTerm p n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ico L U,
          ((if p ∣ n then (1 : ℝ)/n else 0)+2*(if p ∣ n+1 then (1 : ℝ)/(n+1) else 0)) := by
        apply sum_le_sum
        intro n _
        have h := primeWinnerLoserHarmonicTerm_norm_bound p n
        have h₁ := primeLabelReciprocal_le_multiples p n
        have h₂ := primeLabelReciprocal_le_multiples p (n+1)
        push_cast at h₂
        linarith [norm_nonneg (primeLoserHarmonicTerm p n)]
      _ = _ := by
        rw [sum_add_distrib,← mul_sum]
        congr 1
        congr 1
        unfold multiplesReciprocalInterval
        rw [← sum_Ico_add' (fun n => if p ∣ n then (1 : ℝ)/n else 0) L U 1]
        simp only [Nat.cast_add,Nat.cast_one]
  have h := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) p)
  have h₁ := multiples_reciprocal_interval_bound p L U hp hL
  have h₂ := multiples_reciprocal_interval_bound p (L+1) (U+1) hp (by omega)
  have h₃ := reciprocalInterval_shift_le L U hL
  nlinarith

#print axioms multiples_reciprocal_interval_bound
#print axioms primeWinner_harmonic_window_label_bound
end Erdos371
