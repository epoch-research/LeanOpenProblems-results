import Submission.IteratedPrimeBlocks
import Submission.ComplementUnitMass

/-! Exact identification of an occupied first-prime block witness with the
untruncated unit complementary term. Repeated prime factors are retained via
the rough radical, and the exceptional input n=0 is kept explicit. -/
namespace Erdos371
open Finset FiniteSieve

noncomputable def fullRadicalParity (n : ℕ) : ℝ :=
  (-1 : ℝ)^((n*(n+1)).primeFactors.card)

noncomputable def untruncatedRoughUnit (B n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    divisorSideColour n (roughRadical B (n*(n+1)))

lemma roughRadical_primeFactors (B m : ℕ) :
    (roughRadical B m).primeFactors=m.primeFactors.filter (fun p => B<p) := by
  rw [roughRadical,Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)]

lemma roughRadical_moebius_parity (B m : ℕ) :
    (ArithmeticFunction.moebius (roughRadical B m) : ℝ)=
      (-1 : ℝ)^(m.primeFactors.filter (fun p => B<p)).card := by
  have hs := roughRadical_squarefree B m
  have hc : (roughRadical B m).primeFactors.card=ArithmeticFunction.cardFactors (roughRadical B m) := by
    rw [ArithmeticFunction.cardFactors_apply,← Nat.toFinset_factors]
    exact List.toFinset_card_of_nodup hs.nodup_primeFactorsList
  rw [ArithmeticFunction.moebius_apply_of_squarefree hs,← hc,roughRadical_primeFactors]
  norm_cast

lemma active_primesThrough_eq (B n : ℕ) (hn : 0<n) :
    activeBlockPrimes (primesThrough B) (activePrimeAtoms (primesThrough B) n)=
      (n*(n+1)).primeFactors.filter (fun p => p≤B) := by
  have hm : n*(n+1)≠0 := by positivity
  rw [activeBlockPrimes_arithmetic _ (fun p hp => ((mem_primesThrough p B).mp hp).1) n]
  ext p
  simp only [mem_filter,mem_primesThrough,Nat.mem_primeFactors,hm,ne_eq,not_false_eq_true,and_true]
  tauto

lemma roughRadical_moebius_eq_fullParity (B n : ℕ) (hn : 0<n) :
    (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)=
      fullRadicalParity n*naturalBlockParity (primesThrough B) n := by
  rw [roughRadical_moebius_parity]
  unfold fullRadicalParity naturalBlockParity blockParity
  rw [active_primesThrough_eq B n hn]
  have hc := card_filter_add_card_filter_not (s := (n*(n+1)).primeFactors) (fun p => B<p)
  simp only [not_lt] at hc
  rw [← hc,pow_add]
  have hs : ((-1 : ℝ)^((n*(n+1)).primeFactors.filter (fun p => p≤B)).card)^2=1 := by
    rw [← pow_mul,mul_comm _ 2,pow_mul]
    norm_num
  calc
    _ = (-1 : ℝ)^((n*(n+1)).primeFactors.filter (fun p => B<p)).card*
        ((-1 : ℝ)^((n*(n+1)).primeFactors.filter (fun p => p≤B)).card)^2 := by rw [hs,mul_one]
    _ = _ := by ring

lemma rough_first_colour_eq_block (B C n : ℕ) (hn : 0<n)
    (hocc : (activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n)).Nonempty) :
    naturalFirstBlockColour (largePrimeSet B C) n=
      divisorSideColour n (roughRadical B (n*(n+1))) := by
  let P := largePrimeSet B C
  let S := activeBlockPrimes P (activePrimeAtoms P n)
  let R := roughRadical B (n*(n+1))
  have hm : n*(n+1)≠0 := by positivity
  have hP (p : ℕ) (hp : p∈P) : p.Prime := ((mem_largePrimeSet_iff p B C).mp hp).1
  have hS : S=P.filter (fun p => p∣n*(n+1)) := activeBlockPrimes_arithmetic P hP n
  have hSrough (p : ℕ) (hp : p∈S) : p∈R.primeFactors := by
    rw [hS] at hp
    obtain ⟨hpP,hpd⟩ := mem_filter.mp hp
    have hpa := (mem_largePrimeSet_iff p B C).mp hpP
    rw [roughRadical_primeFactors]
    exact mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpa.1,hpd,hm⟩,hpa.2.1⟩
  obtain ⟨q,hq⟩ := hocc
  have hqR := hSrough q hq
  have hR : 1<R := Nat.nonempty_primeFactors.mp ⟨q,hqR⟩
  have hpR : R.minFac∈R.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd R,(roughRadical_pos B _).ne'⟩
  have hpdata := hpR
  rw [roughRadical_primeFactors] at hpdata
  obtain ⟨hpM,hpB⟩ := mem_filter.mp hpdata
  obtain ⟨hpp,hpd,_⟩ := Nat.mem_primeFactors.mp hpM
  have hpq : R.minFac≤q := Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hqR).two_le
    (Nat.dvd_of_mem_primeFactors hqR)
  have hpC : R.minFac≤C := by
    have hqS : q∈S := hq
    rw [hS] at hqS
    have hqP := (mem_filter.mp hqS).1
    exact hpq.trans ((mem_largePrimeSet_iff q B C).mp hqP).2.2
  have hpP : R.minFac∈P := (mem_largePrimeSet_iff _ B C).mpr ⟨hpp,hpB,hpC⟩
  have hpS : R.minFac∈S := by rw [hS]; exact mem_filter.mpr ⟨hpP,hpd⟩
  have hmin : S.min' ⟨q,hq⟩=R.minFac := by
    apply le_antisymm
    · exact min'_le S _ hpS
    · have hs := hSrough _ (S.min'_mem ⟨q,hq⟩)
      exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hs).two_le (Nat.dvd_of_mem_primeFactors hs)
  unfold naturalFirstBlockColour firstBlockColour
  change (if h : S.Nonempty then atomColour (S.min' h) (activePrimeAtoms P n) else 0)=_
  rw [dif_pos ⟨q,hq⟩,hmin,prime_atomColour_arithmetic P R.minFac n hpP hpp hpd]
  rfl

lemma fullRadicalParity_abs (n : ℕ) : |fullRadicalParity n|=1 := by
  simp only [fullRadicalParity,abs_pow,abs_neg,abs_one,one_pow]

lemma untruncatedRoughUnit_abs (B n : ℕ) : |untruncatedRoughUnit B n|=1 := by
  unfold untruncatedRoughUnit
  rw [abs_mul,← Int.cast_abs,ArithmeticFunction.abs_moebius_eq_one_of_squarefree (roughRadical_squarefree B _)]
  simp only [Int.cast_one,one_mul,divisorSideColour]
  split_ifs <;> norm_num

/-- The witness equals the actual unit term whenever its first-prime block
is occupied. The common multiplier is independent of the rough cutoff B. -/
theorem untruncatedRoughUnit_eq_witness (B C n : ℕ) (hn : 0<n)
    (hocc : (activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n)).Nonempty) :
    untruncatedRoughUnit B n=
      fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n := by
  unfold untruncatedRoughUnit primeBlockWitness
  rw [roughRadical_moebius_eq_fullParity B n hn,← rough_first_colour_eq_block B C n hn hocc]
  ring

lemma untruncatedRoughUnit_witness_point_error (B C n : ℕ) :
    |untruncatedRoughUnit B n-fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n| ≤
      (if n=0 then (2 : ℝ) else 0)+
        (if activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n)=∅ then 2 else 0) := by
  have hw : |fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n|≤1 := by
    rw [abs_mul,fullRadicalParity_abs,one_mul]
    exact primeBlockWitness_abs_le _ _ n
  have hb : |untruncatedRoughUnit B n-fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n|≤2 := by
    have h := abs_sub (untruncatedRoughUnit B n)
      (fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n)
    rw [untruncatedRoughUnit_abs] at h
    linarith
  by_cases hn : n=0
  · rw [if_pos hn]
    exact hb.trans (le_add_of_nonneg_right (by split_ifs <;> norm_num))
  · rw [if_neg hn,zero_add]
    split_ifs with he
    · exact hb
    · rw [untruncatedRoughUnit_eq_witness B C n (by omega) (nonempty_iff_ne_empty.mpr he),sub_self,abs_zero]

/-- The discrepancy between a witness mean and the untruncated unit mean is
paid only by the empty-block proportion and the single input n=0. -/
theorem untruncatedRoughUnit_witness_mean_error (B C N : ℕ) :
    |(∑ n ∈ range N, untruncatedRoughUnit B n)/N-
      (∑ n ∈ range N, fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n)/N| ≤
      2/(N : ℝ)+2*(emptyPrimeBlockCount (largePrimeSet B C) N : ℝ)/N := by
  have h0 : (∑ n ∈ range N, if n=0 then (2 : ℝ) else 0)≤2 := by
    simp only [sum_ite_eq',mem_range]
    split_ifs <;> norm_num
  have he : (∑ n ∈ range N, if activeBlockPrimes (largePrimeSet B C)
      (activePrimeAtoms (largePrimeSet B C) n)=∅ then (2 : ℝ) else 0) =
        2*(emptyPrimeBlockCount (largePrimeSet B C) N : ℝ) := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    dsimp only [emptyPrimeBlockCount]
    ring
  have hs := sum_le_sum (s := range N) (fun n _ => untruncatedRoughUnit_witness_point_error B C n)
  rw [sum_add_distrib,he] at hs
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ)≤N)]
  calc
    _ ≤ (∑ n ∈ range N, |untruncatedRoughUnit B n-
        fullRadicalParity n*primeBlockWitness (primesThrough B) (largePrimeSet B C) n|)/N :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
    _ ≤ (2+2*(emptyPrimeBlockCount (largePrimeSet B C) N : ℝ))/N :=
      div_le_div_of_nonneg_right (hs.trans (add_le_add h0 le_rfl)) (Nat.cast_nonneg N)
    _ = _ := by ring

#print axioms untruncatedRoughUnit_eq_witness
#print axioms untruncatedRoughUnit_witness_mean_error
end Erdos371
