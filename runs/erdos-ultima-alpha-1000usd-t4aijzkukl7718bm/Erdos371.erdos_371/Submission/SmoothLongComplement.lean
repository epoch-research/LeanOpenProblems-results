import Submission.ExponentialPrimePatternTail
import Submission.LongComplementCriterion

/-! Absolute control of the smooth part of the remaining long complementary
sum. This does not control indices containing a prime above the smoothness
cutoff, in particular long complementary prime indices. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def smoothComplementCount (B U Y n : ℕ) : ℕ :=
  ((roughRadical B (n*(n+1))).divisors.filter
    (fun e => U < e ∧ e.primeFactors ⊆ largePrimeSet B Y)).card

/-- A long squarefree divisor supported on the band (B,Y] forces a large
active count when U≥Y^L. The total number of its possibilities is at most 2^m. -/
lemma smoothComplementCount_high_count_bound (B U Y L n : ℕ) (hn : 0 < n)
    (hY : 1 ≤ Y) (hU : Y^L ≤ U) :
    (smoothComplementCount B U Y n : ℝ) ≤
      if L ≤ (activeBlockPrimes (largePrimeSet B Y) (activePrimeAtoms (largePrimeSet B Y) n)).card then
        (2 : ℝ)^(activeBlockPrimes (largePrimeSet B Y) (activePrimeAtoms (largePrimeSet B Y) n)).card else 0 := by
  let R := roughRadical B (n*(n+1))
  let A := activeBlockPrimes (largePrimeSet B Y) (activePrimeAtoms (largePrimeSet B Y) n)
  let T := R.divisors.filter (fun e => U < e ∧ e.primeFactors ⊆ largePrimeSet B Y)
  have hA : A=R.primeFactors.filter (fun p => p ≤ Y) := rough_active_block_eq B Y n hn
  have hsq (e : ℕ) (he : e ∈ T) : Squarefree e :=
    (roughRadical_squarefree B _).squarefree_of_dvd (Nat.mem_divisors.mp (mem_filter.mp he).1).1
  have hsub (e : ℕ) (he : e ∈ T) : e.primeFactors ⊆ A := by
    obtain ⟨hed,_,heP⟩ := mem_filter.mp he
    have hpf := Nat.primeFactors_mono (Nat.mem_divisors.mp hed).1 (roughRadical_pos B _).ne'
    intro p hp
    rw [hA]
    exact mem_filter.mpr ⟨hpf hp,((mem_largePrimeSet_iff p B Y).mp (heP hp)).2.2⟩
  have hcount : T.card ≤ 2^A.card := by
    rw [← card_powerset]
    apply card_le_card_of_injOn Nat.primeFactors (fun e he => mem_powerset.mpr (hsub e he))
    intro e he f hf hef
    have heq := Nat.prod_primeFactors_of_squarefree (hsq e he)
    have hfq := Nat.prod_primeFactors_of_squarefree (hsq f hf)
    rw [← heq,← hfq,hef]
  change (T.card : ℝ) ≤ if L ≤ A.card then (2 : ℝ)^A.card else 0
  by_cases hm : L ≤ A.card
  · rw [if_pos hm]
    exact_mod_cast hcount
  · rw [if_neg hm]
    have hT : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have heU := (mem_filter.mp he).2.1
      have hpf := hsub e he
      have hep : e ≤ Y^e.primeFactors.card := by
        calc
          e = ∏ p ∈ e.primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hsq e he)).symm
          _ ≤ _ := by
            simpa only [prod_const] using prod_le_prod' (fun p hp =>
              ((mem_largePrimeSet_iff p B Y).mp ((mem_filter.mp he).2.2 hp)).2.2)
      have hcard : e.primeFactors.card ≤ L := (card_le_card hpf).trans (by omega)
      have hp := Nat.pow_le_pow_right (by omega : 0 < Y) hcard
      omega
    rw [hT,card_empty,Nat.cast_zero]

noncomputable def smoothComplementAfterAt (B D U Y n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e ∧ e.primeFactors ⊆ largePrimeSet B Y ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma smoothComplementAfterAt_abs_le_count (B D U Y n : ℕ) :
    |smoothComplementAfterAt B D U Y n| ≤ smoothComplementCount B U Y n := by
  rw [smoothComplementAfterAt,abs_mul,roughRadical_moebius_abs,one_mul]
  have he : (smoothComplementCount B U Y n : ℝ) =
      ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
        if U < e ∧ e.primeFactors ⊆ largePrimeSet B Y then (1 : ℝ) else 0 := by
    simp only [smoothComplementCount,sum_boole]
  rw [he]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro e _
  by_cases hu : U < e
  · by_cases hp : e.primeFactors ⊆ largePrimeSet B Y
    · simp only [hu,hp,true_and,if_true]
      split_ifs
      · rw [abs_mul,divisorSideColour_abs,mul_one,← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := e))
      · norm_num
    · simp [hp,hu]
  · simp [hu]

/-- For every fixed a, all long complementary indices whose prime factors
are at most B^a have vanishing mean ABSOLUTE contribution. D is arbitrary;
the moving size condition can only reduce the absolute bound. -/
theorem smoothComplementAfterAt_absolute_zero (B D U : ℕ → ℕ)
    (hB : Tendsto B atTop atTop)
    (hU : ∀ k : ℕ, ∀ᶠ N in atTop, (B N)^k ≤ U N) (a : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      |smoothComplementAfterAt (B N) (D N) (U N) ((B N)^a) (n+1)|)/N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M : ℝ := 16*(a+1)
  obtain ⟨L,hL⟩ := prime_pattern_exponential_tail_uniform M ε hε
  have htlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)).atTop_div_const
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hB.eventually_gt_atTop 1,htlog.eventually_ge_atTop 2,hU (a*L),
    eventually_gt_atTop (0 : ℕ)] with N hb hl hu hN
  let P := largePrimeSet (B N) ((B N)^a)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := ((mem_largePrimeSet_iff p _ _).mp hp).1
  have hmass : primeReciprocalMass P ≤ M := by
    have hh := short_power_band_mass_upper (B N) a hb hl
    have hnonneg := primeReciprocalMass_nonneg P
    change 2*primeReciprocalMass P ≤ M at hh
    linarith
  have hmean := hL N hN P hP hmass
  have hy : 1 ≤ (B N)^a := Nat.pow_pos (by omega)
  have hprod : ((B N)^a)^L ≤ U N := by rw [← pow_mul]; exact hu
  have hs := sum_le_sum (s := range N) (fun n _ =>
    (smoothComplementAfterAt_abs_le_count (B N) (D N) (U N) ((B N)^a) (n+1)).trans
      (smoothComplementCount_high_count_bound (B N) (U N) ((B N)^a) L (n+1) (by omega) hy hprod))
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (sum_nonneg fun n _ => abs_nonneg _) (Nat.cast_nonneg N))]
  exact hd.trans_lt hmean

#print axioms smoothComplementAfterAt_absolute_zero
end Erdos371
