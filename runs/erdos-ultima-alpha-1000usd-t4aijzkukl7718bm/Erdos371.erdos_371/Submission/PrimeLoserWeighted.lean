import Submission.WeightedCofactorPairs
import Submission.PrimeWinnerFlux

/-! Weighted loser counts and a halving inequality. The weights are kept
inside the cofactor sieve instead of bounded by a single global maximum. -/
namespace Erdos371
open Finset FiniteSieve

noncomputable def largestPrimeCofactor (n : ℕ) : ℕ :=
  max (primeCofactor n) (primeCofactor (n+1))

lemma bothAbove_cofactor_data (B N z n : ℕ) (hB : 1 ≤ B) (hz : z ≤ B)
    (hn : n ∈ bothAboveSet B N) :
    1 < n ∧ primeCofactor n ∈ Icc 1 (N/(B+1)) ∧
      primeCofactor (n+1) ∈ Icc 1 (N/(B+1)) ∧
      n ∈ cofactorPrimePairSet N (primeCofactor n) (primeCofactor (n+1)) z := by
  obtain ⟨hnN,hp,hq⟩ := mem_filter.mp hn
  have hnN' := mem_range.mp hnN
  have hn2 : 1 < n := (Nat.one_lt_maxPrimeFac_iff n).mp (by omega)
  have hd := primeCofactor_data n hn2
  have he := primeCofactor_data (n+1) (by omega)
  have ha : primeCofactor n ≤ N/(B+1) := by
    change n/Nat.maxPrimeFac n ≤ _
    exact (Nat.div_le_div_right (by omega : n ≤ N)).trans
      (Nat.div_le_div_left (by omega) (by omega))
  have hb : primeCofactor (n+1) ≤ N/(B+1) := by
    change (n+1)/Nat.maxPrimeFac (n+1) ≤ _
    exact (Nat.div_le_div_right (by omega : n+1 ≤ N)).trans
      (Nat.div_le_div_left (by omega) (by omega))
  refine ⟨hn2,mem_Icc.mpr ⟨hd.1,ha⟩,mem_Icc.mpr ⟨he.1,hb⟩,?_⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hd.2.1,he.2.1,?_⟩
  rw [hd.2.2,he.2.2]
  exact ⟨Nat.prime_maxPrimeFac_of_one_lt n hn2,
    Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),by omega,by omega⟩

lemma bothAbove_weighted_cofactor_le (B N z : ℕ) (hB : 1 ≤ B) (hz : z ≤ B) :
    (∑ n ∈ bothAboveSet B N, (largestPrimeCofactor n : ℝ)) ≤
      cofactorWeightedPrimePairCount N (N/(B+1)) z := by
  let T := Icc 1 (N/(B+1)) ×ˢ Icc 1 (N/(B+1))
  let f (n : ℕ) := (primeCofactor n,primeCofactor (n+1))
  have hmap : ∀ n ∈ bothAboveSet B N, f n ∈ T := by
    intro n hn
    have hd := bothAbove_cofactor_data B N z n hB hz hn
    exact mem_product.mpr ⟨hd.2.1,hd.2.2.1⟩
  rw [← sum_fiberwise_of_maps_to hmap (fun n => (largestPrimeCofactor n : ℝ))]
  have he : cofactorWeightedPrimePairCount N (N/(B+1)) z =
      ∑ ab ∈ T, (max ab.1 ab.2 : ℕ)*((cofactorPrimePairSet N ab.1 ab.2 z).card : ℝ) := by
    rw [sum_product]
    rfl
  rw [he]
  apply sum_le_sum
  intro ab hab
  have hs : ((bothAboveSet B N).filter fun n => f n = ab) ⊆
      cofactorPrimePairSet N ab.1 ab.2 z := by
    intro n hn
    obtain ⟨hn,he⟩ := mem_filter.mp hn
    have hd := (bothAbove_cofactor_data B N z n hB hz hn).2.2.2
    have he1 : primeCofactor n = ab.1 := congrArg Prod.fst he
    have he2 : primeCofactor (n+1) = ab.2 := congrArg Prod.snd he
    simpa only [he1,he2] using hd
  calc
    _ = ∑ _n ∈ (bothAboveSet B N).filter (fun n => f n = ab), ((max ab.1 ab.2 : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro n hn
      have he := (mem_filter.mp hn).2
      exact congrArg (fun p : ℕ × ℕ => ((max p.1 p.2 : ℕ) : ℝ)) he
    _ ≤ ∑ _n ∈ cofactorPrimePairSet N ab.1 ab.2 z, ((max ab.1 ab.2 : ℕ) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)
    _ = _ := by simp [mul_comm]

noncomputable def loserMultiplicityWeight (N n : ℕ) : ℝ :=
  2*(N : ℝ)/primeLoser n+1

noncomputable def weightedLoserCount (B N : ℕ) : ℝ :=
  ∑ n ∈ bothAboveSet B N, loserMultiplicityWeight N n

lemma weightedLoserCount_nonneg (B N : ℕ) : 0 ≤ weightedLoserCount B N := by
  apply sum_nonneg
  intro n hn
  unfold loserMultiplicityWeight
  positivity

lemma loser_times_largestCofactor_ge (n : ℕ) :
    n ≤ primeLoser n*largestPrimeCofactor n := by
  have ha := maxPrimeFac_mul_primeCofactor n
  have hb := maxPrimeFac_mul_primeCofactor (n+1)
  have hmax1 : primeCofactor n ≤ largestPrimeCofactor n := le_max_left _ _
  have hmax2 : primeCofactor (n+1) ≤ largestPrimeCofactor n := le_max_right _ _
  rcases min_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h | h
  · unfold primeLoser
    rw [h.1]
    nlinarith
  · unfold primeLoser
    rw [h.1]
    nlinarith

lemma loserMultiplicityWeight_late_bound (N n : ℕ)
    (hn : N/2 ≤ n) (hn2 : 1 < n) :
    loserMultiplicityWeight N n ≤ 7*(largestPrimeCofactor n : ℝ) := by
  have hNn : N ≤ 3*n := by omega
  have hp := (Nat.prime_maxPrimeFac_of_one_lt n hn2).pos
  have hq := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).pos
  have hlos : 0 < primeLoser n := lt_min hp hq
  have hlosr : (0 : ℝ) < primeLoser n := by exact_mod_cast hlos
  have he := loser_times_largestCofactor_ge n
  have hNc : (N : ℝ) ≤ 3*primeLoser n*largestPrimeCofactor n := by
    exact_mod_cast (show N ≤ 3*primeLoser n*largestPrimeCofactor n by nlinarith)
  have hdiv : (N : ℝ)/primeLoser n ≤ 3*largestPrimeCofactor n :=
    (div_le_iff₀ hlosr).mpr (by nlinarith)
  have hco := (primeCofactor_data n hn2).1
  have hco' : (1 : ℝ) ≤ largestPrimeCofactor n := by
    exact_mod_cast hco.trans_le (le_max_left (primeCofactor n) (primeCofactor (n+1)))
  unfold loserMultiplicityWeight
  simp only [mul_div_assoc] at *
  nlinarith

lemma loserMultiplicityWeight_halving_bound (N n : ℕ) (hN : 2 ≤ N) :
    loserMultiplicityWeight N n ≤ 3*loserMultiplicityWeight (N/2) n := by
  have hN' : (N : ℝ) ≤ 3*((N/2 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 3*(N/2) by omega)
  have hd := div_le_div_of_nonneg_right hN' (Nat.cast_nonneg (α := ℝ) (primeLoser n))
  unfold loserMultiplicityWeight
  simp only [mul_div_assoc] at *
  nlinarith

/-- Splitting at half the endpoint preserves a shrinking cofactor range.
The first term can be iterated; the second retains the actual cofactor. -/
theorem weightedLoserCount_halving (B N z : ℕ) (hB : 1 ≤ B) (hz : z ≤ B)
    (hN : 2 ≤ N) :
    weightedLoserCount B N ≤ 3*weightedLoserCount B (N/2)+
      7*cofactorWeightedPrimePairCount N (N/(B+1)) z := by
  have he : (bothAboveSet B N).filter (fun n => n < N/2) = bothAboveSet B (N/2) := by
    ext n
    simp only [bothAboveSet,mem_filter,mem_range]
    have hh := Nat.div_le_self N 2
    omega
  have hs := sum_filter_add_sum_filter_not (bothAboveSet B N)
    (fun n => n < N/2) (loserMultiplicityWeight N)
  have hfirst : (∑ n ∈ (bothAboveSet B N).filter (fun n => n < N/2),
      loserMultiplicityWeight N n) ≤ 3*weightedLoserCount B (N/2) := by
    rw [he,weightedLoserCount,mul_sum]
    exact sum_le_sum fun n _ => loserMultiplicityWeight_halving_bound N n hN
  have hlast : (∑ n ∈ (bothAboveSet B N).filter (fun n => ¬n < N/2),
      loserMultiplicityWeight N n) ≤
        7*cofactorWeightedPrimePairCount N (N/(B+1)) z := by
    calc
      _ ≤ ∑ n ∈ (bothAboveSet B N).filter (fun n => ¬n < N/2),
          7*(largestPrimeCofactor n : ℝ) := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hn,hhalf⟩ := mem_filter.mp hn
        exact loserMultiplicityWeight_late_bound N n (not_lt.mp hhalf)
          (bothAbove_cofactor_data B N z n hB hz hn).1
      _ ≤ ∑ n ∈ bothAboveSet B N, 7*(largestPrimeCofactor n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (bothAbove_weighted_cofactor_le B N z hB hz) (by norm_num)
  unfold weightedLoserCount at hfirst ⊢
  linarith

#print axioms bothAbove_weighted_cofactor_le
#print axioms weightedLoserCount_halving
end Erdos371
