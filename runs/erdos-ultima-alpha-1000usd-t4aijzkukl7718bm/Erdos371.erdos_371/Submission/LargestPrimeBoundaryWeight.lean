import Submission.LargestPrimeToggle

/-! An exact moving-smoothness form of the largest-prime toggle. These
identities retain the smoothness weight; no cancellation under that weight
is asserted. -/
namespace Erdos371
open Finset

lemma maxPrimeFac_divisor_lt_iff (R d : ℕ) (hR : 1 < R) (hd : d ∣ R) :
    Nat.maxPrimeFac d < Nat.maxPrimeFac R ↔ Nat.maxPrimeFac R ∉ d.primeFactors := by
  have hR0 : R ≠ 0 := by omega
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  have hp := Nat.prime_maxPrimeFac_of_one_lt R hR
  by_cases hd1 : d = 1
  · simp [hd1, hp.one_lt]
  · have hd2 : 1 < d := by omega
    have hdp := Nat.prime_maxPrimeFac_of_one_lt d hd2
    have hle : Nat.maxPrimeFac d ≤ Nat.maxPrimeFac R :=
      Nat.le_maxPrimeFac hR0 hdp (Nat.maxPrimeFac_dvd.trans hd)
    constructor
    · intro h hm
      exact (Nat.le_maxPrimeFac hd0.ne' hp (Nat.dvd_of_mem_primeFactors hm)).not_gt h
    · intro h
      apply lt_of_le_of_ne hle
      intro he
      apply h
      exact Nat.mem_primeFactors.mpr ⟨hp, he ▸ Nat.maxPrimeFac_dvd, hd0.ne'⟩

lemma powerset_erase_eq_filter_not_mem (s : Finset ℕ) (p : ℕ) :
    (s.erase p).powerset = s.powerset.filter (fun t => p ∉ t) := by
  ext t
  simp only [mem_powerset, mem_filter]
  constructor
  · intro h
    exact ⟨fun q hq => mem_of_mem_erase (h hq), fun hp => notMem_erase p s (h hp)⟩
  · rintro ⟨h, hp⟩ q hq
    exact mem_erase.mpr ⟨fun he => hp (he ▸ hq), h hq⟩

/-- The cutoff now depends only on the divisor and D, rather than on a
choice of the largest prime to be omitted from each subset. -/
theorem squarefree_tail_moving_smooth_weight (R D : ℕ) (hR : 1 < R)
    (hs : Squarefree R) (hD : Nat.maxPrimeFac R ≤ D) (f : ℕ → ℝ) :
    (∑ d ∈ R.divisors, if D < d then leastFactorTerm f d else 0) =
      -∑ d ∈ R.divisors,
        if d ≤ D ∧ max (Nat.maxPrimeFac d) (D / d) < Nat.maxPrimeFac R then
          leastFactorTerm f d else 0 := by
  have hR0 : R ≠ 0 := by omega
  have hp := Nat.prime_maxPrimeFac_of_one_lt R hR
  have hpm : Nat.maxPrimeFac R ∈ R.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Nat.maxPrimeFac_dvd, hR0⟩
  rw [squarefree_tail_eq_subset_tail R D hs hR0 f]
  rw [subset_tail_toggle_largest R.primeFactors (Nat.maxPrimeFac R) D f hpm
    (fun q hq => Nat.le_maxPrimeFac hR0 (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq)) hp.one_lt.le hD]
  rw [powerset_erase_eq_filter_not_mem, sum_filter]
  congr 1
  rw [← sum_squarefree_divisors_eq_powerset R hR0
    (fun t => if Nat.maxPrimeFac R ∉ t then
      if (∏ q ∈ t, q) ≤ D ∧ D < Nat.maxPrimeFac R * (∏ q ∈ t, q) then
        subsetMinTerm f t else 0 else 0)]
  apply sum_congr rfl
  intro d hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hds := hs.squarefree_of_dvd hdvd
  rw [if_pos hds, Nat.prod_primeFactors_of_squarefree hds]
  have hcut : D < Nat.maxPrimeFac R * d ↔ D / d < Nat.maxPrimeFac R := by
    rw [Nat.div_lt_iff_lt_mul hd0]
  have hnot := maxPrimeFac_divisor_lt_iff R d hR hdvd
  simp only [← hnot, hcut, leastFactorTerm_eq, if_pos hds, max_lt_iff]
  split_ifs <;> tauto

lemma roughRadical_maxPrimeFac (B m : ℕ) (hm : m ≠ 0)
    (hR : 1 < roughRadical B m) :
    Nat.maxPrimeFac (roughRadical B m) = Nat.maxPrimeFac m := by
  have hpR := Nat.prime_maxPrimeFac_of_one_lt _ hR
  have hle : Nat.maxPrimeFac (roughRadical B m) ≤ Nat.maxPrimeFac m :=
    Nat.le_maxPrimeFac hm hpR (Nat.maxPrimeFac_dvd.trans (roughRadical_dvd B m))
  have hm1 : 1 < m := (Nat.one_lt_maxPrimeFac_iff m).mp (hpR.one_lt.trans_le hle)
  have hpm := Nat.prime_maxPrimeFac_of_one_lt m hm1
  have hB : B < Nat.maxPrimeFac m :=
    (roughRadical_prime_large B m _ hpR Nat.maxPrimeFac_dvd).trans_le hle
  have hmem : Nat.maxPrimeFac m ∈ m.primeFactors.filter (fun p => B < p) :=
    mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpm, Nat.maxPrimeFac_dvd, hm⟩, hB⟩
  apply le_antisymm hle
  exact Nat.le_maxPrimeFac (roughRadical_pos B m).ne' hpm (dvd_prod_of_mem id hmem)

noncomputable def commonSmoothWeight (U n : ℕ) : ℝ :=
  if Nat.maxPrimeFac n ≤ U ∧ Nat.maxPrimeFac (n+1) ≤ U then 1 else 0

/-- The actual rough tail, with its input-dependent largest-prime exclusion
replaced by a common smoothness weight at max(P(d), floor(D/d)). -/
theorem roughLargeDivisorTail_moving_smooth_weight_of_nontrivial (B D n : ℕ) (hn : 0 < n)
    (hR : 1 < roughRadical B (n*(n+1)))
    (hD : Nat.maxPrimeFac (n*(n+1)) ≤ D) :
    roughLargeDivisorTail B D n =
      -∑ d ∈ (roughRadical B (n*(n+1))).divisors,
        if d ≤ D then
          leastFactorTerm (fun p => if p ∣ n+1 then 1 else -1) d *
            (1 - commonSmoothWeight (max (Nat.maxPrimeFac d) (D / d)) n)
        else 0 := by
  have hm : n*(n+1) ≠ 0 := by positivity
  have hp := roughRadical_maxPrimeFac B (n*(n+1)) hm hR
  have hD1 : 1 ≤ D :=
    ((Nat.prime_maxPrimeFac_of_one_lt _ hR).one_lt.le.trans (hp.le.trans hD))
  rw [roughLargeDivisorTail_eq_subset_tail B D n hn hD1,
    ← squarefree_tail_eq_subset_tail _ D (roughRadical_squarefree B _) (roughRadical_pos B _).ne',
    squarefree_tail_moving_smooth_weight _ D hR (roughRadical_squarefree B _) (hp ▸ hD), hp]
  congr 1
  apply sum_congr rfl
  intro d hd
  have he (U : ℕ) :
      Nat.maxPrimeFac n ≤ U ∧ Nat.maxPrimeFac (n+1) ≤ U ↔
        Nat.maxPrimeFac (n*(n+1)) ≤ U := by
    rw [Nat.maxPrimeFac_mul hn.ne' (by omega), max_le_iff]
  simp only [commonSmoothWeight, he]
  by_cases hdD : d ≤ D
  · by_cases hu : Nat.maxPrimeFac (n*(n+1)) ≤ max (Nat.maxPrimeFac d) (D / d)
    · simp [hdD, hu, not_lt.mpr hu]
    · simp [hdD, hu, lt_of_not_ge hu]
  · simp [hdD]

/-- The same identity with no exceptional inputs where the rough radical
is one. In that case both divisor expressions vanish exactly. -/
theorem roughLargeDivisorTail_moving_smooth_weight (B D n : ℕ) (hn : 0 < n)
    (hD : Nat.maxPrimeFac (n*(n+1)) ≤ D) :
    roughLargeDivisorTail B D n =
      -∑ d ∈ (roughRadical B (n*(n+1))).divisors,
        if d ≤ D then
          leastFactorTerm (fun p => if p ∣ n+1 then 1 else -1) d *
            (1 - commonSmoothWeight (max (Nat.maxPrimeFac d) (D / d)) n)
        else 0 := by
  by_cases hR : 1 < roughRadical B (n*(n+1))
  · exact roughLargeDivisorTail_moving_smooth_weight_of_nontrivial B D n hn hR hD
  · have he : roughRadical B (n*(n+1)) = 1 := by
      have := roughRadical_pos B (n*(n+1))
      omega
    have hm1 : 1 < n*(n+1) := by nlinarith
    have hD1 : 1 ≤ D :=
      (Nat.prime_maxPrimeFac_of_one_lt _ hm1).one_lt.le.trans hD
    rw [roughLargeDivisorTail_eq_subset_tail B D n hn hD1, he]
    simp [subsetMinTerm, leastFactorTerm]


#print axioms roughLargeDivisorTail_moving_smooth_weight

#print axioms squarefree_tail_moving_smooth_weight
end Erdos371
