import Submission.RoughRadicalComplement

/-! Exact cancellation by toggling the largest prime. The surviving boundary
condition depends on the input's largest rough prime; no mean estimate for
that boundary is asserted here. -/
namespace Erdos371
open Finset

/-- Truncating the finite Alladi identity leaves precisely the subsets
whose product crosses the cutoff on insertion of the largest element. -/
theorem subset_tail_toggle_largest (s : Finset ℕ) (p D : ℕ) (f : ℕ → ℝ)
    (hp : p∈s) (hmax : ∀ q∈s, q≤p) (hp1 : 1≤p) (hD : p≤D) :
    (∑ t ∈ s.powerset, if D<(∏ q ∈ t, q) then subsetMinTerm f t else 0) =
      -∑ t ∈ (s.erase p).powerset,
        if (∏ q ∈ t, q)≤D ∧ D<p*(∏ q ∈ t, q) then subsetMinTerm f t else 0 := by
  have hpnot : p∉s.erase p := notMem_erase p s
  conv_lhs => rw [← insert_erase hp,sum_powerset_insert hpnot,← sum_add_distrib]
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  have hts := mem_powerset.mp ht
  have hpt : p∉t := fun h => hpnot (hts h)
  rw [prod_insert hpt]
  by_cases hte : t.Nonempty
  · have hm : t.min' hte≤p := hmax _ (mem_of_mem_erase (hts (t.min'_mem hte)))
    have hc : subsetMinTerm f (insert p t) = -subsetMinTerm f t := by
      simp only [subsetMinTerm,dif_pos hte,dif_pos (insert_nonempty p t),
        card_insert_of_notMem hpt,min'_insert p t hte,min_eq_right hm,pow_succ]
      ring
    rw [hc]
    have hprod : (∏ q ∈ t, q)≤p*(∏ q ∈ t, q) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (∏ q ∈ t, q) hp1
    by_cases hsmall : (∏ q ∈ t, q)≤D
    · by_cases hlarge : D<p*(∏ q ∈ t, q)
      · simp [hsmall,hlarge,not_lt.mpr hsmall]
      · simp [hsmall,hlarge,not_lt.mpr hsmall]
    · have hlarge : D<p*(∏ q ∈ t, q) := (lt_of_not_ge hsmall).trans_le hprod
      simp [hsmall,hlarge,lt_of_not_ge hsmall]
  · have he : t=∅ := not_nonempty_iff_eq_empty.mp hte
    subst t
    simp [not_lt.mpr hD,not_lt.mpr (hp1.trans hD)]

lemma squarefree_tail_eq_subset_tail (R D : ℕ) (hR : Squarefree R) (hR0 : R≠0)
    (f : ℕ → ℝ) :
    (∑ d ∈ R.divisors, if D<d then leastFactorTerm f d else 0) =
      ∑ t ∈ R.primeFactors.powerset,
        if D<(∏ q ∈ t, q) then subsetMinTerm f t else 0 := by
  rw [← sum_squarefree_divisors_eq_powerset R hR0
    (fun t => if D<(∏ q ∈ t, q) then subsetMinTerm f t else 0)]
  apply sum_congr rfl
  intro d hd
  have hs := hR.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
  rw [if_pos hs,Nat.prod_primeFactors_of_squarefree hs,leastFactorTerm_eq,if_pos hs]

theorem roughLargeDivisorTail_eq_subset_tail (B D n : ℕ) (hn : 0<n) (hD : 1≤D) :
    roughLargeDivisorTail B D n =
      ∑ t ∈ (roughRadical B (n*(n+1))).primeFactors.powerset,
        if D<(∏ q ∈ t, q) then subsetMinTerm (fun p => if p∣n+1 then 1 else -1) t else 0 := by
  have hm : n*(n+1)≠0 := by positivity
  have he : roughLargeDivisorTail B D n =
      ∑ d ∈ (n*(n+1)).divisors.filter (fun d => D<d ∧ B<d.minFac),
        (ArithmeticFunction.moebius d : ℝ)*divisorSideColour n d := by
    unfold roughLargeDivisorTail
    apply sum_congr rfl
    intro d hd
    obtain ⟨hd,hdD,_⟩ := mem_filter.mp hd
    have hd1 : 1<d := lt_of_le_of_lt hD hdD
    simp only [orientedDivisorTerm,if_pos (Nat.mem_divisors.mp hd).1,
      leastFactorTerm_eq_moebius,if_pos hd1,divisorSideColour]
  rw [he,rough_moebius_tail_radical B D _ hm hD,sum_filter]
  rw [← squarefree_tail_eq_subset_tail _ D (roughRadical_squarefree B _) (roughRadical_pos B _).ne']
  apply sum_congr rfl
  intro d hd
  by_cases h : D<d
  · have hd1 : 1<d := lt_of_le_of_lt hD h
    simp [h,leastFactorTerm_eq_moebius,hd1,divisorSideColour]
  · simp [h]

/-- The true arithmetic tail becomes a boundary sum after pairing by the
largest rough prime. The varying largest-prime restriction is retained. -/
theorem roughLargeDivisorTail_max_toggle (B D n : ℕ) (hn : 0<n)
    (hR : 1<roughRadical B (n*(n+1)))
    (hD : Nat.maxPrimeFac (n*(n+1))≤D) :
    roughLargeDivisorTail B D n =
      -∑ t ∈ ((roughRadical B (n*(n+1))).primeFactors.erase
        (Nat.maxPrimeFac (roughRadical B (n*(n+1))))).powerset,
        if (∏ q ∈ t, q)≤D ∧
            D<Nat.maxPrimeFac (roughRadical B (n*(n+1)))*(∏ q ∈ t, q) then
          subsetMinTerm (fun p => if p∣n+1 then 1 else -1) t
        else 0 := by
  let R := roughRadical B (n*(n+1))
  have hp := Nat.prime_maxPrimeFac_of_one_lt R hR
  have hR0 : R≠0 := (roughRadical_pos B _).ne'
  have hpm : Nat.maxPrimeFac R≤Nat.maxPrimeFac (n*(n+1)) :=
    Nat.le_maxPrimeFac (by positivity) hp (Nat.maxPrimeFac_dvd.trans (roughRadical_dvd B _))
  have hpD := hpm.trans hD
  have hD1 : 1≤D := hp.one_lt.le.trans hpD
  rw [roughLargeDivisorTail_eq_subset_tail B D n hn hD1]
  apply subset_tail_toggle_largest
  · exact Nat.mem_primeFactors.mpr ⟨hp,Nat.maxPrimeFac_dvd,hR0⟩
  · intro q hq
    exact Nat.le_maxPrimeFac hR0 (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
  · exact hp.one_lt.le
  · exact hpD

#print axioms subset_tail_toggle_largest
#print axioms roughLargeDivisorTail_max_toggle
end Erdos371
