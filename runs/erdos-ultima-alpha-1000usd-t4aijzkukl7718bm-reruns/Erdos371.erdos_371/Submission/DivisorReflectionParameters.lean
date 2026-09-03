import FormalConjecturesUtil
import Submission.DivisorPrimeReflection
import Submission.CompleteAdditiveComparison
import Submission.Explore

/-! Almost every integer supplies a parameter for the divisor-prime
reflection. This counts parameters, not distinct ascent/descent inputs,
and does not prove Erdős 371. -/

namespace Erdos371DivisorReflectionParameters

open Finset Filter Erdos371DivisorPrimeReflection
  Erdos371CompleteAdditiveComparison
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- The largest prime occurs at least twice. -/
def repeatedTop (n : ℕ) : Prop := (Nat.maxPrimeFac n)^2 ∣ n

lemma repeatedTop_density_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    {n | repeatedTop n}.partialDensity Set.univ N ≤
      {n | Nat.maxPrimeFac n ≤ K}.partialDensity Set.univ N + 1/N + 2/K := by
  have hsub : {n | repeatedTop n} ⊆
      {n | Nat.maxPrimeFac n ≤ K} ∪ {n | squareBad K n} := by
    intro n hn
    by_cases h : Nat.maxPrimeFac n ≤ K
    · exact Or.inl h
    · exact Or.inr ⟨Nat.maxPrimeFac n, by omega, hn⟩
  have h1 := partialDensity_mono hsub N
  have h2 := Erdos371ComparableRatio.partialDensity_union_le
    {n | Nat.maxPrimeFac n ≤ K} {n | squareBad K n} N
  linarith [squareBad_density_bound hK hN]

theorem repeatedTop_hasDensity_zero : {n | repeatedTop n}.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hKbig⟩ := exists_nat_gt (4/ε)
  have hK : 0 < K := Nat.cast_pos.mp
    ((by positivity : (0:ℝ) < 4/ε).trans hKbig)
  have hsmall : 2/(K:ℝ) < ε/2 := by
    have hk : (0:ℝ) < K := Nat.cast_pos.mpr hK
    have hh := (div_lt_iff₀ hε).mp hKbig
    apply (div_lt_iff₀ hk).mpr
    nlinarith
  have hu := (Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero K).add
    tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at hu
  filter_upwards [hu.eventually_lt_const (half_pos hε), eventually_gt_atTop 0]
    with N huN hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show
    0 ≤ {n | repeatedTop n}.partialDensity Set.univ N by
      unfold Set.partialDensity; positivity)]
  have hb := repeatedTop_density_bound hK hN
  change {n | Nat.maxPrimeFac n ≤ K}.partialDensity Set.univ N + 1/(N:ℝ) < ε/2 at huN
  linarith

/-- A nontrivial smooth cofactor of a prime; this is exactly the parameter
shape used by the verified reflection construction. -/
def admissible (n : ℕ) : Prop :=
  ∃ p b : ℕ, p.Prime ∧ 1 < b ∧ Nat.maxPrimeFac b < p ∧ n = p*b

lemma admissible_of_good {n : ℕ} (hb : 1 < n / Nat.maxPrimeFac n)
    (hs : ¬repeatedTop n) : admissible n := by
  let p := Nat.maxPrimeFac n
  let b := n/p
  have hn : 1 < n := by
    exact hb.trans_le (Nat.div_le_self n (Nat.maxPrimeFac n))
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hb1 : 1 < b := hb
  have he : p*b = n := Nat.mul_div_cancel' Nat.maxPrimeFac_dvd
  have hb0 : b ≠ 0 := by omega
  have hmax : max p (Nat.maxPrimeFac b) = p := by
    have hh := congrArg Nat.maxPrimeFac he
    simpa only [Nat.maxPrimeFac_mul hp.ne_zero hb0, hp.maxPrimeFac_eq_self] using hh
  have hle : Nat.maxPrimeFac b ≤ p := by
    have hh := le_max_right p (Nat.maxPrimeFac b)
    rwa [hmax] at hh
  have hlt : Nat.maxPrimeFac b < p := by
    by_contra h
    have hpb : Nat.maxPrimeFac b = p := by omega
    have hd : p ∣ b := hpb ▸ Nat.maxPrimeFac_dvd
    have hh : p*p ∣ p*b := Nat.mul_dvd_mul_left p hd
    have hsq : p^2 ∣ n := by simpa only [pow_two, he] using hh
    exact hs hsq
  exact ⟨p, b, hp, hb1, hlt, he.symm⟩

lemma inadmissible_hasDensity_zero : {n | ¬admissible n}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset
    (T := {n | n / Nat.maxPrimeFac n ≤ 1} ∪ {n | repeatedTop n})
  · intro n hn
    by_cases hb : n / Nat.maxPrimeFac n ≤ 1
    · exact Or.inl hb
    · exact Or.inr (by
        by_contra hs
        exact hn (admissible_of_good (by omega) hs))
  · exact Erdos371CofactorDensity.density_zero_union
      (Erdos371CofactorDensity.bounded_cofactor_hasDensity_zero 1)
      repeatedTop_hasDensity_zero

/-- Parameter availability has density one. This says nothing about the
multiplicities of the reflected inputs. -/
theorem admissible_hasDensity_one : {n | admissible n}.HasDensity 1 := by
  have h := hasDensity_compl inadmissible_hasDensity_zero
  simpa only [sub_zero, Set.compl_setOf, not_not] using h

lemma opposite_decomposition_of_admissible {n : ℕ} (hn : admissible n) :
    ∃ r t : ℕ, 0 < r ∧ 0 < t ∧ r+t+1 = n ∧
      Nat.maxPrimeFac r < Nat.maxPrimeFac (r+1) ∧
      Nat.maxPrimeFac (t+1) < Nat.maxPrimeFac t := by
  obtain ⟨p, b, hp, hb, hbp, rfl⟩ := hn
  obtain ⟨r, t, hr, ht, he, _, _, _, _, hsign⟩ := exists_opposite_pair hp hb hbp
  exact ⟨r, t, hr, ht, he, hsign⟩

def hasOppositeDecomposition (n : ℕ) : Prop :=
  ∃ r t : ℕ, 0 < r ∧ 0 < t ∧ r+t+1 = n ∧
    Nat.maxPrimeFac r < Nat.maxPrimeFac (r+1) ∧
    Nat.maxPrimeFac (t+1) < Nat.maxPrimeFac t

/-- Almost every parameter decomposes into one ascent input and one descent
input, plus one. This sumset statement does not assert equal densities. -/
theorem opposite_decomposition_hasDensity_one :
    {n | hasOppositeDecomposition n}.HasDensity 1 := by
  have hb : {n | ¬hasOppositeDecomposition n}.HasDensity 0 := by
    apply Erdos371Exploration.density_zero_of_subset
      (T := {n | ¬admissible n}) _ inadmissible_hasDensity_zero
    intro n hn ha
    exact hn (opposite_decomposition_of_admissible ha)
  have h := hasDensity_compl hb
  simpa only [sub_zero, Set.compl_setOf, not_not] using h

end Erdos371DivisorReflectionParameters

#print axioms Erdos371DivisorReflectionParameters.admissible_hasDensity_one
#print axioms Erdos371DivisorReflectionParameters.opposite_decomposition_of_admissible
#print axioms Erdos371DivisorReflectionParameters.opposite_decomposition_hasDensity_one
