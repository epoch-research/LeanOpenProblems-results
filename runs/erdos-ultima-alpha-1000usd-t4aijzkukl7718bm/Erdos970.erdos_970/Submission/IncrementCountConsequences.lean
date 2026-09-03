import Submission.LargePrimeCountReduction

/-! Higher-count consequences of the proposed largest-prime increment.
The increment remains an explicit hypothesis, never an axiom or a theorem
of this development. These consequences retain the old prime set and bound. -/
namespace Erdos970.IncrementReduction
open Finset OptimalCoverCore

lemma increment_length_step (k g t : ℕ) :
    (g + 2 * k * t + t * (t - 1)) + 2 * (k + t) =
      g + 2 * k * (t + 1) + (t + 1) * ((t + 1) - 1) := by
  cases t with
  | zero => simp
  | succ t => simp only [Nat.add_sub_cancel]; ring

/-- Iterating largest-prime insertion preserves the exact old bound g.
The new residues are unrestricted throughout. -/
theorem primeSetBound_union_of_increment (hstep : LargestPrimeIncrement)
    (P : Finset ℕ) (hne : P.Nonempty) (hP : ∀ q ∈ P, q.Prime)
    (g : ℕ) (hg : PrimeSetBound P g) (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime ∧ ∀ q ∈ P, q < p) :
    PrimeSetBound (P ∪ R) (g + 2 * P.card * R.card + R.card * (R.card - 1)) := by
  classical
  induction R using Finset.induction_on_max with
  | h0 => simpa using hg
  | @step p R hlt ih =>
    have hp := (hR p (mem_insert_self _ _)).1
    have hpP := (hR p (mem_insert_self _ _)).2
    have hR' : ∀ v ∈ R, v.Prime ∧ ∀ q ∈ P, q < v :=
      fun v hv => hR v (mem_insert_of_mem hv)
    have hdis : Disjoint P R := by
      apply disjoint_left.mpr
      intro q hq hqR
      exact ((hR' q hqR).2 q hq).false
    have hpR : p ∉ R := fun hh => (hlt p hh).false
    have hnew := hstep (P ∪ R) p (g + 2 * P.card * R.card + R.card * (R.card - 1))
      (hne.mono (subset_union_left)) hp
      (by
        intro q hq
        rcases mem_union.mp hq with hq | hq
        · exact ⟨hP q hq, hpP q hq⟩
        · exact ⟨(hR' q hq).1, hlt q hq⟩)
      (ih hR')
    rw [card_union_of_disjoint hdis, increment_length_step] at hnew
    simpa only [union_insert, card_insert_of_notMem hpR] using hnew

/-- Any prescribed cardinality of fresh primes can be placed beyond a
specified threshold and every old prime. -/
lemma exists_prime_set_above (P : Finset ℕ) (B t : ℕ) :
    ∃ R : Finset ℕ, R.card = t ∧ Disjoint P R ∧
      ∀ p ∈ R, p.Prime ∧ B ≤ p ∧ ∀ q ∈ P, q < p := by
  classical
  let F := range (B + P.sup id + 1)
  have hinf := Nat.infinite_setOf_prime.diff F.finite_toSet
  obtain ⟨R, hR, hcard⟩ := hinf.exists_subset_card_eq t
  have hlarge (p : ℕ) (hp : p ∈ R) : p.Prime ∧ B ≤ p ∧ ∀ q ∈ P, q < p := by
    have hh := hR hp
    have hpB : B + P.sup id + 1 ≤ p := by
      have : p ∉ F := hh.2
      simpa only [F, mem_range, not_lt] using this
    refine ⟨hh.1, by omega, fun q hq => ?_⟩
    have hqle : q ≤ P.sup id := le_sup (f := id) hq
    omega
  refine ⟨R, hcard, disjoint_left.mpr ?_, hlarge⟩
  intro q hq hqR
  exact ((hlarge q hqR).2.2 q hq).false

/-- The increment conjecture entails a full hierarchy of old-population
count bounds, not just the two-survivor consequence. -/
theorem count_bound_of_largestPrimeIncrement (hstep : LargestPrimeIncrement)
    (P : Finset ℕ) (hne : P.Nonempty) (hP : ∀ q ∈ P, q.Prime)
    (g : ℕ) (hg : PrimeSetBound P g) (t : ℕ) :
    PrimeSetCountBound P (g + 2 * P.card * t + t * (t - 1)) (t + 1) := by
  obtain ⟨R, hcard, hdis, hR⟩ := exists_prime_set_above P
    (g + 2 * P.card * t + t * (t - 1)) t
  have hb := primeSetBound_union_of_increment hstep P hne hP g hg R
    (fun p hp => ⟨(hR p hp).1, (hR p hp).2.2⟩)
  rw [hcard] at hb
  have hc := (primeSetBound_union_large_iff_count _ P R hdis
    (fun p hp => (hR p hp).2.1)).mp hb
  simpa only [hcard] using hc

/-- Pointwise consequence for an actual short interval with few survivors. -/
theorem length_lt_increment_envelope_of_few_survivors
    (hstep : LargestPrimeIncrement) (P : Finset ℕ)
    (hne : P.Nonempty) (hP : ∀ q ∈ P, q.Prime)
    (g : ℕ) (hg : PrimeSetBound P g) (m t : ℕ) (r : ℕ → ℕ)
    (hcount : (survivors m P r).card ≤ t) :
    m < g + 2 * P.card * t + t * (t - 1) := by
  by_contra hbad
  have hh := count_bound_of_largestPrimeIncrement hstep P hne hP g hg t r
  have hsub : survivors (g + 2 * P.card * t + t * (t - 1)) P r ⊆ survivors m P r := by
    intro i hi
    obtain ⟨him, hia⟩ := (mem_survivors _ _ _ _).mp hi
    exact (mem_survivors _ _ _ _).mpr ⟨by omega, hia⟩
  have hc := card_le_card hsub
  omega

#print axioms primeSetBound_union_of_increment
#print axioms count_bound_of_largestPrimeIncrement
#print axioms length_lt_increment_envelope_of_few_survivors
end Erdos970.IncrementReduction
