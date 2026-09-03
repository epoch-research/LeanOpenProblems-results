import FormalConjecturesUtil
import Submission.Progress

/-!
# Globally consecutive prime endpoints from two occupied bands

Independent structural reductions only. No statement from `Spec.lean` is used.
The simultaneous prime-occupancy hypothesis is not proved here.
-/

namespace PrimeEndpointBridge

/-- An empty open interval between two primes identifies the next *global* prime. -/
theorem consecutive_prime_count_index {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hempty : ∀ r : ℕ, p < r → r < q → ¬ r.Prime) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = q := by
  have hidx : Nat.count Nat.Prime p < Nat.count Nat.Prime q := by
    apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp
    simpa only [Nat.nth_count hp, Nat.nth_count hq] using hpq
  have hsucc : Nat.count Nat.Prime p + 1 = Nat.count Nat.Prime q := by
    by_contra hne
    have hlt : Nat.count Nat.Prime p + 1 < Nat.count Nat.Prime q := by omega
    have hlo : p < Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) := by
      conv_lhs => rw [← Nat.nth_count hp]
      exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
    have hhi : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) < q := by
      conv_rhs => rw [← Nat.nth_count hq]
      exact Nat.nth_strictMono Nat.infinite_setOf_prime hlt
    exact hempty _ hlo hhi
      (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _)
  rw [hsucc, Nat.nth_count hq]

/-- The corresponding gap is indexed by the count of primes strictly below `p`. -/
theorem primeGap_of_empty_interval {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hempty : ∀ r : ℕ, p < r → r < q → ¬ r.Prime) :
    primeGap (Nat.count Nat.Prime p) = q - p := by
  unfold primeGap
  rw [consecutive_prime_count_index hp hq hpq hempty, Nat.nth_count hp]

/-- The last prime of the first pool and first prime of the second pool are
consecutive globally, even when other pool points are prime. -/
theorem two_bands_give_prime_gap (A B : Finset ℕ)
    (hA : ∃ p ∈ A, p.Prime) (hB : ∃ q ∈ B, q.Prime)
    (hsep : ∀ p ∈ A, ∀ q ∈ B, p < q)
    (hcover : ∀ p ∈ A, ∀ q ∈ B, ∀ r : ℕ,
      p < r → r < q → r.Prime → r ∈ A ∨ r ∈ B) :
    ∃ p ∈ A, ∃ q ∈ B, p.Prime ∧ q.Prime ∧ p < q ∧
      Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = q ∧
      primeGap (Nat.count Nat.Prime p) = q - p := by
  classical
  let AP := A.filter Nat.Prime
  let BP := B.filter Nat.Prime
  have hAP : AP.Nonempty := by
    obtain ⟨p, hpA, hp⟩ := hA
    exact ⟨p, Finset.mem_filter.mpr ⟨hpA, hp⟩⟩
  have hBP : BP.Nonempty := by
    obtain ⟨q, hqB, hq⟩ := hB
    exact ⟨q, Finset.mem_filter.mpr ⟨hqB, hq⟩⟩
  let p := AP.max' hAP
  let q := BP.min' hBP
  have hpAP : p ∈ AP := Finset.max'_mem AP hAP
  have hqBP : q ∈ BP := Finset.min'_mem BP hBP
  obtain ⟨hpA, hp⟩ := Finset.mem_filter.mp hpAP
  obtain ⟨hqB, hq⟩ := Finset.mem_filter.mp hqBP
  have hpq := hsep p hpA q hqB
  have hempty : ∀ r : ℕ, p < r → r < q → ¬ r.Prime := by
    intro r hpr hrq hr
    rcases hcover p hpA q hqB r hpr hrq hr with hrA | hrB
    · have hrAP : r ∈ AP := Finset.mem_filter.mpr ⟨hrA, hr⟩
      exact (not_lt_of_ge (Finset.le_max' AP r hrAP)) hpr
    · have hrBP : r ∈ BP := Finset.mem_filter.mpr ⟨hrB, hr⟩
      exact (not_lt_of_ge (Finset.min'_le BP r hrBP)) hrq
  exact ⟨p, hpA, q, hqB, hp, hq, hpq,
    consecutive_prime_count_index hp hq hpq hempty,
    primeGap_of_empty_interval hp hq hpq hempty⟩

/-- A witness uses the actual number of primes strictly below its left endpoint,
not the position of that endpoint in a selected tuple. -/
def EndpointBand (N : ℕ) (a b : ℝ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧
    (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
    max N 2 ≤ Nat.count Nat.Prime p ∧
    a * Real.log (Nat.count Nat.Prime p) < (q - p : ℕ) ∧
    ((q - p : ℕ) : ℝ) < b * Real.log (Nat.count Nat.Prime p)

/-- This equivalence has no prime-pair or distribution assumption. -/
theorem endpoint_band_iff_gap_band (N : ℕ) (a b : ℝ) :
    EndpointBand N a b ↔
      ∃ n : ℕ, max N 2 ≤ n ∧
        a * Real.log n < (primeGap n : ℝ) ∧
        (primeGap n : ℝ) < b * Real.log n := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, hempty, hN, hlo, hhi⟩
    refine ⟨Nat.count Nat.Prime p, hN, ?_, ?_⟩
    · simpa only [primeGap_of_empty_interval hp hq hpq hempty] using hlo
    · simpa only [primeGap_of_empty_interval hp hq hpq hempty] using hhi
  · rintro ⟨n, hN, hlo, hhi⟩
    let p := Nat.nth Nat.Prime n
    let q := Nat.nth Nat.Prime (n + 1)
    have hp : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have hq : q.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
    have hpq : p < q := Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)
    have hempty : ∀ r : ℕ, p < r → r < q → ¬ r.Prime := by
      intro r hpr hrq hr
      have hloidx : n < Nat.count Nat.Prime r := by
        apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp
        simpa only [Nat.nth_count hr] using hpr
      have hhiidx : Nat.count Nat.Prime r < n + 1 := by
        apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp
        simpa only [Nat.nth_count hr] using hrq
      omega
    have hcount : Nat.count Nat.Prime p = n :=
      Nat.count_nth_of_infinite Nat.infinite_setOf_prime n
    refine ⟨p, q, hp, hq, hpq, hempty, ?_, ?_, ?_⟩
    · simpa only [hcount] using hN
    · simpa only [hcount] using hlo
    · simpa only [hcount] using hhi

/-- All geometric and occupancy assumptions are explicit. In particular `hA`
and `hB` are the simultaneous primality input, not a consequence of the cover. -/
theorem two_bands_suffice (N : ℕ) (a b : ℝ) (A B : Finset ℕ)
    (hA : ∃ p ∈ A, p.Prime) (hB : ∃ q ∈ B, q.Prime)
    (hsep : ∀ p ∈ A, ∀ q ∈ B, p < q)
    (hcover : ∀ p ∈ A, ∀ q ∈ B, ∀ r : ℕ,
      p < r → r < q → r.Prime → r ∈ A ∨ r ∈ B)
    (htail : ∀ p ∈ A, max N 2 ≤ Nat.count Nat.Prime p)
    (hwidth : ∀ p ∈ A, ∀ q ∈ B,
      a * Real.log (Nat.count Nat.Prime p) < (q - p : ℕ) ∧
      ((q - p : ℕ) : ℝ) < b * Real.log (Nat.count Nat.Prime p)) :
    EndpointBand N a b := by
  obtain ⟨p, hpA, q, hqB, _, _, _, _, hgap⟩ :=
    two_bands_give_prime_gap A B hA hB hsep hcover
  apply (endpoint_band_iff_gap_band N a b).mpr
  refine ⟨Nat.count Nat.Prime p, htail p hpA, ?_, ?_⟩
  · rw [hgap]
    exact (hwidth p hpA q hqB).1
  · rw [hgap]
    exact (hwidth p hpA q hqB).2


open Filter
open scoped Topology

/-- Exact reformulation of the target. The right-hand arithmetic assertion is
NOT proved here. In particular the normalization is `log (count Prime p)`. -/
theorem target_iff_prime_endpoint_bands :
    (∀ C : ℝ, 0 ≤ C →
      ∃ n : ℕ → ℕ, StrictMono n ∧
        Tendsto (fun i => (primeGap (n i) : ℝ) / Real.log (n i)) atTop (𝓝 C)) ↔
    (∀ a b : ℚ, 0 < a → a < b → ∀ N : ℕ,
      EndpointBand N (a : ℝ) (b : ℝ)) := by
  change PrimeGapProgress.FullNonnegativeCluster PrimeGapProgress.normalizedGap ↔ _
  rw [PrimeGapProgress.target_iff_rational_gap_intervals]
  constructor
  · intro h a b ha hab N
    exact (endpoint_band_iff_gap_band N a b).mpr (h a b ha hab N)
  · intro h a b ha hab N
    exact (endpoint_band_iff_gap_band N a b).mp (h a b ha hab N)

/-- A disproof would require an actual missing rational band, not a failure
of a particular construction or sieve estimate. No such band is supplied here. -/
theorem not_target_iff_forbidden_prime_endpoint_band :
    (¬ (∀ C : ℝ, 0 ≤ C →
      ∃ n : ℕ → ℕ, StrictMono n ∧
        Tendsto (fun i => (primeGap (n i) : ℝ) / Real.log (n i)) atTop (𝓝 C))) ↔
    ∃ a b : ℚ, 0 < a ∧ a < b ∧ ∃ N : ℕ,
      ¬ EndpointBand N (a : ℝ) (b : ℝ) := by
  rw [target_iff_prime_endpoint_bands]
  push_neg
  rfl

#print axioms not_target_iff_forbidden_prime_endpoint_band
#print axioms consecutive_prime_count_index
#print axioms primeGap_of_empty_interval
#print axioms two_bands_give_prime_gap
#print axioms endpoint_band_iff_gap_band
#print axioms two_bands_suffice
#print axioms target_iff_prime_endpoint_bands

end PrimeEndpointBridge
