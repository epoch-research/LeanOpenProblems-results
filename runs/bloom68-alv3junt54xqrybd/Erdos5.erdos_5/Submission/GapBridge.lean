import FormalConjecturesUtil
import Submission.PrimeNormalization

/-! Arithmetic and normalization bridges only; no import of Submission.Spec. -/

open Filter Set
open scoped Topology

namespace Erdos5CoveredGapBridge

def ConsecutivePrimePair (q r : ℕ) : Prop :=
  Nat.Prime q ∧ Nat.Prime r ∧ q < r ∧
    ∀ m : ℕ, q < m → m < r → ¬ Nat.Prime m

/-- Prime endpoints with a prime-free interior are successive indexed primes. -/
theorem indexed_of_consecutive {q r : ℕ} (h : ConsecutivePrimePair q r) :
    ∃ n : ℕ, Nat.nth Nat.Prime n = q ∧ Nat.nth Nat.Prime (n + 1) = r := by
  rcases h with ⟨hq, hr, hqr, hbetween⟩
  have hqn : Nat.nth Nat.Prime (Nat.primeCounting' q) = q := Nat.nth_count hq
  have hrn : Nat.nth Nat.Prime (Nat.primeCounting' r) = r := Nat.nth_count hr
  have hindex : Nat.primeCounting' q < Nat.primeCounting' r := by
    apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp
    simpa only [hqn, hrn] using hqr
  have hsucc : Nat.nth Nat.Prime (Nat.primeCounting' q + 1) ≤ r := by
    rw [← hrn]
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega)
  have hleft : q < Nat.nth Nat.Prime (Nat.primeCounting' q + 1) := by
    simpa only [hqn] using
      (Nat.nth_strictMono Nat.infinite_setOf_prime) (Nat.lt_succ_self (Nat.primeCounting' q))
  have heq : Nat.nth Nat.Prime (Nat.primeCounting' q + 1) = r := by
    by_contra hne
    exact hbetween _ hleft (lt_of_le_of_ne hsucc hne) (Nat.prime_nth_prime _)
  exact ⟨Nat.primeCounting' q, hqn, heq⟩

/-- Conversely, the enumeration omits no prime between two successive values. -/
theorem consecutive_of_indexed (n : ℕ) :
    ConsecutivePrimePair (Nat.nth Nat.Prime n) (Nat.nth Nat.Prime (n + 1)) := by
  refine ⟨Nat.prime_nth_prime _, Nat.prime_nth_prime _,
    (Nat.nth_strictMono Nat.infinite_setOf_prime) (by omega), ?_⟩
  intro m hlo hhi hm
  have hmem : m ∈ Set.range (Nat.nth Nat.Prime) := by
    rw [Nat.range_nth_of_infinite Nat.infinite_setOf_prime]
    exact hm
  obtain ⟨j, hj⟩ := hmem
  rw [← hj] at hlo hhi
  have hnj : n < j := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hlo
  have hjn : j < n + 1 := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mp hhi
  omega

theorem consecutive_iff_indexed (q r : ℕ) :
    ConsecutivePrimePair q r ↔
      ∃ n : ℕ, Nat.nth Nat.Prime n = q ∧ Nat.nth Nat.Prime (n + 1) = r := by
  constructor
  · exact indexed_of_consecutive
  · rintro ⟨n, rfl, rfl⟩
    exact consecutive_of_indexed n

/-- The gap produced by a covered pair is precisely the intended `primeGap`. -/
theorem gap_of_consecutive {q r : ℕ} (h : ConsecutivePrimePair q r) :
    primeGap (Nat.primeCounting' q) = r - q := by
  obtain ⟨n, hq, hr⟩ := indexed_of_consecutive h
  have hi : Nat.primeCounting' q = n := by
    rw [← hq]
    exact Nat.primeCounting'_nth_eq n
  rw [hi, primeGap, hq, hr]

/-- Select the last left-block prime and the first right-block prime. -/
theorem consecutive_from_two_blocks (L R : Finset ℕ)
    (hsep : ∀ q ∈ L, ∀ r ∈ R, q < r)
    (hcover : ∀ q ∈ L, ∀ r ∈ R, ∀ m : ℕ,
      q < m → m < r → Nat.Prime m → m ∈ L ∨ m ∈ R)
    (hL : ∃ q ∈ L, Nat.Prime q) (hR : ∃ r ∈ R, Nat.Prime r) :
    ∃ q ∈ L, ∃ r ∈ R, ConsecutivePrimePair q r := by
  classical
  let LP := L.filter Nat.Prime
  let RP := R.filter Nat.Prime
  have hLP : LP.Nonempty := by
    obtain ⟨q, hq, hprime⟩ := hL
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hprime⟩⟩
  have hRP : RP.Nonempty := by
    obtain ⟨r, hr, hprime⟩ := hR
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, hprime⟩⟩
  let q := LP.max' hLP
  let r := RP.min' hRP
  have hq : q ∈ L ∧ Nat.Prime q := Finset.mem_filter.mp (LP.max'_mem hLP)
  have hr : r ∈ R ∧ Nat.Prime r := Finset.mem_filter.mp (RP.min'_mem hRP)
  refine ⟨q, hq.1, r, hr.1, hq.2, hr.2, hsep q hq.1 r hr.1, ?_⟩
  intro m hqm hmr hm
  rcases hcover q hq.1 r hr.1 m hqm hmr hm with hmL | hmR
  · have hp : m ∈ LP := Finset.mem_filter.mpr ⟨hmL, hm⟩
    exact not_lt_of_ge (LP.le_max' m hp) hqm
  · have hp : m ∈ RP := Finset.mem_filter.mpr ⟨hmR, hm⟩
    exact not_lt_of_ge (RP.min'_le m hp) hmr

/-- An interior cover and two occupied blocks give an indexed gap with the desired bounds. -/
theorem primeGap_from_two_block_cover (L R : Finset ℕ) (a b c d : ℕ)
    (hLb : ∀ q ∈ L, a ≤ q ∧ q ≤ b)
    (hRb : ∀ r ∈ R, c ≤ r ∧ r ≤ d) (hbc : b < c)
    (hcover : ∀ m : ℕ, a ≤ m → m ≤ d → Nat.Prime m → m ∈ L ∨ m ∈ R)
    (hL : ∃ q ∈ L, Nat.Prime q) (hR : ∃ r ∈ R, Nat.Prime r) :
    ∃ n : ℕ, Nat.nth Nat.Prime n ∈ L ∧ Nat.nth Nat.Prime (n + 1) ∈ R ∧
      c - b ≤ primeGap n ∧ primeGap n ≤ d - a := by
  have hsep : ∀ q ∈ L, ∀ r ∈ R, q < r := by
    intro q hq r hr
    exact (hLb q hq).2.trans_lt (hbc.trans_le (hRb r hr).1)
  have hcv : ∀ q ∈ L, ∀ r ∈ R, ∀ m : ℕ,
      q < m → m < r → Nat.Prime m → m ∈ L ∨ m ∈ R := by
    intro q hq r hr m hqm hmr hm
    exact hcover m ((hLb q hq).1.trans hqm.le) (hmr.le.trans (hRb r hr).2) hm
  obtain ⟨q, hq, r, hr, hpair⟩ := consecutive_from_two_blocks L R hsep hcv hL hR
  obtain ⟨n, hnq, hnr⟩ := indexed_of_consecutive hpair
  have hg : primeGap n = r - q := by rw [primeGap, hnq, hnr]
  have hqb := hLb q hq
  have hrb := hRb r hr
  refine ⟨n, by simpa only [hnq] using hq, by simpa only [hnr] using hr, ?_, ?_⟩
  · rw [hg]
    omega
  · rw [hg]
    omega

noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / Real.log n
noncomputable def primeNormalizedGap (n : ℕ) : ℝ :=
  primeGap n / Real.log (Nat.nth Nat.Prime n)

lemma log_prime_ne_zero (n : ℕ) : Real.log (Nat.nth Nat.Prime n : ℝ) ≠ 0 := by
  apply ne_of_gt
  exact Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime n).one_lt)

lemma gap_normalization_identity (n : ℕ) :
    normalizedGap n = primeNormalizedGap n *
      (Real.log (Nat.nth Nat.Prime n : ℝ) / Real.log (n : ℝ)) := by
  unfold normalizedGap primeNormalizedGap
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc
    (primeGap n : ℝ) * (Real.log (n : ℝ))⁻¹ =
        (primeGap n : ℝ) *
          ((Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹ *
            Real.log (Nat.nth Nat.Prime n : ℝ)) * (Real.log (n : ℝ))⁻¹ := by
      rw [inv_mul_cancel₀ (log_prime_ne_zero n), mul_one]
    _ = _ := by ring

lemma prime_gap_normalization_identity (n : ℕ) (hn : 2 ≤ n) :
    primeNormalizedGap n = normalizedGap n *
      (Real.log (n : ℝ) / Real.log (Nat.nth Nat.Prime n : ℝ)) := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  unfold normalizedGap primeNormalizedGap
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc
    (primeGap n : ℝ) * (Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹ =
        (primeGap n : ℝ) *
          ((Real.log (n : ℝ))⁻¹ * Real.log (n : ℝ)) *
            (Real.log (Nat.nth Nat.Prime n : ℝ))⁻¹ := by
      rw [inv_mul_cancel₀ hlog, mul_one]
    _ = _ := by ring

/-- Both conventional logarithmic normalizations have exactly the same subsequential limits. -/
theorem subsequence_normalizations_iff (n : ℕ → ℕ) (hn : StrictMono n) (C : ℝ) :
    Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C) ↔
      Tendsto (fun i => primeNormalizedGap (n i)) atTop (𝓝 C) := by
  constructor
  · intro hlim
    have hratio := Erdos5PrimeNormalization.tendsto_log_index_div_log_nth_prime.comp
      hn.tendsto_atTop
    have hprod := hlim.mul hratio
    have hev : (fun i => primeNormalizedGap (n i)) =ᶠ[atTop]
        (fun i => normalizedGap (n i) *
          (Real.log (n i : ℝ) / Real.log (Nat.nth Nat.Prime (n i) : ℝ))) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with i hi
      exact prime_gap_normalization_identity (n i) (hi.trans (hn.id_le i))
    exact (tendsto_congr' hev).mpr
      (by simpa only [Function.comp_def, mul_one] using hprod)
  · intro hlim
    have hratio := Erdos5PrimeNormalization.tendsto_log_nth_prime_div_log_index.comp
      hn.tendsto_atTop
    have hprod := hlim.mul hratio
    simpa only [Function.comp_def, ← gap_normalization_identity, mul_one] using hprod

theorem subsequential_limits_iff (C : ℝ) :
    (∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C)) ↔
    (∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun i => primeNormalizedGap (n i)) atTop (𝓝 C)) := by
  constructor
  · rintro ⟨n, hn, hlim⟩
    exact ⟨n, hn, (subsequence_normalizations_iff n hn C).mp hlim⟩
  · rintro ⟨n, hn, hlim⟩
    exact ⟨n, hn, (subsequence_normalizations_iff n hn C).mpr hlim⟩

end Erdos5CoveredGapBridge

#print axioms Erdos5CoveredGapBridge.indexed_of_consecutive
#print axioms Erdos5CoveredGapBridge.consecutive_iff_indexed
#print axioms Erdos5CoveredGapBridge.gap_of_consecutive
#print axioms Erdos5CoveredGapBridge.consecutive_from_two_blocks
#print axioms Erdos5CoveredGapBridge.primeGap_from_two_block_cover
#print axioms Erdos5CoveredGapBridge.subsequence_normalizations_iff
#print axioms Erdos5CoveredGapBridge.subsequential_limits_iff
