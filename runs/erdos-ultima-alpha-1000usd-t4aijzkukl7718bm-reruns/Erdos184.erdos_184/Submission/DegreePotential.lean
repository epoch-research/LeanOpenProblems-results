import FormalConjecturesUtil

/-! Analytic restrictions on bounded monotone degree potentials.
These lemmas do not prove or disprove the cycle decomposition conjecture. -/
open Filter
namespace Erdos184.DegreePotential

/-- A nonnegative summable sequence cannot eventually dominate a positive
multiple of the harmonic sequence. -/
lemma exists_small_weighted_term {a : ℕ → ℝ} (_ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n ≥ N, ((n : ℝ) + 1) * a n < ε := by
  by_contra! hn
  have htail : Summable (fun n : ℕ => ε⁻¹ * a (n + N)) :=
    ((summable_nat_add_iff N).mpr hs).mul_left _
  have hbound (n : ℕ) :
      1 / ((n + N : ℕ) + 1 : ℝ) ≤ ε⁻¹ * a (n + N) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hε, div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : 0 < ((n + N : ℕ) : ℝ) + 1)).mpr
    have hh := hn (n + N) (by omega)
    nlinarith
  have hsum : Summable (fun n : ℕ => 1 / ((n + N : ℕ) + 1 : ℝ)) :=
    htail.of_nonneg_of_le (fun n => by positivity) hbound
  have hsum' : Summable (fun n : ℕ => ((n + (N + 1) : ℕ) : ℝ)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div, add_assoc] using hsum
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff (N + 1)).mp hsum')

/-- Bounded monotone sequences have summable forward increments. -/
lemma summable_increments {φ : ℕ → ℝ} (hm : Monotone φ)
    (hb : BddAbove (Set.range φ)) :
    Summable (fun n => φ (n + 1) - φ n) := by
  obtain ⟨M, hM⟩ := hb
  apply summable_of_sum_range_le (fun n => sub_nonneg.mpr (hm (by omega)))
    (c := M - φ 0)
  intro n
  rw [Finset.sum_range_sub]
  exact sub_le_sub_right (hM (Set.mem_range_self n)) _

/-- Along arbitrarily large even degrees, both the remaining potential tail
and the degree-weighted two-step increment are small. -/
lemma exists_even_small_tail_and_increment {φ : ℕ → ℝ} (hm : Monotone φ)
    (hb : BddAbove (Set.range φ)) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ d ≥ N, Even d ∧ 2 ≤ d ∧
      (⨆ i, φ i) - φ (d - 2) + (d : ℝ) * (φ d - φ (d - 2)) < ε := by
  let ψ : ℕ → ℝ := fun n => φ (2 * n)
  have hmψ : Monotone ψ := fun a b h => hm (Nat.mul_le_mul_left 2 h)
  have hbψ : BddAbove (Set.range ψ) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun _ ⟨n, hn⟩ => hn ▸ hM (Set.mem_range_self _)⟩
  have hs := summable_increments hmψ hbψ
  have ht : Tendsto (fun n => φ (2 * n)) atTop (nhds (⨆ i, φ i)) :=
    (tendsto_atTop_ciSup hm hb).comp
      (tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n, n ≤ 2 * n) tendsto_id)
  obtain ⟨K, hK⟩ := (ht.eventually_const_lt (by linarith :
    (⨆ i, φ i) - ε / 2 < (⨆ i, φ i))).exists_forall_of_atTop
  obtain ⟨n, hn, hsmall⟩ := exists_small_weighted_term
    (fun n => sub_nonneg.mpr (hmψ (by omega))) hs
    (by positivity : 0 < ε / 4) (max N K)
  refine ⟨2 * (n + 1), by omega, ⟨n + 1, by omega⟩, by omega, ?_⟩
  have hsub : 2 * (n + 1) - 2 = 2 * n := by omega
  rw [hsub]
  have htail := hK n (by omega)
  dsimp [ψ] at hsmall
  push_cast
  nlinarith

end Erdos184.DegreePotential
