import Submission.PrimeIntervalExplore
import Submission.ParabolaRepairExplore
import Submission.CyclicThickeningExplore

/-! Flat finite sets in prime-field planes and in cyclic groups. The prime may
be arbitrarily large. No compatibility across integer prefixes is asserted. -/
namespace Erdos66PrimeFlat
open Erdos66PrimeInterval Erdos66ParabolaRepair Erdos66OriginRepair
  Erdos66FiniteField Erdos66Coset Erdos66CyclicThickening

/-- Prime-field-plane sets with mean `(2k+1)^2` and relative error tending to zero
as `k` tends to infinity, uniformly in an arbitrarily large choice of prime. -/
theorem exists_flat_prime_plane (k N : ℕ) :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ p % 8 = 1 ∧ ∃ B : Finset (ZMod p × ZMod p), ∃ E : ℤ,
        0 ≤ E ∧ E ^ 2 ≤ 4 * ((2 * k + 1 : ℕ) : ℤ) ^ 3 ∧
        ∀ z, |(pairCount B B z : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ^ 2| ≤
          E + 10 * (2 * k + 1) + 8 := by
  let h := 2 * k + 1
  let m := 2 * k * (k + 1)
  obtain ⟨p, hp, hpN, hp8, U, hUcard, hU, hUU, E, hE0, hEsq, hEfiber⟩ :=
    exists_prime_parameters h (max N (max (2 * h + 1) m))
  letI : Fact p.Prime := ⟨hp⟩
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hne : U.Nonempty := Finset.card_pos.mp (by rw [hUcard]; dsimp [h]; omega)
  have hcard : 2 * U.card + 1 < Fintype.card (ZMod p) := by
    rw [hUcard, ZMod.card]
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hpN
  have hm : m < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hpN
  obtain ⟨B, hBzero, hBother⟩ := exists_parabola_origin_repair hF U hU hUU hne hcard m hm
  have hmean : 1 + 2 * m = h ^ 2 := by dsimp [m, h]; ring
  have hmain : ∀ z, |(pairCount B B z : ℤ) - (h : ℤ) ^ 2| ≤ E + 10 * h + 8 := by
    intro z
    by_cases hz : z = 0
    · subst z
      rw [hBzero, hmean, Nat.cast_pow, sub_self, abs_zero]
      positivity
    · obtain ⟨hlo, hhi⟩ := hBother z hz
      have hbase := graph_set_error_bound hF U hU hUU hne z.1 z.2
        (by simpa only [Prod.mk.eta] using hz)
      rw [← parabolaSet_pairCount_eq U z, hUcard] at hbase
      have hbase' : |(pairCount (parabolaSet U) (parabolaSet U) z : ℤ) - (h : ℤ) ^ 2| ≤
          E + 2 * h := by linarith
      have hlo' : (pairCount (parabolaSet U) (parabolaSet U) z : ℤ) ≤ pairCount B B z := by
        exact_mod_cast hlo
      have hhi' : (pairCount B B z : ℤ) ≤
          pairCount (parabolaSet U) (parabolaSet U) z + 8 * h + 8 := by
        rw [hUcard] at hhi
        exact_mod_cast hhi
      rw [abs_le] at hbase' ⊢
      constructor <;> omega
  exact ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hpN, hp8, B, E, hE0, hEsq, hmain⟩

/-- The prime-field examples transfer to actual cyclic sets after block
thickening; the error includes both the algebraic and carry contributions. -/
theorem exists_flat_cyclic (k K N : ℕ) [NeZero K] :
    ∃ p : ℕ, ∃ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      N < p ∧ ∃ C : Finset (ZMod ((p * K) ^ 2)), ∃ E : ℝ,
        0 ≤ E ∧ E ^ 2 ≤ 4 * ((2 * k + 1 : ℕ) : ℝ) ^ 3 ∧
        ∀ z : ZMod ((p * K) ^ 2), |((C.filter (fun a ↦ z - a ∈ C)).card : ℝ) -
            (K : ℝ) ^ 2 * ((2 * k + 1 : ℕ) : ℝ) ^ 2| ≤
          (K : ℝ) ^ 2 * (E + 10 * (2 * k + 1) + 8) +
            2 * K * (((2 * k + 1 : ℕ) : ℝ) ^ 2 + E + 10 * (2 * k + 1) + 8) := by
  obtain ⟨p, hp, hpN, hp8, B, E, hE0, hEsq, hB⟩ := exists_flat_prime_plane k N
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨p, hp, hpN, thickenedSet p K B, (E : ℝ), ?_, ?_, ?_⟩
  · exact_mod_cast hE0
  · exact_mod_cast hEsq
  · intro z
    have hf : ∀ t s : ZMod p,
        |((sumFiber p B t s).card : ℝ) - ((2 * k + 1 : ℕ) : ℝ) ^ 2| ≤
          (E : ℝ) + 10 * (2 * k + 1) + 8 := by
      intro t s
      have hh := hB (t, s)
      change |((sumFiber p B t s).card : ℤ) - ((2 * k + 1 : ℕ) : ℤ) ^ 2| ≤ _ at hh
      exact_mod_cast hh
    have hh := thickenedSet_error p K B (((2 * k + 1 : ℕ) : ℝ) ^ 2)
      ((E : ℝ) + 10 * (2 * k + 1) + 8) hf z
    convert hh using 1 <;> ring

end Erdos66PrimeFlat
