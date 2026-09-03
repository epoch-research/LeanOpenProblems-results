import Submission.ParitySquarePadding
import Submission.PrimeCountingDyadicDiscrepancy

/-! Padding and endpoint control for an arbitrary fixed positive multiple of a
square. Used only to test a parity-counting estimate, not a Jacobsthal bound. -/
namespace Erdos970.ParityDiscrepancy
open Finset Filter

def ScaledSquareParityBound (C A : ℕ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) →
    |alternatingCount P 1 (C * P.card ^ 2)| ≤ (A : ℚ) * P.card

lemma oddPrimes_card_le_primeCounting (y : ℕ) : (oddPrimes y).card ≤ y.primeCounting := by
  have hsub : oddPrimes y ⊆ (y + 1).primesBelow := by
    intro p hp
    obtain ⟨hpy, hpp, hpo⟩ := (mem_oddPrimes p y).mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
  have hc := card_le_card hsub
  simpa only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range] using hc

/-- The relevant odd-prime core occupies an arbitrarily small fraction of s. -/
lemma eventually_small_oddPrime_core (C : ℕ) (hC : 0 < C) :
    ∀ᶠ s : ℕ in atTop, C * (oddPrimes (2 * s)).card ≤ s := by
  have htwo : Tendsto (fun s : ℕ => 2 * s) atTop atTop :=
    tendsto_atTop_mono (fun s => by omega : ∀ s : ℕ, s ≤ 2 * s) tendsto_id
  have hlim := PrimeCountingDyadic.density_tendsto_zero.comp htwo
  have hCQ : (0 : ℝ) < C := by exact_mod_cast hC
  have heps : (0 : ℝ) < 1 / (2 * C) := by positivity
  have hev : ∀ᶠ s : ℕ in atTop,
      ((2 * s).primeCounting : ℝ) / (2 * s : ℕ) < 1 / (2 * C) :=
    hlim.eventually (gt_mem_nhds heps)
  filter_upwards [hev, eventually_ge_atTop 1] with s hs hs1
  have hs0 : (0 : ℝ) < (2 * s : ℕ) := by exact_mod_cast (show 0 < 2 * s by omega)
  have hh := (div_lt_div_iff₀ hs0 (by positivity : (0 : ℝ) < 2 * C)).mp hs
  have hcQ : ((oddPrimes (2 * s)).card : ℝ) ≤ (2 * s).primeCounting := by
    exact_mod_cast oddPrimes_card_le_primeCounting (2 * s)
  have hmul := mul_le_mul_of_nonneg_left hcQ hCQ.le
  have hgoal : (C : ℝ) * (oddPrimes (2 * s)).card ≤ s := by push_cast at hh; nlinarith
  exact_mod_cast hgoal

lemma scaled_square_bound_to_short (C A : ℕ) (hC : 0 < C) (hA : ScaledSquareParityBound C A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (m : ℕ)
    (hcard : C * P.card ^ 2 ≤ m) :
    |alternatingCount P 1 m| ≤ ((A : ℚ) + 2 * C) * ((m / C).sqrt + 1 : ℕ) := by
  let k := (m / C).sqrt + 1
  have hmk : m ≤ C * k ^ 2 := by
    have hl := Nat.lt_mul_div_succ m hC
    have hs := Nat.lt_succ_sqrt' (m / C)
    change m / C < k ^ 2 at hs
    have hm := Nat.mul_le_mul_left C (show m / C + 1 ≤ k ^ 2 by omega)
    omega
  have hcardk : P.card ≤ k := by
    have hh : P.card ^ 2 ≤ m / C := (Nat.le_div_iff_mul_le hC).mpr (by nlinarith)
    have hr : P.card ≤ (m / C).sqrt := Nat.le_sqrt.mpr (by simpa only [pow_two] using hh)
    dsimp [k]
    omega
  have hgap : C * k ^ 2 - m ≤ 2 * C * k := by
    have hs := Nat.sqrt_le (m / C)
    have hmul := Nat.mul_le_mul_left C hs
    have hdiv := Nat.mul_div_le m C
    have hh : C * k ^ 2 ≤ m + 2 * C * k := by dsimp [k]; nlinarith
    omega
  obtain ⟨Q, hPQ, hQcard, hQ, hnew⟩ := exists_padding P hP k (C * k ^ 2) hcardk
  have hbound := hA Q hQ
  rw [hQcard, alternatingCount_eq_of_padding P Q hPQ (C * k ^ 2) (C * k ^ 2) le_rfl hnew] at hbound
  have hprefix := abs_alternatingCount_prefix P 1 m (C * k ^ 2) hmk
  have hgapQ : ((C * k ^ 2 - m : ℕ) : ℚ) ≤ 2 * C * k := by exact_mod_cast hgap
  change |alternatingCount P 1 m| ≤ ((A : ℚ) + 2 * C) * k
  nlinarith

lemma scaled_square_bound_in_window (C A : ℕ) (hC : 0 < C) (hA : ScaledSquareParityBound C A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ Odd p) (s m : ℕ) (hs : 0 < s)
    (hcard : C * P.card ≤ s) (hlo : s ^ 2 ≤ m) (hhi : m ≤ 4 * s ^ 2) :
    |alternatingCount P 1 m| ≤ 3 * ((A : ℚ) + 2 * C) * s := by
  have hc : P.card ≤ s := (Nat.le_mul_of_pos_left P.card hC).trans hcard
  have hcm : C * P.card ^ 2 ≤ m := by
    have hm := Nat.mul_le_mul hcard hc
    nlinarith
  have hroothi : (m / C).sqrt ≤ 2 * s := by
    have h := Nat.sqrt_le_sqrt ((Nat.div_le_self m C).trans
      (show m ≤ (2 * s) ^ 2 by nlinarith))
    simpa only [Nat.sqrt_eq'] using h
  have hh := scaled_square_bound_to_short C A hC hA P hP m hcm
  have hbound : ((m / C).sqrt + 1 : ℕ) ≤ 3 * s := by omega
  have hboundQ : (((m / C).sqrt + 1 : ℕ) : ℚ) ≤ 3 * s := by exact_mod_cast hbound
  have hmul := mul_le_mul_of_nonneg_left hboundQ (by positivity : (0 : ℚ) ≤ A + 2 * C)
  nlinarith

#print axioms eventually_small_oddPrime_core
#print axioms scaled_square_bound_to_short
end Erdos970.ParityDiscrepancy
