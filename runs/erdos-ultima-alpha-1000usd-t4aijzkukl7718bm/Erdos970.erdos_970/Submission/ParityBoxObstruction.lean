import FormalConjecturesUtil

/-! A finite separation between full synthetic moment populations and a more
restrictive nonnegative parity-box construction. It is not an actual residue
cover, and does not disprove a Jacobsthal bound. -/
namespace Erdos970.ParityBoxObstruction

abbrev Pattern := Finset (Fin 4)

def smallPatterns : Finset Pattern :=
  {{0}, {1}, {0, 1}, {2}, {0, 2}, {3}, {0, 3}}

lemma pattern_cover (T : Pattern) :
    T = ∅ ∨ T ∈ smallPatterns ∨ ({1, 2} : Pattern) ⊆ T ∨
      ({1, 3} : Pattern) ⊆ T ∨ ({2, 3} : Pattern) ⊆ T := by
  have h : ∀ T : Pattern,
      T = ∅ ∨ T ∈ smallPatterns ∨ ({1, 2} : Pattern) ⊆ T ∨
        ({1, 3} : Pattern) ⊆ T ∨ ({2, 3} : Pattern) ⊆ T := by decide +kernel
  exact h T

noncomputable def upperMass (c : Pattern → ℝ) (B : Pattern) : ℝ :=
  ∑ T : Pattern, if B ⊆ T then c T else 0

/-- Every nonempty pattern is either one of seven small patterns or contains a
pair of the last three coordinates. This uses only positivity and pair caps. -/
theorem total_mass_le (c : Pattern → ℝ) (hc : ∀ T, 0 ≤ c T) (hc0 : c ∅ = 0)
    (ε : ℝ) (hcap : ∀ T, c T ≤ ε) :
    (∑ T : Pattern, c T) ≤ 7 * ε + upperMass c {1, 2} +
      upperMass c {1, 3} + upperMass c {2, 3} := by
  classical
  have hpoint (T : Pattern) : c T ≤
      (if T ∈ smallPatterns then c T else 0) +
      (if ({1, 2} : Pattern) ⊆ T then c T else 0) +
      (if ({1, 3} : Pattern) ⊆ T then c T else 0) +
      (if ({2, 3} : Pattern) ⊆ T then c T else 0) := by
    rcases pattern_cover T with h | h | h | h | h
    · subst T
      simp [hc0]
    all_goals split_ifs <;> linarith [hc T]
  have hs := Finset.sum_le_sum (fun T (_ : T ∈ (Finset.univ : Finset Pattern)) => hpoint T)
  simp only [Finset.sum_add_distrib] at hs
  have hsmall : (∑ T : Pattern, if T ∈ smallPatterns then c T else 0) ≤ 7 * ε := by
    calc
      _ = ∑ T ∈ smallPatterns, c T := by simp
      _ ≤ ∑ _T ∈ smallPatterns, ε := Finset.sum_le_sum (fun T _ => hcap T)
      _ = 7 * ε := by
        have hh : smallPatterns.card = 7 := by decide +kernel
        simp [hh]
  dsimp only [upperMass]
  linarith

/-- For the Bernoulli marginals 1/2,1/3,1/5,1/7, the empty probability is8/35.
Nonnegative parity-box corrections with each moment error <=1/42 cannot remove
that atom. Even the three displayed pair capacities already rule this out. -/
theorem no_positive_boxes_at_forty_two :
    ¬∃ c : Pattern → ℝ,
      (∀ T, 0 ≤ c T) ∧ c ∅ = 0 ∧
      (∑ T : Pattern, c T) = 8 / 35 ∧
      (∀ T, c T ≤ 1 / 42) ∧
      upperMass c {1, 2} ≤ 1 / 35 ∧
      upperMass c {1, 3} ≤ 2 / 105 ∧
      upperMass c {2, 3} ≤ 1 / 105 := by
  rintro ⟨c, hc, hc0, hsum, hcap, h12, h13, h23⟩
  have hh := total_mass_le c hc hc0 (1 / 42) hcap
  rw [hsum] at hh
  linarith

/-- Encode the four hit coordinates by a bit mask, only for finite evaluation. -/
def code (T : Pattern) : ℕ := ∑ i ∈ T, 2 ^ i.val

def probabilityMass (T : Pattern) : ℚ :=
  match code T with
  | 1 => 79 / 245
  | 2 => 313 / 1470
  | 3 => 17 / 210
  | 4 => 43 / 294
  | 5 => 1 / 30
  | 7 => 4 / 105
  | 8 => 173 / 1470
  | 9 => 1 / 42
  | 11 => 2 / 105
  | 15 => 4 / 735
  | _ => 0

def marginal : Fin 4 → ℚ := ![1 / 2, 1 / 3, 1 / 5, 1 / 7]

def moment (T : Pattern) : ℚ :=
  ∑ B : Pattern, if T ⊆ B then probabilityMass B else 0

/-- Nevertheless, the unrestricted synthetic-population problem IS feasible,
with the sharper uniform moment error17/735. The empty hit pattern has zero mass.
This finite calculation is kernel checked, not a floating-point LP assertion. -/
theorem synthetic_population :
    (∀ T : Pattern, 0 ≤ probabilityMass T) ∧ probabilityMass ∅ = 0 ∧
    (∑ T : Pattern, probabilityMass T) = 1 ∧
    (∀ T : Pattern, |moment T - ∏ i ∈ T, marginal i| ≤ (17 / 735 : ℚ)) := by
  decide +kernel

/-- Scaling the probability population to total mass42 gives unit-error
intersection counts, still with no survivor atom. -/
theorem scaled_unit_error :
    (∑ T : Pattern, 42 * probabilityMass T) = 42 ∧
    (∀ T : Pattern,
      |(∑ B : Pattern, if T ⊆ B then 42 * probabilityMass B else 0) -
        42 * ∏ i ∈ T, marginal i| ≤ 1) := by
  decide +kernel

#print axioms no_positive_boxes_at_forty_two
#print axioms synthetic_population
#print axioms scaled_unit_error
end Erdos970.ParityBoxObstruction
