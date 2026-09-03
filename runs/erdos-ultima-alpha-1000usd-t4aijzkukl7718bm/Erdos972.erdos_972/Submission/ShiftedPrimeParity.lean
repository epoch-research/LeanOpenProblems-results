import FormalConjecturesUtil

/-! Exact parity constraints on proposed shifts of the original problem.
These lemmas do not prove infinitude for any prescribed irrational slope. -/
namespace Erdos972ShiftedPrimeParity

/-- Prime inputs and prime outputs, allowing a fixed intercept. -/
def shiftedPrimeSet (α β : ℝ) : Set ℕ :=
  {p | Nat.Prime p ∧ Nat.Prime ⌊α * p + β⌋₊}

lemma floor_slope_nat_shift {α : ℝ} (hα : 0 ≤ α) (k p : ℕ) :
    ⌊(α + k) * p⌋₊ = ⌊α * p⌋₊ + k * p := by
  have h : (α + (k : ℝ)) * (p : ℝ) = α * p + (k * p : ℕ) := by
    push_cast
    ring
  rw [h, Nat.floor_add_natCast (by positivity)]

/-- At an odd prime input above two, an odd integral change of slope
cannot preserve prime output, provided the original slope is at least one. -/
theorem not_both_prime_odd_slope_shift {α : ℝ} (hα : 1 ≤ α)
    {k p : ℕ} (hk : Odd k) (hp : Nat.Prime p) (hp2 : 2 < p) :
    ¬ (Nat.Prime ⌊α * p⌋₊ ∧ Nat.Prime ⌊(α + k) * p⌋₊) := by
  rintro ⟨hq, hr⟩
  have hpq : p ≤ ⌊α * p⌋₊ := Nat.le_floor (by
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith)
  have hq2 : ⌊α * p⌋₊ ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hqodd : Odd ⌊α * p⌋₊ := hq.odd_of_ne_two hq2
  rw [floor_slope_nat_shift (by linarith)] at hr
  have he : Even (⌊α * p⌋₊ + k * p) := hqodd.add_odd (hk.mul hpodd)
  have hh := hr.even_iff.mp he
  omega

/-- The original and odd-integrally-translated prime-input sets can have
at most the input two in common. No preservation of infinitude follows. -/
theorem odd_slope_shift_inter_subset {α : ℝ} (hα : 1 ≤ α)
    {k : ℕ} (hk : Odd k) :
    shiftedPrimeSet α 0 ∩ shiftedPrimeSet (α + k) 0 ⊆ {2} := by
  intro p hp
  rcases hp with ⟨⟨hprime, hq⟩, ⟨_, hr⟩⟩
  simp only [add_zero] at hq hr
  have hp2 := hprime.two_le
  by_contra h
  have hne : p ≠ 2 := by simpa using h
  exact not_both_prime_odd_slope_shift hα hk hprime (by omega) ⟨hq, hr⟩

/-- Two adjacent natural numbers can both be prime only at the pair 2,3. -/
lemma prime_and_succ_prime {n : ℕ} (hn : Nat.Prime n)
    (hs : Nat.Prime (n + 1)) : n = 2 := by
  by_contra h
  have he : Even (n + 1) := (hn.odd_of_ne_two h).add_odd (by decide : Odd (1 : ℕ))
  have hh := hs.even_iff.mp he
  have := hn.two_le
  omega

/-- An intercept change by one cannot preserve prime output above input two. -/
theorem unit_intercept_inter_subset {α : ℝ} (hα : 1 ≤ α) :
    shiftedPrimeSet α 0 ∩ shiftedPrimeSet α 1 ⊆ {2} := by
  intro p hp
  rcases hp with ⟨⟨hprime, hq⟩, ⟨_, hr⟩⟩
  simp only [add_zero] at hq
  rw [Nat.floor_add_one (by positivity)] at hr
  have hq2 := prime_and_succ_prime hq hr
  have hpq : p ≤ ⌊α * p⌋₊ := Nat.le_floor (by
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith)
  have hp2 := hprime.two_le
  simp only [Set.mem_singleton_iff]
  omega

/-- A bounded nonnegative intercept changes the natural floor by at most one. -/
lemma floor_bounded_intercept {x β : ℝ} (hx : 0 ≤ x)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ⌊x + β⌋₊ = ⌊x⌋₊ ∨ ⌊x + β⌋₊ = ⌊x⌋₊ + 1 := by
  have hlo : ⌊x⌋₊ ≤ ⌊x + β⌋₊ := Nat.floor_mono (by linarith)
  have hhi : ⌊x + β⌋₊ ≤ ⌊x⌋₊ + 1 := by
    calc
      ⌊x + β⌋₊ ≤ ⌊x + 1⌋₊ := Nat.floor_mono (by linarith)
      _ = ⌊x⌋₊ + 1 := Nat.floor_add_one hx
  omega

/-- If both the original and a bounded-intercept output are prime above
input two, the two outputs must in fact be equal. -/
theorem equal_outputs_of_both_prime {α β : ℝ} (hα : 1 ≤ α)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {p : ℕ} (hp2 : 2 < p)
    (hq : Nat.Prime ⌊α * p⌋₊) (hr : Nat.Prime ⌊α * p + β⌋₊) :
    ⌊α * p + β⌋₊ = ⌊α * p⌋₊ := by
  rcases floor_bounded_intercept (by positivity : 0 ≤ α * p) hβ0 hβ1 with h | h
  · exact h
  · rw [h] at hr
    have he := prime_and_succ_prime hq hr
    have hpq : p ≤ ⌊α * p⌋₊ := Nat.le_floor (by
      have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      nlinarith)
    omega

#print axioms not_both_prime_odd_slope_shift
#print axioms odd_slope_shift_inter_subset
#print axioms unit_intercept_inter_subset
#print axioms equal_outputs_of_both_prime

end Erdos972ShiftedPrimeParity
