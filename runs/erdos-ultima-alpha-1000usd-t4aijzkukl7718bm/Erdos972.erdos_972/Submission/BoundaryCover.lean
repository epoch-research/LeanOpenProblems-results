import FormalConjecturesUtil

/-!
Finite prime-pair coverage, and the precise obstruction to a uniform bound
at the rational boundary 2. These results do not settle Erdős 972.
-/

namespace Erdos972Boundary

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ (⌊α * p⌋₊).Prime}

lemma mem_primeSet_of_bounds {α : ℝ} {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hlo : (q : ℝ) ≤ α * p) (hhi : α * p < (q : ℝ) + 1) :
    p ∈ primeSet α := by
  refine ⟨hp, ?_⟩
  have hf : ⌊α * p⌋₊ = q := (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hlo, hhi⟩
  simpa only [hf] using hq

/-- Four small inputs cover the entire interval `[1, 2)`, including its rational slopes.
This provides one witness, not infinitely many witnesses. -/
theorem first_pair_below_two {α : ℝ} (hlo : 1 ≤ α) (hhi : α < 2) :
    ∃ p : ℕ, p ≤ 7 ∧ p ∈ primeSet α := by
  by_cases h₁ : α < 3 / 2
  · refine ⟨2, by omega, mem_primeSet_of_bounds (by norm_num) (show Nat.Prime 2 by norm_num) ?_ ?_⟩ <;>
      norm_num only [Nat.cast_ofNat] <;> linarith
  by_cases h₂ : α < 8 / 5
  · refine ⟨5, by omega, mem_primeSet_of_bounds (by norm_num) (show Nat.Prime 7 by norm_num) ?_ ?_⟩ <;>
      norm_num only [Nat.cast_ofNat] <;> linarith
  by_cases h₃ : α < 5 / 3
  · refine ⟨7, by omega, mem_primeSet_of_bounds (by norm_num) (show Nat.Prime 11 by norm_num) ?_ ?_⟩ <;>
      norm_num only [Nat.cast_ofNat] <;> linarith
  · refine ⟨3, by omega, mem_primeSet_of_bounds (by norm_num) (show Nat.Prime 5 by norm_num) ?_ ?_⟩ <;>
      norm_num only [Nat.cast_ofNat] <;> linarith

/-- Immediately to the left of 2, every fixed input has output `2*p - 1`. -/
lemma floor_left_of_two {δ : ℝ} {p : ℕ} (hp : 0 < p)
    (hδ : 0 < δ) (hsmall : δ * p ≤ 1) :
    ⌊(2 - δ) * p⌋₊ = 2 * p - 1 := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hn : 1 ≤ 2 * p := by omega
  have hcast : ((2 * p - 1 : ℕ) : ℝ) = 2 * p - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  apply (Nat.floor_eq_iff' (by omega : 2 * p - 1 ≠ 0)).mpr
  rw [hcast]
  constructor
  · nlinarith
  · nlinarith

/-- On the other side of an integer at least two, every qualifying input
must exceed the elementary prime-free scale. -/
theorem input_lower_bound_right_of_integer {a p : ℕ} {α : ℝ}
    (ha : 2 ≤ a) (hα : (a : ℝ) < α) (hp : p ∈ primeSet α) :
    1 / (α - a) ≤ (p : ℝ) := by
  have hδ : 0 < α - a := sub_pos.mpr hα
  apply (div_le_iff₀ hδ).mpr
  by_contra h
  have hsmall : (α - a) * p < 1 := by nlinarith
  have hα0 : 0 ≤ α := (Nat.cast_nonneg a).trans hα.le
  have hf : ⌊α * p⌋₊ = a * p := by
    apply (Nat.floor_eq_iff (mul_nonneg hα0 (Nat.cast_nonneg p))).mpr
    push_cast
    constructor
    · exact mul_le_mul_of_nonneg_right hα.le (Nat.cast_nonneg p)
    · nlinarith
  have hprime : (a * p).Prime := by simpa only [hf] using hp.2
  exact Nat.not_prime_mul (by omega) hp.1.ne_one hprime

/-- A finite uniform input bound for irrational slopes approaching 2 from below
is equivalent to a prime pair of the specific form `p, 2*p - 1`.
The original conjecture does not provide this boundary uniformity. -/
theorem uniform_left_boundary_iff (N : ℕ) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, ∀ α : ℝ,
      2 - ε < α → α < 2 → Irrational α →
        ∃ p : ℕ, N < p ∧ p ≤ M ∧ p ∈ primeSet α) ↔
      ∃ p : ℕ, N < p ∧ p.Prime ∧ (2 * p - 1).Prime := by
  constructor
  · rintro ⟨ε, hε, M, hcover⟩
    have hbound : (0 : ℝ) < min ε (1 / ((M : ℝ) + 1)) := by
      apply lt_min hε
      positivity
    obtain ⟨δ, hI, hδ, hδbound⟩ := exists_irrational_btwn hbound
    have hδε : δ < ε := hδbound.trans_le (min_le_left _ _)
    have hδM : δ < 1 / ((M : ℝ) + 1) :=
      hδbound.trans_le (min_le_right _ _)
    have hαI : Irrational (2 - δ) := by
      simpa using hI.natCast_sub 2
    obtain ⟨p, hNp, hpM, hp, hprime⟩ :=
      hcover (2 - δ) (by linarith) (by linarith) hαI
    have hsmallM : δ * ((M : ℝ) + 1) < 1 :=
      (lt_div_iff₀ (by positivity)).mp hδM
    have hsmall : δ * p ≤ 1 := by
      have hle : (p : ℝ) ≤ M := Nat.cast_le.mpr hpM
      nlinarith
    rw [floor_left_of_two hp.pos hδ hsmall] at hprime
    exact ⟨p, hNp, hp, hprime⟩
  · rintro ⟨p, hNp, hp, hprime⟩
    have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    refine ⟨1 / p, by positivity, p, ?_⟩
    intro α hlo hhi _
    refine ⟨p, hNp, le_rfl, hp, ?_⟩
    have hδ : 0 < 2 - α := by linarith
    have hsmall : (2 - α) * p ≤ 1 := by
      have hlt : 2 - α < 1 / p := by linarith
      exact ((lt_div_iff₀ hpR).mp hlt).le
    have hf := floor_left_of_two hp.pos hδ hsmall
    have he : 2 - (2 - α) = α := by ring
    rw [he] at hf
    simpa only [hf] using hprime

#print axioms input_lower_bound_right_of_integer
#print axioms first_pair_below_two
#print axioms uniform_left_boundary_iff

end Erdos972Boundary
