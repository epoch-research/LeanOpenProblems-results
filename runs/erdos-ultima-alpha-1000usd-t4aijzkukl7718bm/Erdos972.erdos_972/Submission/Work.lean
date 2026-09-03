import FormalConjecturesUtil
/-! Auxiliary checks for the prime-approximation formulation. -/
namespace Erdos972

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊ (α * p) ⌋₊}

theorem primeSet_infinite_iff_approximation {α : ℝ}
    (hα : 0 ≤ α) (hI : Irrational α) :
    (primeSet α).Infinite ↔ ∀ N : ℕ, ∃ p q : ℕ,
      N < p ∧ Nat.Prime p ∧ Nat.Prime q ∧
      (q : ℝ) < α * p ∧ α * p < (q : ℝ) + 1 := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h N
    obtain ⟨hprime, hfloor⟩ := hp
    refine ⟨p, ⌊α * p⌋₊, hNp, hprime, hfloor, ?_, Nat.lt_floor_add_one _⟩
    exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
      ((hI.mul_natCast hprime.ne_zero).ne_nat _).symm
  · intro h N
    obtain ⟨p, q, hNp, hp, hq, hlo, hhi⟩ := h N
    refine ⟨p, ⟨hp, ?_⟩, hNp⟩
    have hf : ⌊α * p⌋₊ = q := (Nat.floor_eq_iff (mul_nonneg hα (Nat.cast_nonneg p))).mpr ⟨hlo.le, hhi⟩
    simpa only [hf] using hq

theorem primeSet_integer_empty {a : ℕ} (ha : 2 ≤ a) : primeSet (a : ℝ) = ∅ := by
  ext p
  simp only [primeSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp
  rw [← Nat.cast_mul, Nat.floor_natCast]
  exact Nat.not_prime_mul (by omega) hp.ne_one

theorem conjecture_negation_iff :
    (¬ (∀ α > 1, Irrational α → (primeSet α).Infinite)) ↔
      ∃ α : ℝ, 1 < α ∧ Irrational α ∧ ∃ N : ℕ,
        ∀ p : ℕ, N < p → Nat.Prime p → ¬ Nat.Prime ⌊α * p⌋₊ := by
  classical
  simp only [Set.infinite_iff_exists_gt, primeSet, Set.mem_setOf_eq]
  push_neg
  constructor
  · rintro ⟨α, hα, hI, N, hN⟩
    exact ⟨α, hα, hI, N, fun p hp hprime hfloor =>
      (not_le_of_gt hp) (hN p ⟨hprime, hfloor⟩)⟩
  · rintro ⟨α, hα, hI, N, hN⟩
    refine ⟨α, hα, hI, N, fun p hp => ?_⟩
    by_contra h
    exact hN p (lt_of_not_ge h) hp.1 hp.2

theorem arbitrarily_long_initial_gap (N : ℕ) :
    ∃ α : ℝ, 1 < α ∧ Irrational α ∧ ∀ p : ℕ, p ≤ N → p ∉ primeSet α := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨δ, hI, hδ, hδN⟩ := exists_irrational_btwn
    (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity)
  refine ⟨2 + δ, by linarith, by simpa using hI.natCast_add 2, ?_⟩
  intro p hp hmem
  have hpN : (p : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hp
  have hδp : δ * p < 1 := by
    have h := (lt_div_iff₀ hN).mp hδN
    nlinarith [mul_le_mul_of_nonneg_left hpN hδ.le]
  have hf : ⌊(2 + δ) * p⌋₊ = 2 * p := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    push_cast
    constructor
    · nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg p)]
    · nlinarith
  have hp' : Nat.Prime p := hmem.1
  have hf' : Nat.Prime (2 * p) := by simpa only [hf] using hmem.2
  exact Nat.not_prime_mul (by decide) hp'.ne_one hf'

open Filter Topology in
theorem primeSet_eventually_of_tendsto {a : ℕ → ℝ} {α : ℝ}
    (hlim : Tendsto a atTop (𝓝 α)) (hα : 0 ≤ α) (hI : Irrational α)
    {p : ℕ} (hp : p ∈ primeSet α) : ∀ᶠ n in atTop, p ∈ primeSet (a n) := by
  have hlo : (⌊α * p⌋₊ : ℝ) < α * p :=
    lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
      ((hI.mul_natCast hp.1.ne_zero).ne_nat _).symm
  have hhi := Nat.lt_floor_add_one (α * p)
  have he := (hlim.mul_const (p : ℝ)).eventually (Ioo_mem_nhds hlo hhi)
  filter_upwards [he] with n hn
  have hf : ⌊a n * p⌋₊ = ⌊α * p⌋₊ :=
    (Nat.floor_eq_iff' hp.2.ne_zero).mpr ⟨hn.1.le, hn.2⟩
  exact ⟨hp.1, by simpa only [hf] using hp.2⟩

open Filter Topology in
theorem primeSet_finite_of_initial_gaps_limit {a : ℕ → ℝ} {α : ℝ}
    (hlim : Tendsto a atTop (𝓝 α)) (hα : 0 ≤ α) (hI : Irrational α)
    (N₀ : ℕ) (hgap : ∀ n p : ℕ, p ≤ n → N₀ < p → p ∉ primeSet (a n)) :
    (primeSet α).Finite := by
  apply (Set.finite_Iic N₀).subset
  intro p hp
  change p ≤ N₀
  by_contra h
  have he := primeSet_eventually_of_tendsto hlim hα hI hp
  obtain ⟨n, hpn, hn⟩ := ((eventually_ge_atTop p).and he).exists
  exact hgap n p hpn (Nat.lt_of_not_ge h) hn

open Filter Topology in
theorem conjecture_false_of_initial_gaps_irrational_limit {a : ℕ → ℝ} {α : ℝ}
    (hlim : Tendsto a atTop (𝓝 α)) (hα : 1 < α) (hI : Irrational α)
    (N₀ : ℕ) (hgap : ∀ n p : ℕ, p ≤ n → N₀ < p → p ∉ primeSet (a n)) :
    ¬ (∀ β > 1, Irrational β → (primeSet β).Infinite) := by
  intro h
  exact (h α hα hI)
    (primeSet_finite_of_initial_gaps_limit hlim (by linarith) hI N₀ hgap)

#print axioms conjecture_false_of_initial_gaps_irrational_limit
#print axioms primeSet_finite_of_initial_gaps_limit
#print axioms primeSet_eventually_of_tendsto
#print axioms arbitrarily_long_initial_gap
#print axioms conjecture_negation_iff
#print axioms primeSet_infinite_iff_approximation
#print axioms primeSet_integer_empty
end Erdos972
