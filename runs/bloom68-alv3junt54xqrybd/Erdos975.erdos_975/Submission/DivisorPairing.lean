import FormalConjecturesUtil

/-!
# Exact divisor pairing at an arbitrary natural cutoff

When `K * K < m`, the divisors of `m` split into three disjoint classes:
`a ≤ K`, `m / a ≤ K`, and `K < a ∧ K < m / a`. The involution `a ↦ m / a`
identifies the first two classes, giving an exact divisor-counting identity.

Division by a divisor is exact. Thus the balanced predicate also describes
`(K : ℚ) < a ∧ (K : ℚ) < m / a`; for `0 < K` this is equivalent to
`(K : ℚ) < a ∧ (a : ℚ) < m / K`. No natural floor of `m / K` is used.
The natural formulation works even for `K = 0`.

We use mathlib's `σ 0`, namely `ArithmeticFunction.sigma 0`. This is
definitionally the `ArithmeticFunction.sigma0` abbreviation in
`Submission.DivisorAverage`, without importing or redeclaring that abbreviation.
These are supporting identities only, not a solution of the full conjecture.
-/

namespace Erdos975Support

open scoped ArithmeticFunction.sigma

/-- The number of divisors of `m` at most `K`. -/
def smallDivisorCount (m K : ℕ) : ℕ :=
  (m.divisors.filter fun a ↦ a ≤ K).card

/-- The number of divisors whose two complementary factors are both greater than `K`. -/
def balancedDivisorCount (m K : ℕ) : ℕ :=
  (m.divisors.filter fun a ↦ K < a ∧ K < m / a).card

/-- The complementary factor of a divisor is again a divisor. -/
lemma complementaryDivisor_mem_divisors {m a : ℕ} (ha : a ∈ m.divisors) :
    m / a ∈ m.divisors :=
  Nat.mem_divisors.mpr
    ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha), Nat.ne_zero_of_mem_divisors ha⟩

/-- Complementary-factor division is an involution on the divisors of `m`. -/
lemma complementaryDivisor_involutive {m a : ℕ} (ha : a ∈ m.divisors) :
    m / (m / a) = a :=
  Nat.div_div_self (Nat.dvd_of_mem_divisors ha) (Nat.ne_zero_of_mem_divisors ha)

/-- Complementation is a bijection between divisors with small complement and small divisors. -/
theorem card_complementary_small_divisors (m K : ℕ) :
    (m.divisors.filter fun a ↦ m / a ≤ K).card = smallDivisorCount m K := by
  unfold smallDivisorCount
  refine Finset.card_nbij' (fun a : ℕ ↦ m / a) (fun a : ℕ ↦ m / a) ?_ ?_ ?_ ?_
  · intro a ha
    change a ∈ m.divisors.filter (fun a ↦ m / a ≤ K) at ha
    change m / a ∈ m.divisors.filter (fun a ↦ a ≤ K)
    obtain ⟨ha, haK⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨complementaryDivisor_mem_divisors ha, haK⟩
  · intro a ha
    change a ∈ m.divisors.filter (fun a ↦ a ≤ K) at ha
    change m / a ∈ m.divisors.filter (fun a ↦ m / a ≤ K)
    obtain ⟨ha, haK⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨complementaryDivisor_mem_divisors ha, ?_⟩
    rwa [complementaryDivisor_involutive ha]
  · intro a ha
    change a ∈ m.divisors.filter (fun a ↦ m / a ≤ K) at ha
    exact complementaryDivisor_involutive (Finset.mem_filter.mp ha).1
  · intro a ha
    change a ∈ m.divisors.filter (fun a ↦ a ≤ K) at ha
    exact complementaryDivisor_involutive (Finset.mem_filter.mp ha).1

/-- If `K * K < m`, a divisor and its complement cannot both be at most `K`. -/
lemma small_complementary_divisors_disjoint {m K : ℕ} (hm : K * K < m) :
    Disjoint (m.divisors.filter fun a ↦ a ≤ K)
      (m.divisors.filter fun a ↦ m / a ≤ K) := by
  refine Finset.disjoint_left.mpr ?_
  intro a ha hb
  obtain ⟨ha, haK⟩ := Finset.mem_filter.mp ha
  have hbK := (Finset.mem_filter.mp hb).2
  have hle : m ≤ K * K := by
    calc
      m = a * (m / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)).symm
      _ ≤ K * K := Nat.mul_le_mul haK hbK
  exact (Nat.not_le.mpr hm) hle

/-- Exact divisor pairing for any natural cutoff strictly below the square root of `m`. -/
theorem sigma_zero_pairing {m K : ℕ} (hm : K * K < m) :
    σ 0 m = 2 * smallDivisorCount m K + balancedDivisorCount m K := by
  let s := m.divisors.filter fun a ↦ a ≤ K
  let l := m.divisors.filter fun a ↦ m / a ≤ K
  let b := m.divisors.filter fun a ↦ K < a ∧ K < m / a
  have hsl : Disjoint s l := small_complementary_divisors_disjoint hm
  have hsb : Disjoint s b := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    have haK := (Finset.mem_filter.mp ha).2
    have hbK := (Finset.mem_filter.mp hb).2.1
    omega
  have hlb : Disjoint l b := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    have haK := (Finset.mem_filter.mp ha).2
    have hbK := (Finset.mem_filter.mp hb).2.2
    omega
  have hcover : m.divisors = s ∪ (l ∪ b) := by
    ext a
    simp only [s, l, b, Finset.mem_union, Finset.mem_filter, ← not_le]
    tauto
  have hcard : m.divisors.card = s.card + (l.card + b.card) := by
    rw [hcover,
      Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hsl, hsb⟩),
      Finset.card_union_of_disjoint hlb]
  have hl : l.card = smallDivisorCount m K := card_complementary_small_divisors m K
  rw [ArithmeticFunction.sigma_zero_apply, hcard]
  change smallDivisorCount m K + (l.card + balancedDivisorCount m K) = _
  rw [hl]
  omega

/-- On divisors, the natural quotient in the balanced predicate equals rational division. -/
lemma balancedDivisor_iff_rat {m K a : ℕ} (ha : a ∈ m.divisors) :
    (K < a ∧ K < m / a) ↔
      ((K : ℚ) < (a : ℚ) ∧ (K : ℚ) < (m : ℚ) / (a : ℚ)) := by
  have hdiv : ((m / a : ℕ) : ℚ) = (m : ℚ) / (a : ℚ) :=
    Nat.cast_div_charZero (Nat.dvd_of_mem_divisors ha)
  rw [← hdiv]
  norm_cast

/-- For a positive cutoff, the balanced predicate has the strict rational endpoint `m / K`. -/
lemma balancedDivisor_iff_rat_cutoff {m K a : ℕ}
    (ha : a ∈ m.divisors) (hK : 0 < K) :
    (K < a ∧ K < m / a) ↔
      ((K : ℚ) < (a : ℚ) ∧ (a : ℚ) < (m : ℚ) / (K : ℚ)) := by
  have haQ : (0 : ℚ) < (a : ℚ) := by exact_mod_cast Nat.pos_of_mem_divisors ha
  have hKQ : (0 : ℚ) < (K : ℚ) := by exact_mod_cast hK
  rw [balancedDivisor_iff_rat ha, lt_div_iff₀ haQ, lt_div_iff₀ hKQ, mul_comm (K : ℚ)]

/-- The balanced count agrees with the rational-inequality count when `K > 0`. -/
theorem balancedDivisorCount_eq_card_rat_cutoff (m K : ℕ) (hK : 0 < K) :
    balancedDivisorCount m K =
      (m.divisors.filter fun a : ℕ ↦
        (K : ℚ) < (a : ℚ) ∧ (a : ℚ) < (m : ℚ) / (K : ℚ)).card := by
  unfold balancedDivisorCount
  congr 1
  apply Finset.filter_congr
  intro a ha
  exact balancedDivisor_iff_rat_cutoff ha hK

/-- The exact pairing identity with a strict rational upper endpoint, for positive `K`. -/
theorem sigma_zero_pairing_rat {m K : ℕ} (hm : K * K < m) (hK : 0 < K) :
    σ 0 m = 2 * smallDivisorCount m K +
      (m.divisors.filter fun a : ℕ ↦
        (K : ℚ) < (a : ℚ) ∧ (a : ℚ) < (m : ℚ) / (K : ℚ)).card := by
  rw [sigma_zero_pairing hm, balancedDivisorCount_eq_card_rat_cutoff m K hK]

/-- Sum the exact pairing identity along any sequence satisfying the pointwise cutoff bound. -/
theorem sum_sigma_zero_pairing {g : ℕ → ℕ} {N K : ℕ}
    (hg : ∀ n ∈ Finset.Iic N, K * K < g n) :
    (∑ n ∈ Finset.Iic N, σ 0 (g n)) =
      2 * (∑ n ∈ Finset.Iic N, smallDivisorCount (g n) K) +
        ∑ n ∈ Finset.Iic N, balancedDivisorCount (g n) K := by
  calc
    (∑ n ∈ Finset.Iic N, σ 0 (g n)) =
        ∑ n ∈ Finset.Iic N,
          (2 * smallDivisorCount (g n) K + balancedDivisorCount (g n) K) :=
      Finset.sum_congr rfl fun n hn ↦ sigma_zero_pairing (hg n hn)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

end Erdos975Support
