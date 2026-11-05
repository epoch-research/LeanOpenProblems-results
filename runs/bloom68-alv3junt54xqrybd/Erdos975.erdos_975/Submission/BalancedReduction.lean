import Submission.DivisorPairing
import Submission.RealCutoff

/-!
# Exact reduction to balanced divisors

An overlap correction makes divisor pairing valid for every value and every
cutoff, including zero. Consequently the normalized summatory limit is
equivalent to the balanced-divisor limit, provided the small-divisor limit
and vanishing overlap error have been established. No such hypotheses are
assumed to hold for arbitrary polynomial values in this module.
-/

namespace Erdos975Support

open Filter
open scoped Topology

/-- The overlap between a small divisor and a small complementary divisor. -/
def overlapDivisorCount (m K : ℕ) : ℕ :=
  (m.divisors.filter fun a ↦ a ≤ K ∧ m / a ≤ K).card

/-- Divisor pairing with its overlap correction, without any size hypothesis. -/
theorem sigma_zero_pairing_with_overlap (m K : ℕ) :
    ArithmeticFunction.sigma 0 m + overlapDivisorCount m K =
      2 * smallDivisorCount m K + balancedDivisorCount m K := by
  let s := m.divisors.filter fun a ↦ a ≤ K
  let l := m.divisors.filter fun a ↦ m / a ≤ K
  let b := m.divisors.filter fun a ↦ K < a ∧ K < m / a
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
  have hcover : m.divisors = (s ∪ l) ∪ b := by
    ext a
    simp only [s, l, b, Finset.mem_union, Finset.mem_filter, ← not_le]
    tauto
  have hinter : s ∩ l = m.divisors.filter (fun a ↦ a ≤ K ∧ m / a ≤ K) := by
    ext a
    simp only [s, l, Finset.mem_inter, Finset.mem_filter]
    tauto
  have hc : m.divisors.card + overlapDivisorCount m K = s.card + l.card + b.card := by
    rw [hcover, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hsb, hlb⟩)]
    change (s ∪ l).card + b.card + (m.divisors.filter fun a ↦ a ≤ K ∧ m / a ≤ K).card = _
    rw [← hinter]
    have h := Finset.card_union_add_card_inter s l
    omega
  rw [ArithmeticFunction.sigma_zero_apply, hc]
  change smallDivisorCount m K + l.card + balancedDivisorCount m K = _
  rw [show l.card = smallDivisorCount m K from card_complementary_small_divisors m K]
  omega

lemma overlapDivisorCount_eq_zero {m K : ℕ} (hm : K * K < m) :
    overlapDivisorCount m K = 0 := by
  unfold overlapDivisorCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨ha, haK, hcomp⟩ := Finset.mem_filter.mp ha
  have hle : m ≤ K * K := by
    calc
      m = a * (m / a) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors ha)).symm
      _ ≤ K * K := Nat.mul_le_mul haK hcomp
  exact (Nat.not_le.mpr hm) hle

lemma overlapDivisorCount_le_sigma (m K : ℕ) :
    overlapDivisorCount m K ≤ ArithmeticFunction.sigma 0 m := by
  rw [ArithmeticFunction.sigma_zero_apply]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A divisor summatory function along an arbitrary natural-valued sequence. -/
noncomputable def divisorAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (ArithmeticFunction.sigma 0 (g n) : ℝ)

/-- Small divisors at the common cutoff `N`. -/
noncomputable def smallAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (smallDivisorCount (g n) N : ℝ)

/-- Ordered balanced divisor pairs with both factors greater than the cutoff. -/
noncomputable def balancedAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (balancedDivisorCount (g n) N : ℝ)

/-- The small-factor overlap correction. -/
noncomputable def overlapAlong (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Iic N, (overlapDivisorCount (g n) N : ℝ)

lemma along_pairing (g : ℕ → ℕ) (N : ℕ) :
    divisorAlong g N + overlapAlong g N = 2 * smallAlong g N + balancedAlong g N := by
  unfold divisorAlong overlapAlong smallAlong balancedAlong
  rw [← Finset.sum_add_distrib]
  calc
    (∑ n ∈ Finset.Iic N,
      ((ArithmeticFunction.sigma 0 (g n) : ℝ) + (overlapDivisorCount (g n) N : ℝ))) =
        ∑ n ∈ Finset.Iic N,
          (2 * (smallDivisorCount (g n) N : ℝ) + (balancedDivisorCount (g n) N : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact_mod_cast sigma_zero_pairing_with_overlap (g n) N
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

lemma balancedAlong_nonneg (g : ℕ → ℕ) (N : ℕ) : 0 ≤ balancedAlong g N :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- Exact relation between the four normalized quantities. -/
lemma normalized_along_pairing (g : ℕ → ℕ) (N : ℕ) :
    divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)) =
      2 * (smallAlong g N / ((N : ℝ) * Real.log (N : ℝ))) +
        balancedAlong g N / ((N : ℝ) * Real.log (N : ℝ)) -
          overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)) := by
  rw [eq_sub_of_add_eq (along_pairing g N), sub_div, add_div, mul_div_assoc]

/-- Once the small-divisor limit and overlap error are controlled, the only
remaining limit is the balanced term. -/
theorem balanced_limit_iff {g : ℕ → ℕ} {κ c : ℝ}
    (hs : Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ))
    (ho : Tendsto (fun N : ℕ ↦ overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦ divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
        atTop (𝓝 c) ↔
      Tendsto (fun N : ℕ ↦ balancedAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
        atTop (𝓝 (c - 2 * κ)) := by
  constructor
  · intro ht
    have h := (ht.sub (hs.const_mul 2)).add ho
    simp only [add_zero] at h
    apply h.congr
    intro N
    rw [normalized_along_pairing]
    ring
  · intro ht
    have h := ((hs.const_mul 2).add ht).sub ho
    have hc : 2 * κ + (c - 2 * κ) - 0 = c := by ring
    rw [hc] at h
    apply h.congr
    intro N
    exact (normalized_along_pairing g N).symm

/-- A finite limit of the balanced term is necessarily nonnegative. -/
lemma balanced_limit_nonneg {g : ℕ → ℕ} {L : ℝ}
    (hL : Tendsto (fun N : ℕ ↦ balancedAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 L)) : 0 ≤ L := by
  apply ge_of_tendsto hL
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  exact div_nonneg (balancedAlong_nonneg g N)
    (mul_nonneg (Nat.cast_nonneg N) (Real.log_pos hN1).le)

/-- Existence of the remaining finite balanced limit implies positivity of the
full limit, without identifying either constant. -/
theorem exists_divisor_limit_iff_exists_balanced_limit {g : ℕ → ℕ} {κ : ℝ}
    (hκ : 0 < κ)
    (hs : Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ))
    (ho : Tendsto (fun N : ℕ ↦ overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0)) :
    (∃ c > (0 : ℝ),
      Tendsto (fun N : ℕ ↦ divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
        atTop (𝓝 c)) ↔
      ∃ L : ℝ,
        Tendsto (fun N : ℕ ↦ balancedAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
          atTop (𝓝 L) := by
  constructor
  · rintro ⟨c, _, hc⟩
    exact ⟨c - 2 * κ, (balanced_limit_iff hs ho).mp hc⟩
  · rintro ⟨L, hL⟩
    have hL0 := balanced_limit_nonneg hL
    refine ⟨2 * κ + L, by positivity, (balanced_limit_iff hs ho).mpr ?_⟩
    simpa only [add_sub_cancel_left] using hL

end Erdos975Support
