import FormalConjecturesUtil

/-!
# Occupation counts and modular variance

For any finite residue type `α` and any map `f : Fin n → α`, this module defines
natural-number occupation counts and the rational normalized variance
`V = q * ∑ a, (N_a / n)^2 - 1`, where `q = Fintype.card α`.

The collision count counts **ordered** pairs of indices, including the diagonal.
We prove the exact collision identity, nonnegativity for `0 < n`, and the lower
bound `1 / (q - 1)` when a residue class is omitted and `1 < q`. The key
omitted-class inequality is also proved over `ℕ`, without division. A
sum-of-squares identity also characterizes zero variance as full uniform
occupation: `q * N_a = n` for every `a`.

No field structure, injectivity, independence, or equidistribution assumption
is imposed on `f`. In particular, for points `x : Fin n → G` and a residue map
`r : G → α`, use `f := r ∘ x`; injectivity of `x` is unnecessary for these facts.
The counting results also cover `n = 0`; all variance conclusions explicitly
require `0 < n`. That hypothesis already forces `α` to be nonempty.

This is independent finite counting infrastructure relevant to a capped
variance candidate. It does **not** prove CVL (a capped variance lemma), any
path-geometric estimate, or the Gaussian moat theorem. It neither imports nor
changes `Submission.Spec`.
-/

namespace Erdos952.ModularVariance

open scoped BigOperators

variable {α : Type*} {n : ℕ}

/-- Number of indices with residue `a`. Repeated residues are counted with
multiplicity, even when the underlying points are distinct. -/
noncomputable def occupationCount (f : Fin n → α) (a : α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = a)).card

/-- Number of ordered equal-residue pairs of indices, including `(i, i)`. -/
noncomputable def collisionCount (f : Fin n → α) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin n × Fin n => f p.1 = f p.2)).card

/-- Zero occupation is exactly omission of a residue class. -/
theorem occupationCount_eq_zero_iff (f : Fin n → α) (a : α) :
    occupationCount f a = 0 ↔ ∀ i, f i ≠ a := by
  classical
  simp [occupationCount]

variable [Fintype α]

/-- Rational normalized occupation variance. The division is in `ℚ`, not `ℕ`.
Theorems about its probabilistic interpretation require `0 < n`. -/
noncomputable def variance (f : Fin n → α) : ℚ :=
  (Fintype.card α : ℚ) * ∑ a, ((occupationCount f a : ℚ) / (n : ℚ)) ^ 2 - 1

/-- Every index belongs to exactly one residue class. -/
theorem sum_occupationCount (f : Fin n → α) :
    ∑ a, occupationCount f a = n := by
  classical
  simpa [occupationCount] using
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset α) f

/-- The total occupation count, cast to `ℚ`. -/
theorem sum_occupationCount_rat (f : Fin n → α) :
    ∑ a, (occupationCount f a : ℚ) = (n : ℚ) := by
  exact_mod_cast sum_occupationCount f

/-- Partitioning ordered collisions by their common residue gives a sum of
squares of occupation counts. This holds even for `n = 0`. -/
theorem collisionCount_eq_sum_sq (f : Fin n → α) :
    collisionCount f = ∑ a, occupationCount f a ^ 2 := by
  classical
  let C : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p => f p.1 = f p.2)
  have hfiber (a : α) :
      C.filter (fun p => f p.1 = a) =
        (Finset.univ.filter (fun i => f i = a)) ×ˢ
          (Finset.univ.filter (fun i => f i = a)) := by
    ext p
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨hij, hi⟩
      exact ⟨hi, hij.symm.trans hi⟩
    · rintro ⟨hi, hj⟩
      exact ⟨hi.trans hj.symm, hi⟩
  calc
    collisionCount f = C.card := rfl
    _ = ∑ a : α, (C.filter (fun p => f p.1 = a)).card :=
      Finset.card_eq_sum_card_fiberwise
        (f := fun p : Fin n × Fin n => f p.1) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)
    _ = ∑ a, occupationCount f a ^ 2 := by
      simp only [hfiber, Finset.card_product, occupationCount, pow_two]

/-- Clearing the positive sample-size denominator in the variance. -/
theorem sq_mul_variance (f : Fin n → α) (hn : 0 < n) :
    (n : ℚ) ^ 2 * variance f =
      (Fintype.card α : ℚ) * ∑ a, (occupationCount f a : ℚ) ^ 2 - (n : ℚ) ^ 2 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (∑ a, ((occupationCount f a : ℚ) / (n : ℚ)) ^ 2) =
      (∑ a, (occupationCount f a : ℚ) ^ 2) / (n : ℚ) ^ 2 := by
    simp_rw [div_pow]
    rw [Finset.sum_div]
  rw [variance, hsum]
  field_simp [hn0]

/-- Exact collision identity: `n² V = q C - n²`, where `C` counts ordered
pairs with equal residue, including diagonal pairs. -/
theorem collision_identity (f : Fin n → α) (hn : 0 < n) :
    (n : ℚ) ^ 2 * variance f =
      (Fintype.card α : ℚ) * (collisionCount f : ℚ) - (n : ℚ) ^ 2 := by
  rw [sq_mul_variance f hn, collisionCount_eq_sum_sq]
  simp only [Nat.cast_sum, Nat.cast_pow]

/-- The natural-number Cauchy--Schwarz bound for all residue classes. -/
theorem sq_le_card_mul_sum_sq (f : Fin n → α) :
    n ^ 2 ≤ Fintype.card α * ∑ a, occupationCount f a ^ 2 := by
  simpa only [sum_occupationCount, Finset.card_univ, Nat.cast_id] using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset α)) (f := occupationCount f))

/-- Normalized occupation variance is nonnegative for a nonempty sample. -/
theorem variance_nonneg (f : Fin n → α) (hn : 0 < n) :
    0 ≤ variance f := by
  have hbound : (n : ℚ) ^ 2 ≤
      (Fintype.card α : ℚ) * ∑ a, (occupationCount f a : ℚ) ^ 2 := by
    exact_mod_cast sq_le_card_mul_sum_sq f
  have hn2 : 0 < (n : ℚ) ^ 2 := by positivity
  apply (mul_nonneg_iff_of_pos_left hn2).mp
  rw [sq_mul_variance f hn]
  exact sub_nonneg.mpr hbound

/-- Removing an empty class improves the natural-number Cauchy--Schwarz
factor from `q` to `q - 1`. Neither `0 < n` nor `1 < q` is needed here. -/
theorem sq_le_card_sub_one_mul_sum_sq (f : Fin n → α) (a : α)
    (ha : occupationCount f a = 0) :
    n ^ 2 ≤ (Fintype.card α - 1) * ∑ b, occupationCount f b ^ 2 := by
  classical
  have hsum : ∑ b ∈ (Finset.univ : Finset α).erase a, occupationCount f b = n := by
    simpa only [ha, add_zero, sum_occupationCount] using
      (Finset.sum_erase_add Finset.univ (occupationCount f) (Finset.mem_univ a))
  have hsq : ∑ b ∈ (Finset.univ : Finset α).erase a, occupationCount f b ^ 2 =
      ∑ b, occupationCount f b ^ 2 := by
    simpa only [ha, zero_pow (by decide : 2 ≠ 0), add_zero] using
      (Finset.sum_erase_add Finset.univ
        (fun b => occupationCount f b ^ 2) (Finset.mem_univ a))
  simpa only [hsum, hsq, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, Nat.cast_id] using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset α).erase a) (f := occupationCount f))

/-- An empty class forces variance at least `1 / (q - 1)`. The hypotheses
`0 < n` and `1 < q` explicitly ensure the denominators are positive. -/
theorem one_div_card_sub_one_le_variance_of_count_eq_zero (f : Fin n → α)
    (hn : 0 < n) (hq : 1 < Fintype.card α) (a : α)
    (ha : occupationCount f a = 0) :
    1 / ((Fintype.card α : ℚ) - 1) ≤ variance f := by
  have hn2 : 0 < (n : ℚ) ^ 2 := by positivity
  have hq1 : (1 : ℚ) < (Fintype.card α : ℚ) := by exact_mod_cast hq
  have hqpos : 0 < (Fintype.card α : ℚ) - 1 := sub_pos.mpr hq1
  have hbound : (n : ℚ) ^ 2 ≤
      ((Fintype.card α - 1 : ℕ) : ℚ) * ∑ b, (occupationCount f b : ℚ) ^ 2 := by
    exact_mod_cast sq_le_card_sub_one_mul_sum_sq f a ha
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card α), Nat.cast_one] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound
    (show (0 : ℚ) ≤ (Fintype.card α : ℚ) by positivity)
  apply (div_le_iff₀ hqpos).mpr
  apply (mul_le_mul_iff_right₀ hn2).mp
  calc
    (n : ℚ) ^ 2 * 1 ≤
        ((Fintype.card α : ℚ) * ∑ b, (occupationCount f b : ℚ) ^ 2 - (n : ℚ) ^ 2) *
          ((Fintype.card α : ℚ) - 1) := by
      nlinarith only [hmul]
    _ = (n : ℚ) ^ 2 * (variance f * ((Fintype.card α : ℚ) - 1)) := by
      rw [← sq_mul_variance f hn]
      ring

/-- Residue-map formulation of the omitted-class lower bound: it is enough
that some `a` is never attained by `f`. -/
theorem one_div_card_sub_one_le_variance_of_omitted (f : Fin n → α)
    (hn : 0 < n) (hq : 1 < Fintype.card α)
    (hmiss : ∃ a : α, ∀ i, f i ≠ a) :
    1 / ((Fintype.card α : ℚ) - 1) ≤ variance f := by
  obtain ⟨a, ha⟩ := hmiss
  exact one_div_card_sub_one_le_variance_of_count_eq_zero f hn hq a
    ((occupationCount_eq_zero_iff f a).mpr ha)

/-- A sum-of-squares expression for the unnormalized deviation from uniform
occupation. It is valid even for an empty sample. -/
theorem sum_sq_centered_counts (f : Fin n → α) :
    (∑ a, ((Fintype.card α : ℚ) * (occupationCount f a : ℚ) - (n : ℚ)) ^ 2) =
      (Fintype.card α : ℚ) *
        ((Fintype.card α : ℚ) * ∑ a, (occupationCount f a : ℚ) ^ 2 - (n : ℚ) ^ 2) := by
  calc
    _ = ∑ a, ((Fintype.card α : ℚ) ^ 2 * (occupationCount f a : ℚ) ^ 2 -
        (2 * (Fintype.card α : ℚ) * (n : ℚ)) * (occupationCount f a : ℚ) +
          (n : ℚ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_occupationCount_rat]
      ring

/-- Variance vanishes exactly for full uniform occupation. The right-hand
side is a natural-number equality, equivalent to `N_a = n / q` in `ℚ`.
No divisibility or uniformity hypothesis is assumed in advance. -/
theorem variance_eq_zero_iff_uniform (f : Fin n → α) (hn : 0 < n) :
    variance f = 0 ↔ ∀ a, Fintype.card α * occupationCount f a = n := by
  have hn2 : (n : ℚ) ^ 2 ≠ 0 := by positivity
  have hq : (Fintype.card α : ℚ) ≠ 0 := by
    have hcard : 0 < Fintype.card α :=
      Fintype.card_pos_iff.mpr ⟨f ⟨0, hn⟩⟩
    positivity
  have hcenter :
      (∑ a, ((Fintype.card α : ℚ) * (occupationCount f a : ℚ) - (n : ℚ)) ^ 2) =
        (Fintype.card α : ℚ) * ((n : ℚ) ^ 2 * variance f) := by
    rw [sum_sq_centered_counts, sq_mul_variance f hn]
  constructor
  · intro hv a
    have hzero :
        (∑ b, ((Fintype.card α : ℚ) * (occupationCount f b : ℚ) - (n : ℚ)) ^ 2) = 0 := by
      simpa only [hv, mul_zero] using hcenter
    have ha : ((Fintype.card α : ℚ) * (occupationCount f a : ℚ) - (n : ℚ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg _)).mp hzero a (Finset.mem_univ a)
    have ha' : (Fintype.card α : ℚ) * (occupationCount f a : ℚ) = (n : ℚ) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp ha)
    exact_mod_cast ha'
  · intro h
    have hzero :
        (∑ a, ((Fintype.card α : ℚ) * (occupationCount f a : ℚ) - (n : ℚ)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      have ha : (Fintype.card α : ℚ) * (occupationCount f a : ℚ) = (n : ℚ) := by
        exact_mod_cast h a
      rw [ha, sub_self, zero_pow (by decide : 2 ≠ 0)]
    rw [hcenter, ← mul_assoc] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hq hn2)

end Erdos952.ModularVariance
